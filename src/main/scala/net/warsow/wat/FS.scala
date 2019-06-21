package net.warsow.wat

import java.io.InputStream
import java.net.URI
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileSystems, FileVisitResult, SimpleFileVisitor, Files => JFiles, Path => JPath}
import java.nio.{ByteBuffer, ByteOrder}
import java.util.{Collections, Locale}

import scala.collection.mutable
import scala.util.Try
import scala.util.control.NonFatal

sealed abstract class VfsPath {
  def parts: IndexedSeq[String]
  def isTopLevel: Boolean = parts.size == 1
}

object VfsPath {
  def splitUnderlying(path: JPath): IndexedSeq[String] =
    for (i <- 0 until path.getNameCount) yield path.getName(i).toString.toLowerCase(Locale.ROOT)
}

case class RealPath(underlying: JPath) extends VfsPath {
  lazy val parts: IndexedSeq[String] = VfsPath.splitUnderlying(underlying)
}

case class PathInPak(pathOfPak: JPath, pathInPak: JPath) extends VfsPath {
  lazy val parts: IndexedSeq[String] = VfsPath.splitUnderlying(pathInPak)
}

sealed abstract class VfsFileKind

object VfsFileKind {
  val (expensiveMatchers, cheapMatchers): (Seq[FileKindMatcher[VfsFileKind]], Seq[FileKindMatcher[VfsFileKind]]) = {
    val matchers = mutable.ArrayBuffer[FileKindMatcher[VfsFileKind]]()
    // Variance hacks
    def matchersOf(seq: FileKindMatcher[_]*) = seq.asInstanceOf[Seq[FileKindMatcher[VfsFileKind]]]
    // This is the only way to get global objects registered
    // (as they're loaded lazily and won't get touched otherwise)
    matchers ++= matchersOf(Texture, Sound, Material, Model, Text, Cfg, Ui, ExecutableLike)
    matchers ++= matchersOf(AiFile, SoundEnvFile, L10n, Bsp, Skin, Hud, Font, Video, Script)
    matchers.partition(_.isExpensiveToCall)
  }

  def apply(path: JPath): (Traversable[String], Option[VfsFileKind]) = {
    val warnings = mutable.ArrayBuffer[String]()
    val kinds = mutable.ArrayBuffer[VfsFileKind]()
    for (matcher <- cheapMatchers) {
      matcher.apply(path) match {
        case Left(warning) => warnings += warning
        case Right(maybeKind) => kinds ++= maybeKind
      }
    }

    // Interrupt early if cheap matchers had any results
    // Note that the early interruption is a quite nasty thing for a purist
    // but we should do that as some matches may perform IO/blocking ops
    if (kinds.nonEmpty) {
      if (kinds.size > 1) {
        warnings += s"There were multiple kinds detected: ${kinds.mkString}"
        return (warnings, None)
      }
      return (warnings, kinds.headOption)
    }

    // We have to perform an explicit loop and interrupt early for reasons described above
    val iter = expensiveMatchers.iterator
    while (iter.hasNext) {
      iter.next().apply(path) match {
        case Left(warning) => warnings += warning
        case Right(Some(kind)) => return (warnings, Some(kind))
        case Right(None) =>
      }
    }
    (warnings, None)
  }
}

abstract class FileKindMatcher[K <: VfsFileKind] {
  def apply(path: JPath): Either[String, Option[K]]
  def isExpensiveToCall: Boolean = false
}

abstract class ExtensionMatcher[K <: VfsFileKind](cons: String => K, extensions: String*) extends FileKindMatcher[K] {
  private val matchAgainst = extensions.map(_.toLowerCase(Locale.ROOT).ensuring(_.startsWith(".")))

  def apply(path: JPath): Either[String, Option[K]] = {
    val pathLastPart = path.getName(path.getNameCount - 1).toString.toLowerCase(Locale.ROOT)
    Right(matchAgainst.find(extension => pathLastPart.endsWith(extension)).map(cons.apply))
  }
}

sealed abstract class Platform
case class WindowsPlatform() extends Platform
case class LinuxPlatform() extends Platform

sealed abstract class Architecture
case class ArchX86() extends Architecture
case class ArchX86_64() extends Architecture
case class ArchAny() extends Architecture

sealed abstract class ExecutableLike extends VfsFileKind {
  def platform: Platform
  def architecture: Architecture
}

case class Executable(platform: Platform, architecture: Architecture) extends ExecutableLike
case class Library(platform: Platform, architecture: Architecture) extends ExecutableLike
case class CommandScript(platform: Platform) extends ExecutableLike {
  override val architecture = ArchAny()
}

object ExecutableLike extends FileKindMatcher[ExecutableLike] {
  override def isExpensiveToCall: Boolean = true

  private def withStream[A](path: JPath)(ops: InputStream => Either[String, A]): Either[String, A] = {
    var stream: InputStream = null
    try {
      stream = JFiles.newInputStream(path)
      ops(stream)
    } catch {
      case NonFatal(_) => Left("An error occurred while reading bytes")
    } finally {
      if (stream ne null) Try(stream.close())
    }
  }

  private def readBytes(path: JPath, numBytes: Int): Either[String, Option[Array[Byte]]] = {
    withStream(path) { stream =>
      val bytes = new Array[Byte](numBytes)
      val readBytes = stream.read(bytes)
      Right(if (readBytes == numBytes) Some(bytes) else None)
    }
  }

  private def readAsByteBuffer(stream: InputStream, numBytes: Int, tag: String): Either[String, ByteBuffer] = {
    val bytes = new Array[Byte](numBytes)
    val readBytes = stream.read(bytes)
    if (readBytes == numBytes) {
      Right(ByteBuffer.wrap(bytes).order(ByteOrder.LITTLE_ENDIAN))
    } else {
      Left(s"Can't read $numBytes of $tag")
    }
  }

  private def matchTwoChars(buffer: ByteBuffer, c1: Char, c2: Char): Boolean =
    buffer.get(0) == c1 && buffer.get(1) == c2

  private def parsePEHeader(buffer: ByteBuffer) = {
    if (!matchTwoChars(buffer, 'P', 'E')) {
      Left("Failed to identify a PE header")
    } else {
      // Workarounds for JVM unsigned data woes
      f"${buffer.asShortBuffer().get(2)}%x" match {
        case "14c" => Right(ArchX86())
        case "8664" => Right(ArchX86_64())
        case _ => Left("Unrecognized architecture")
      }
    }
  }

  private def detectWindowsBinaryArch(path: JPath): Either[String, Architecture] = {
    withStream(path) { stream =>
      readAsByteBuffer(stream, numBytes = 64, "DOS header").flatMap { dosBuffer =>
        if (!matchTwoChars(dosBuffer, 'M', 'Z')) {
          Left("Is not a DOS/Windows MZ executable")
        } else {
          val peOffset = dosBuffer.asIntBuffer().get(15)
          if (peOffset < 64 || peOffset > 4096) {
            Left(s"Weird PE header offset $peOffset")
          } else {
            stream.skip(peOffset - 64)
            readAsByteBuffer(stream, numBytes = 6, "PE header") flatMap parsePEHeader
          }
        }
      }
    }
  }

  private def matchBytes(bytes: Array[Byte], shouldStartWith: Int*): Boolean = {
    if (bytes.length < shouldStartWith.length) false else {
      bytes.zip(shouldStartWith) forall { case (b, v) => b == v }
    }
  }

  private def matchElf(b: Array[Byte]) = matchBytes(b, shouldStartWith = 0x7f, 'E', 'L', 'F')
  private def matchShebang(b: Array[Byte]) = matchBytes(b, shouldStartWith = '#', '!')

  private def tryDetectingLinuxArch(path: JPath): Either[String, Option[Architecture]] = {
    readBytes(path, numBytes = 0x14).flatMap {
      case Some(b) if matchShebang(b) => Right(Some(ArchAny()))
      case Some(b) if !matchElf(b) => Right(None)
      case Some(b) => f"${ByteBuffer.wrap(b).get(0x12)}%x" match {
        case "3" => Right(Some(ArchX86()))
        case "3e" => Right(Some(ArchX86_64()))
        case _ => Left("Unrecognized architecture for an ELF format identified by magic numbers")
      }
      // Try reading only 2 bytes then
      case None => readBytes(path, numBytes = 2) map {
        case Some(b) if matchShebang(b) => Some(ArchAny())
        case _ => None
      }
    }
  }

  private def detectLinuxLibrary(path: JPath): Either[String, Option[ExecutableLike]] = {
    tryDetectingLinuxArch(path).flatMap {
      case Some(ArchAny()) => Left("Must have a specific architecture")
      case Some(arch) => Right(Some(Library(LinuxPlatform(), arch)))
      case _ => Right(None)
    }
  }

  private def tryDetectingLinuxScript(path: JPath): Either[String, Option[CommandScript]] = {
    tryDetectingLinuxArch(path) flatMap {
      case Some(ArchAny()) => Right(Some(CommandScript(LinuxPlatform())))
      case Some(_) => Left("Must not have a specific architecture")
      case _ => Right(None)
    }
  }

  private def tryDetectingLinuxExecutableOrScript(path: JPath): Either[String, Option[ExecutableLike]] = {
    for (maybeArch <- tryDetectingLinuxArch(path)) yield {
      for (arch <- maybeArch) yield
        if (arch == ArchAny()) CommandScript(LinuxPlatform()) else Executable(LinuxPlatform(), arch)
    }
  }

  override def apply(path: JPath): Either[String, Option[ExecutableLike]] = {
    path.getName(path.getNameCount - 1).toString.toLowerCase(Locale.ROOT) match {
      case p if p.endsWith(".dll") =>
        detectWindowsBinaryArch(path).map(a => Some(Library(WindowsPlatform(), a)))
      case p if p.endsWith(".exe") =>
        detectWindowsBinaryArch(path).map(a => Some(Executable(WindowsPlatform(), a)))
      case p if p.endsWith(".so") =>
        detectLinuxLibrary(path)
      case p if p.endsWith(".bat") || p.endsWith(".ps1") =>
        Right(Some(CommandScript(WindowsPlatform())))
      case p if p.endsWith(".sh") =>
        tryDetectingLinuxScript(path)
      case p if !p.contains(".") || p.endsWith(".x86_64") || p.endsWith(".i386") =>
        tryDetectingLinuxExecutableOrScript(path)
      case _ => Right(None)
    }
  }
}

case class Texture(extension: String) extends VfsFileKind
object Texture extends ExtensionMatcher(s => new Texture(s), ".tga", ".ktx", ".png", ".jpg", ".jpeg")

case class Sound(extension: String) extends VfsFileKind
object Sound extends ExtensionMatcher(s => new Sound(s), ".wav", ".ogg", ".m3u")

case class Material() extends VfsFileKind
object Material extends ExtensionMatcher(_ => new Material(), ".shader")

case class Model(extension: String) extends VfsFileKind
object Model extends ExtensionMatcher(s => new Model(s), ".md3", ".iqm")

case class Text() extends VfsFileKind
object Text extends ExtensionMatcher(_ => new Text(), ".txt")

case class Cfg() extends VfsFileKind
object Cfg extends ExtensionMatcher(_ => new Cfg(), ".cfg")

case class AiFile(extension: String) extends VfsFileKind
object AiFile extends ExtensionMatcher(s => new AiFile(s), ".aas", ".spots", ".navmesh", ".areavis", ".floorvis")

case class L10n() extends VfsFileKind
object L10n extends ExtensionMatcher(_ => new L10n(), ".po")

case class Bsp() extends VfsFileKind
object Bsp extends ExtensionMatcher(_ => new Bsp(), ".bsp")

// Should it be just a model?
case class Skin() extends VfsFileKind
object Skin extends ExtensionMatcher(_ => new Skin(), ".skin")

case class Hud() extends VfsFileKind
object Hud extends ExtensionMatcher(_ => new Hud(), ".hud")

case class Font(extension: String) extends VfsFileKind
object Font extends ExtensionMatcher(s => new Font(s), ".ttf", ".otf")

case class Video(extension: String) extends VfsFileKind
object Video extends ExtensionMatcher(s => new Video(s), ".ogv", ".roq")

case class SoundEnvFile(extension: String) extends VfsFileKind
object SoundEnvFile extends ExtensionMatcher(s => new SoundEnvFile(s), ".graph", ".table", ".leafprops")

case class Ui(extension: String) extends VfsFileKind
object Ui extends ExtensionMatcher(s => new Ui(s), ".rml", ".rcss")

case class Script(extension: String) extends VfsFileKind
object Script extends ExtensionMatcher(s => new Script(s), ".as", ".gt", ".gtd")

sealed abstract class VfsEntry {
  def path: VfsPath
}

case class VfsFile(path: VfsPath, kind: VfsFileKind) extends VfsEntry
case class VfsDir(path: VfsPath, children: Set[VfsEntry]) extends VfsEntry

sealed abstract class RealEntry {
  def path: JPath
}

case class RealFile(path: JPath) extends RealEntry

sealed abstract class RealContainer extends RealEntry
case class RealDir(path: JPath) extends RealContainer
case class RealPak(path: JPath) extends RealContainer

object FSWalker {
  private def isOtherFile(path: JPath, attrs: BasicFileAttributes): Boolean =
    attrs.isRegularFile && !hasPakExtension(path)

  private def isASubDir(path: JPath, attrs: BasicFileAttributes): Boolean =
    attrs.isDirectory

  private def isAPakFile(path: JPath, attrs: BasicFileAttributes): Boolean =
    attrs.isRegularFile && hasPakExtension(path)

  private abstract class PathVisitor(protected val dir: JPath) extends SimpleFileVisitor[JPath] {
    val warnings: mutable.Buffer[(JPath, String)] = mutable.ArrayBuffer[(JPath, String)]()

    final override def visitFile(file: JPath, attrs: BasicFileAttributes): FileVisitResult = {
      if (isASubDir(file, attrs)) {
        visitSubDir(file)
      } else if (isAPakFile(file, attrs)) {
        visitPakFile(file)
      } else if (isOtherFile(file, attrs)) {
        visitOtherFile(file)
      }
      FileVisitResult.CONTINUE
    }

    def visitSubDir(path: JPath): Unit
    def visitPakFile(path: JPath): Unit
    def visitOtherFile(path: JPath): Unit
  }

  private trait CollectingDirFiles { self: PathVisitor =>
    val entries = mutable.HashMap.empty[VfsEntry, RealEntry]

    override def visitOtherFile(path: JPath): Unit = {
      val (newWarnings, maybeKind) = VfsFileKind.apply(path)
      warnings ++= newWarnings.map(s => (path, s))
      maybeKind match {
        case Some(kind) => entries += Tuple2(VfsFile(RealPath(path), kind), RealFile(path))
        case None => warnings += Tuple2(path, s"Can't find a kind of `$path`")
      }
    }

    protected def exec(): ((VfsEntry, RealEntry), Traversable[(JPath, String)]) = {
      JFiles.walkFileTree(dir, Collections.emptySet(), 1, this)
      val vfsDir = VfsDir(RealPath(dir), this.entries.keys.toSet)
      ((vfsDir, RealDir(dir)), warnings)
    }
  }

  private class RootDirVisitor(root: JPath) extends PathVisitor(root) with CollectingDirFiles {
    override def visitSubDir(path: JPath): Unit = {
      val (entry, warnings) = walkSubDir(path)
      this.entries += entry
      this.warnings ++= warnings
    }

    override def visitPakFile(path: JPath): Unit = {
      val (entries, warnings) = walkPakFile(path)
      this.entries ++= entries
      this.warnings ++= warnings
    }
  }

  private class SubDirVisitor(dir: JPath) extends PathVisitor(dir) with CollectingDirFiles {
    override def visitSubDir(path: JPath): Unit = {
      val (entry, warnings) = walkSubDir(path)
      this.entries += entry
      this.warnings ++= warnings
    }

    override def visitPakFile(path: JPath): Unit =
      this.warnings += Tuple2(path, "A pak file is not located in a root directory")
  }

  private class PakFileVisitor(pathOfPak: JPath) extends SimpleFileVisitor[JPath] {
    private val subdirs = mutable.HashMap.empty[String, VfsDir]
    private val warnings = mutable.ArrayBuffer.empty[(JPath, String)]

    override def visitFile(file: JPath, attrs: BasicFileAttributes): FileVisitResult = {
      // Only regular files are actually read from a ZIP filesystem
      assert(attrs.isRegularFile)
      if (isAPakFile(file, attrs)) {
        warnings += Tuple2(file, "A pak file is inside other pak file")
      } else {
        visitOtherFile(file)
      }
      FileVisitResult.CONTINUE
    }

    private def visitOtherFile(file: JPath): Unit = {
      val (newWarnings, maybeKind) = VfsFileKind.apply(file)
      warnings ++= newWarnings.map(s => (file, s))
      maybeKind match {
        case Some(kind) => addPakFile(file, kind)
        case None => warnings += Tuple2(file, s"Can't find a kind of $file")
      }
    }

    private def addPakFile(pathInPak: JPath, classifiedKind: VfsFileKind): Unit = {
      val parentPath = pathInPak.getParent.toAbsolutePath
      val parentKey = parentPath.toString.toLowerCase(Locale.ROOT)
      val existingChildren = subdirs.get(parentKey).map(_.children).getOrElse(Set())
      val entry = VfsFile(PathInPak(pathOfPak, pathInPak), classifiedKind)
      val parent = VfsDir(PathInPak(pathOfPak, parentPath), existingChildren ++ Set(entry))
      subdirs.put(parentKey, parent)
    }

    def exec(): (Traversable[(VfsEntry, RealEntry)], Traversable[(JPath, String)]) = {
      val uri = new URI(s"jar:file:${pathOfPak.toAbsolutePath}")
      val fileSystem = FileSystems.newFileSystem(uri, Collections.emptyMap[String, String]())
      JFiles.walkFileTree(fileSystem.getPath("/"), this)
      val realEntryForThis = RealPak(pathOfPak)
      val topLevelDirs = for (e <- subdirs.values if e.path.isTopLevel) yield e
      val resultPairs = for (e <- topLevelDirs) yield (e, realEntryForThis)
      (resultPairs, warnings)
    }
  }

  object RootDirVisitor {
    def exec(root: JPath): ((VfsEntry, RealEntry), Traversable[(JPath, String)]) = new RootDirVisitor(root).exec()
  }

  object SubDirVisitor {
    def exec(dir: JPath): ((VfsEntry, RealEntry), Traversable[(JPath, String)]) = new SubDirVisitor(dir).exec()
  }

  object PakFileVisitor {
    def exec(pathOfPak: JPath): (Traversable[(VfsEntry, RealEntry)], Traversable[(JPath, String)]) =
      new PakFileVisitor(pathOfPak).exec()
  }

  def walkRootPath(root: JPath): ((VfsEntry, RealEntry), Traversable[(JPath, String)]) = RootDirVisitor.exec(root)

  def walkSubDir(dir: JPath): ((VfsEntry, RealEntry), Traversable[(JPath, String)]) = SubDirVisitor.exec(dir)

  def walkPakFile(path: JPath): (Traversable[(VfsEntry, RealEntry)], Traversable[(JPath, String)]) =
    PakFileVisitor.exec(path)

  def hasPakExtension(path: JPath): Boolean = {
    val lowerCase = path.toString.toLowerCase(Locale.ROOT)
    lowerCase.endsWith(".pk3") || lowerCase.endsWith(".pkwsw")
  }
}
