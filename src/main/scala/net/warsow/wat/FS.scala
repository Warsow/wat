package net.warsow.wat

import java.net.URI
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileSystems, FileVisitResult, SimpleFileVisitor, Files => JFiles, Path => JPath}
import java.util.{Collections, Locale}

import scala.collection.mutable

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
case class Texture(extension: String) extends VfsFileKind
case class Sound(extension: String) extends VfsFileKind
case class Shader(extension: String) extends VfsFileKind
case class Executable() extends VfsFileKind
case class Library(extension: String) extends VfsFileKind
case class Other(extension: Option[String]) extends VfsFileKind

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
  private abstract class PathVisitor(protected val dir: JPath) extends SimpleFileVisitor[JPath] {
    val warnings: mutable.Buffer[(JPath, String)] = mutable.ArrayBuffer[(JPath, String)]()

    def isOtherFile(path: JPath, attrs: BasicFileAttributes): Boolean =
      attrs.isRegularFile && !hasPakExtension(path)

    def isASubDir(path: JPath, attrs: BasicFileAttributes): Boolean =
      attrs.isDirectory

    def isAPakFile(path: JPath, attrs: BasicFileAttributes): Boolean =
      attrs.isRegularFile && hasPakExtension(path)

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

    def tryVisitingFile(path: JPath): Option[(VfsFile, RealFile)] = {
      for (recognizedKind <- getFileKind(path)) yield {
        val underlying = RealFile(path)
        (VfsFile(RealPath(path), recognizedKind), underlying)
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

    override def visitOtherFile(path: JPath): Unit =
      this.entries ++= tryVisitingFile(path)
  }

  private class SubDirVisitor(dir: JPath) extends PathVisitor(dir) with CollectingDirFiles {
    override def visitSubDir(path: JPath): Unit = {
      val (entry, warnings) = walkSubDir(path)
      this.entries += entry
      this.warnings ++= warnings
    }

    override def visitPakFile(path: JPath): Unit =
      this.warnings += Tuple2(path, "A pak file is not located in a root directory")

    override def visitOtherFile(path: JPath): Unit =
      this.entries ++= tryVisitingFile(path)
  }

  private class PakFileVisitor(pathOfPak: JPath) extends SimpleFileVisitor[JPath] {
    val subdirs = mutable.HashMap.empty[String, VfsDir]

    override def visitFile(file: JPath, attrs: BasicFileAttributes): FileVisitResult = {
      // Only regular files are actually read from a ZIP filesystem
      assert(attrs.isRegularFile)
      for (recognizedKind <- getFileKind(file)) {
        addPakFile(file, recognizedKind)
      }
      FileVisitResult.CONTINUE
    }

    private def addPakFile(pathInPak: JPath, recognizedKind: VfsFileKind): Unit = {
      val parentPath = pathInPak.getParent.toAbsolutePath
      val parentKey = parentPath.toString.toLowerCase(Locale.ROOT)
      val existingChildren = subdirs.get(parentKey).map(_.children).getOrElse(Set())
      val entry = VfsFile(PathInPak(pathOfPak, pathInPak), recognizedKind)
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
      (resultPairs, Traversable())
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

  def getFileKind(path: JPath): Option[VfsFileKind] = None
}
