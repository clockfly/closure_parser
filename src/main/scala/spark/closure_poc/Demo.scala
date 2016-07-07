package spark.closure_poc

import java.io.PrintWriter

import org.objectweb.asm.ClassReader
import org.objectweb.asm.util.TraceClassVisitor

object Demo {
  case class B(a: String, b: String)

  var xx: String = "xxxxx"

  type T = Long

  val closure = (b: T) => {
    if (b > 0 && b < 5) {
      3
    }  else {
      1
    }
  }

  val closure2 = (b: T) => {
    var array = new Array[Boolean](3)  // temoporary data
    val index = 1 + 2
    array(index) = true
    if (array(1) == true) {
      array(1)
    } else {
      1
    }
  }

  def main(args: Array[String]): Unit = {
    val reader = new ClassReader(closure2.getClass.getName)
    val writer = new PrintWriter(System.out)
    reader.accept(new ByteCodeParser[T](writer), 0)

//    reader.accept(new TraceClassVisitor(writer), 0)
  }
}