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


  val closure3 = (b: Long) => {
    b + 1
  }


  case class ABC(a: Int, b: Int)

  val closure4 = (e: ABC) => {
    val b = e.b
    val sqrt = Math.sqrt(e.a)
    sqrt + b
  }

  def main(args: Array[String]): Unit = {
    val reader = new ClassReader(closure4.getClass.getName)
    val writer = new PrintWriter(System.out)
    reader.accept(new ByteCodeParser[ABC](writer), 0)

//    reader.accept(new TraceClassVisitor(writer), 0)
  }
}