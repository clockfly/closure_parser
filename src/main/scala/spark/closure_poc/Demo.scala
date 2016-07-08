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


  case class ABC(a: Int, b: Long)

  val closure4 = (e: ABC) => {
    val b = e.b
    val sqrt = Math.sqrt(e.a)
    sqrt + b
  }

  val closure5 = (e: ABC) => {
    var i = 0
    while(i < 1) {
      val b = e.b
      i += 1
    }
    val b = e.b
    val sqrt = Math.sqrt(e.a)
    sqrt + b
  }

  val closure6 = (e: ABC) => {
    (e.a + 3).asInstanceOf[Int]
    e.a == 3
  }

  val closure7 = (e: ABC) => {
   if (e.b > 3L) {
     3
   } else {
     6
   }
  }

  def main(args: Array[String]): Unit = {
    val parser = new ByteCodeParser
    parser.parse[ABC](closure7.getClass)
  }
}