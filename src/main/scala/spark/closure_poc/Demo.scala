package spark.closure_poc

import java.io.PrintWriter
import java.lang.Long

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
   val c: ABC = null
    c == null
  }

  val closure8 = (e: ABC) => {
    if (e.a > 10.0) {
      10
    } else {
      8
    }
  }

  val closure9 = (e: ABC) => {
    val array = new Array[Boolean](1)
    array(0) = e.a > 10

    array(0) && e.a < 12
  }

  class D {
    val c: Int = 3
  }

  val closure10 = (e: D) => {
    e.c
  }

  val closure11 = (e: ABC) => {
    e.a.toByte
  }

  val closure12 = new MapFunction[ABC, Int] {
    private val result = 3
    override def call(value: ABC): Int = {
      result
    }
  }

  val closure13 = (s: Short) =>
    (((s + 1) * 2 - 1) / 2) == 3

  val closure14 = (s: Short) => s > 3

  val closure15 = (s: Short) => (Math.sqrt(s) + Math.log10(s)) > 3

  val closure16 = (s: Long) => (((s + 1L) * 2L - 1L) / 2L) == 3L

  val closure17 = (s: String) => s.length > 3

  val closure18 = (t: Tuple2[Int, Int]) => t._1 + t._2 > 4

  // Problemic due to CheckCast...
  val closure19 = (t: Tuple3[Int, Int, String]) => t._3.length > 2

  val closure20 = (t: Tuple4[Int, Int, Int, Double]) => Math.sqrt(t._4) > 3.0

  val closure21 = (t: Tuple3[Int, Int, String]) => t._3 != null

  // Problemic...
  val closure22 = (v: Long) => {
    val result = new Long(v)
    result
  }

  // Problemic
  val closure23 = (v: Long) => {
    val x: Int = v.toInt
    x
  }

  def go: Int = 3

  private final val gogo: Int = 4

  val closure24 = (v: Long) => {
    val result = go + gogo
    result
  }

  val closure25 = (v: Int) => gogo

  val closure26 = (v: ABC) => {
    val array = new Array[Any](4)
    array(0) = (((v.a + 5) - 2) * 6) / 2.0 % 3 // +, -, *, /, %
    array(1) = Math.sqrt(array.length)
    array(2) = v.a.toLong  // cast
    array(3) = {
      // >, <, ==, !=, >=, <=
      val flag = (((v.a > 0) & (v.a < 4) & (v != 2)) | ((v.a >= 5) & (v.a <= 7)))
      if (flag) 1 else 0
    }
    array
  }

  val closure27 = (v: ABC) => {
    val array = new Array[Double](1)

    val flag = (v.a > 0) && (v.a < 4) && (v.a != 2)
    flag
  }


  val closure28 = (v: ABC) => {
    val array = new Array[Double](1)
    (v.a <= 0)
  }


  val closure29 = (v: ABC) => {
    (v.a > 0) && (v.a < 4) && (v.a != 2)
  }

  def apply(a: Int): Int = gogo

  def main(args: Array[String]): Unit = {
    val parser = new ByteCodeParser
    val result = parser.parse[ABC](closure29.getClass)
    Console.println("\nResult of ByteCodeParser: ")
    Console.println("===============================================")
    Console.println(ByteCodeParser.treeString(result))
  }
}