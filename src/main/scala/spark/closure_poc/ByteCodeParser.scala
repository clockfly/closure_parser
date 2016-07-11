package spark.closure_poc

import java.io.{PrintStream}
import scala.collection.immutable.Stack
import scala.collection.mutable
import scala.reflect.ClassTag
import scala.reflect.classTag

import org.objectweb.asm.{ClassReader, ClassVisitor, MethodVisitor, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Type._
import org.objectweb.asm.util.{Printer, Textifier, TraceMethodVisitor}

import org.objectweb.asm.tree.{AbstractInsnNode, FrameNode, IincInsnNode, InsnList, InsnNode, IntInsnNode, JumpInsnNode, LabelNode, LdcInsnNode, LineNumberNode, MethodInsnNode, MethodNode, TypeInsnNode, VarInsnNode}
// TODO: Support scala companion object constant reference...
// TODO: Support GETFIELD, GETSTATIC, ISHL, LSHL, ISHR, LSHR, IUSHR, LUSHR, TABLESWITCH,
// and LOOKUPSWITCH
object ByteCodeParser {
  val UnsupportedOpcodes = Set(
    // InvokeDynamicInsnNode
    INVOKEDYNAMIC,
    // FieldInsnNode
    PUTFIELD, PUTSTATIC, GETFIELD, GETSTATIC,
    // MultiANewArrayInsnNode
    MULTIANEWARRAY,
    // JumpInsnNode, JSR is not used by Java compile since JDK6.
    JSR,
    // VarInsnNode, RET is not used by Java compile since JDK6.
    RET,
    // TypeInsnNode
    NEW, INSTANCEOF,
    // InsnNode
    ISHL, LSHL, ISHR, LSHR, IUSHR, LUSHR,
    ATHROW,
    MONITORENTER, MONITOREXIT,
    // TableSwitchInsnNode
    TABLESWITCH,
    // LookupSwitchInsnNode
    LOOKUPSWITCH
  )

  class ByteCodeParserException(message: String) extends Exception(message)

  class UnsupportedOpcodeException(
      opcode: Int,
      message: String = "")
    extends ByteCodeParserException(s"Unsupported opcode ${Printer.OPCODES(opcode)}, $message")

  sealed trait Node {
    def children: List[Node]
    def dataType: Type
    def copy: Node = this
  }

  trait BinaryNode extends Node {
    def left: Node
    def right: Node
    override def children: List[Node] = List(left, right)
  }

  trait UnaryNode extends Node {
    def node: Node
    override def children: List[Node] = List(node)
  }

  trait NullaryNode extends Node {
    override def children: List[Node] = List.empty[Node]
  }

  case object VOID extends NullaryNode {
    override def dataType: Type = Type.VOID_TYPE
  }

  case class Constant[T: ClassTag](value: T) extends NullaryNode {
    def dataType: Type = Type.getType(classTag[T].runtimeClass)
    override def toString: String = s"$value"
  }

  case class Argument(dataType: Type) extends NullaryNode {
    override def toString: String = s"Argument"
  }

  case class This(dataType: Type) extends NullaryNode {
    override def toString: String = "This"
  }

  case class Field(node: Node, fieldName: String, dataType: Type) extends NullaryNode {
    override def toString: String = s"$node.$fieldName"
  }

  // if (condition == true) left else right
  case class If(condition: Node, left: Node, right: Node) extends BinaryNode {
    def dataType: Type = left.dataType
  }

  case class FunctionCall(
      obj: Node,
      className: String,
      method: String,
      arguments: List[Node], dataType: Type)
    extends Node {
    def children: List[Node] = arguments
    override def toString: String = {
      if (obj == null) {
        s"$className.$method(${arguments.mkString(", ")})"
      } else {
        s"$className.$method(${(obj::arguments).mkString(", ")})"
      }
    }
  }

  case class Cast(node: Node, dataType: Type) extends UnaryNode

  case class ArrayNode[T: ClassTag](
      length: Node,
      defaultValue: T,
      var data: Map[Int, Node] = Map.empty[Int, Node])
    extends Node {

    // We need to override copy as ArrayNode is mutable.
    override def copy(): Node = new ArrayNode[T](length, defaultValue, data)

    if (length.dataType != Type.INT_TYPE) {
      throw new ByteCodeParserException("ArrayNode must have a size of Int type")
    }

    def elementDataType: Type = Type.getType(classTag[T].runtimeClass)
    override def dataType: Type = Type.getType(s"[${elementDataType.getDescriptor}")

    override def children: List[Node] = data.toList.sortBy(_._1).map(_._2)

    def get(index: Int): Node = data.getOrElse(index, Constant(defaultValue))
    def put(index: Int, value: Node): Unit = { data += index -> value }
  }

  def treeString(node: Node): String = {
    val builder = new StringBuilder

    def simpleString: PartialFunction[Node, String] = {
      case product: Node with Product  =>
        val children = product.children.toSet[Any]
        val args = product.productIterator.toList.filterNot {
          case l: Iterable[_] => l.toSet.subsetOf(children)
          case e if children.contains(e) => true
          case dataType: Type => true
          case map: mutable.Map[Int, Node] if product.isInstanceOf[ArrayNode[_]] => true
          case _ => false
        }
        val argString = if (args.length > 0) args.mkString("(", ", ", ")") else ""
        s"${product.getClass.getSimpleName}[${product.dataType}]$argString"
    }

    def buildTreeString(node: Node, depth: Int): Unit = {
      (0 until depth).foreach(_ => builder.append("  "))
      builder.append(simpleString(node))
      builder.append("\n")
      node.children.foreach(buildTreeString(_, depth + 1))
    }
    buildTreeString(node, 0)
    builder.toString()
  }

  /**
   * @param operator +, -, *, /, <, >, ==, !=, <=, >=,
   */
  case class Arithmetic(operator: String, left: Node, right: Node) extends BinaryNode {
    def dataType: Type = left.dataType
    override def toString: String = {
      val leftString = if (left.children.length > 1) s"($left)" else s"$left"
      val rightString = if (right.children.length > 1) s"($right)" else s"$right"
      s"$leftString $operator $rightString"
    }
  }

  object DSL {
    def plus(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a + b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a + b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a + b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a + b)
        case _ => Arithmetic("+", left, right)
      }
    }

    def minus(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a - b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a - b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a - b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a - b)
        case _ => Arithmetic("-", left, right)
      }
    }

    def mul(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a * b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a * b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a * b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a * b)
        case _ => Arithmetic("*", left, right)
      }
    }

    def div(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a / b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a / b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a / b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a / b)
        case _ => Arithmetic("/", left, right)
      }
    }

    def rem(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a % b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a % b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a % b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a % b)
        case _ => Arithmetic("%", left, right)
      }
    }

    def and(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a & b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a & b)
        case _ => Arithmetic("&", left, right)
      }
    }

    def or(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a | b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a | b)
        case _ => Arithmetic("|", left, right)
      }
    }

    def xor(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a ^ b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a ^ b)
        case _ => Arithmetic("^", left, right)
      }
    }

    def compareEqual(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a), Constant(b)) => Constant(a == b)
        case _ => Arithmetic("==", left, right)
      }
    }

    def compareNotEqual(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a), Constant(b)) => Constant(!(a == b))
        case _ => Arithmetic("!=", left, right)
      }
    }

    def lt(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a < b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a < b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a < b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a < b)
        case _ => Arithmetic("<", left, right)
      }
    }

    def gt(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a > b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a > b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a > b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a > b)
        case _ => Arithmetic(">", left, right)
      }
    }

    def le(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a <= b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a <= b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a <= b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a <= b)
        case _ => Arithmetic("<=", left, right)
      }
    }

    def ge(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a >= b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a >= b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a >= b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a >= b)
        case _ => Arithmetic(">=", left, right)
      }
    }

    def cast[T: ClassTag](node: Node): Node = {
      DSL.cast(node, Type.getType(classTag[T].runtimeClass))
    }

    def cast(node: Node, dataType: Type): Node = {
      if (node.dataType == dataType) {
        node
      } else {
        Cast(node, dataType)
      }
    }
  }

  class MethodTracer(method: MethodNode, trace: Boolean = true, out: PrintStream = System.out) {
    private val printer = new Textifier
    private val visitor = new TraceMethodVisitor(printer)
    private val text = printer.getText.asInstanceOf[java.util.List[AnyRef]]

    if (trace) {
      out.println(s"\nByteCode of method ${method.name}:")
      out.println("===============================================")
      method.accept(visitor)
      flush()
      out.println(s"\nStart tracing method ${method.name}:")
      out.println("===============================================")
    }

    def trace(stack: Stack[Node], instruction: AbstractInsnNode): Unit = {
      if (this.trace) {
        instruction.accept(visitor)
        if (instruction.getOpcode >= 0) {
          val stackString = if (stack.length != 0) s"stack: ${stack.mkString(",")}\n" else ""
          val instructionString = text.get(text.size() - 1).toString
          text.set(text.size() - 1, s"$stackString$instructionString")
        }
      }
    }

    def flush(): Unit = {
      (0 until text.size()).foreach { line =>
        out.print(text.get(line).toString)
      }
      out.flush()
      text.clear()
    }
  }
}

class ByteCodeParser {
  import spark.closure_poc.ByteCodeParser._
  import spark.closure_poc.ByteCodeParser.DSL._

  def parse[T: ClassTag](closure: Class[_]): Node = {
    val defaultNamePattern = "call|apply(\\$mc.*\\$sp)?"
    parse[T](closure, defaultNamePattern)
  }

  /**
   * Parses the closure and generate a Node tree to represent the computation of the closure.
   *
   * @param closure input closure (single input argument, and single return value)
   * @param methodNamePattern regular expression pattern for the closure method
   * @tparam T the argument type of input closure
   * @return root Node of the Node tree.
   * @throws ByteCodeParserException
   */
  def parse[T: ClassTag](closure: Class[_], methodNamePattern: String): Node = {
    var applyMethods = List.empty[MethodNode]

    val reader = new ClassReader(closure.getName)

    reader.accept(new ClassVisitor(ASM5, null) {
      override def visitMethod(
          access: Int,
          name: String,
          desc: String,
          signature: String,
          exceptions: Array[String])
        : MethodVisitor = {
        if (isApplyMethod[T](name, desc)) {
          val method = new MethodNode(access, name, desc, signature, exceptions)
          applyMethods = method :: applyMethods
          method
        } else {
          null
        }
      }

      // Check whether it is a valid apply method, with requirements:
      // 1. Name matches "apply" or "apply$mc.*$sp".
      // 2. Single argument function.
      // 3. Argument's type matches the expected type.
      private def isApplyMethod[T: ClassTag](name: String, signature: String): Boolean = {
        val expectedArgumentClass = classTag[T].runtimeClass
        val argumentTypes = Type.getArgumentTypes(signature)
        val returnType = Type.getReturnType(signature)

        argumentTypes.length == 1 &&
        argumentTypes(0).getClassName == expectedArgumentClass.getName &&
        name.matches(methodNamePattern)
      }
    }, 0)

    if (applyMethods.length == 0) {
      throw new ByteCodeParserException(s"Cannot find an apply method in closure " +
        s"${closure.getName}. The expected argument type is: ${classTag[T].runtimeClass}")
    }
    // Pick the first one if there are multiple apply methods found
    analyze[T](closure, applyMethods.head)
  }

  private def analyze[T: ClassTag](closure: Class[_], applyMethod: MethodNode): Node = {
    if(applyMethod.tryCatchBlocks.size() != 0) {
      throw new ByteCodeParserException("try...catch... is not supported in ByteCodeParser")
    }

    var localVars = Map.empty[Int, Node]
    localVars += 0 -> This(Type.getType(closure))
    localVars += 1 -> Argument(Type.getArgumentTypes(applyMethod.desc)(0))

    val tracer = new MethodTracer(applyMethod, trace = true)

    // invoke instructions starting from startIndex
    def invoke(
        instructions: InsnList,
        startIndex: Int,
        inputStack: Stack[Node],
        inputLocalVars: Map[Int, Node]): Node = {
      var result: Option[Node] = None
      var index = startIndex
      var stack = inputStack

      def pop(): Node = {
        val top = stack.top
        stack = stack.pop
        top
      }

      def push(node: Node): Unit = {
        stack = stack.push(node)
      }

      var localVars = inputLocalVars
      def copyLocalVars(): Map[Int, Node] = localVars.map(kv => (kv._1, kv._2.copy))

      while (index < instructions.size() && result.isEmpty) {
        val node = instructions.get(index)
        val opcode = node.getOpcode
        if (ByteCodeParser.UnsupportedOpcodes.contains(opcode)) {
          throw new UnsupportedOpcodeException(opcode)
        }
        tracer.trace(stack, node)
        node match {
          case method: MethodInsnNode =>
            method.getOpcode match {
              case INVOKEVIRTUAL | INVOKESTATIC | INVOKESPECIAL | H_INVOKEINTERFACE =>
                val className = Type.getObjectType(method.owner).getClassName
                val methodName = method.name
                val argumentTypes = Type.getArgumentTypes(method.desc)
                val returnType = Type.getReturnType(method.desc)
                val arguments = (0 until argumentTypes.length).toList.map {_ =>
                  pop()
                }.reverse
                val obj = if (method.getOpcode == INVOKESTATIC) {
                  null
                } else {
                  pop()
                }
                if (obj.isInstanceOf[Argument] && arguments.length == 0) {
                  push(Field(obj, methodName, returnType))
                } else {
                  push(FunctionCall(obj, className, methodName, arguments, returnType))
                }
            }
          case intInstruction: IntInsnNode =>
            intInstruction.getOpcode match {
              case BIPUSH | SIPUSH => push(Constant(intInstruction.operand))
              case NEWARRAY =>
                val count = pop()
                val array = intInstruction.operand match {
                  case T_BOOLEAN | T_BYTE | T_CHAR | T_SHORT | T_INT => ArrayNode[Int](count, 0)
                  case T_FLOAT => ArrayNode[Float](count, 0F)
                  case T_DOUBLE => ArrayNode[Double](count, 0D)
                  case T_LONG => ArrayNode[Long](count, 0L)
                }
                push(array)
            }

          case typeInstruction: TypeInsnNode =>
            val array = typeInstruction.getOpcode match {
              case ANEWARRAY =>
                val array = ArrayNode[AnyRef](pop(), null)
                push(array)
              case CHECKCAST => // skip
                val node = pop()
                push(cast(node, Type.getType(typeInstruction.desc)))
            }
          case inc: IincInsnNode =>
            val index = inc.`var`
            val increase = inc.incr
            val localVar = localVars(index)
            localVars += index -> plus(localVar, Constant(increase))
          case jump: JumpInsnNode =>
            // comparator: <, >, ==, <=, >=
            def compareAndJump(comparator: (Node, Node) => Node): Node = {
              val right = pop()
              val left = pop()

              if (jump.label == instructions.get(index + 1)) {
                // Jump to immediate next instruction
                invoke(instructions, instructions.indexOf(jump.label), stack, localVars)
              } else {
                val condition = left match {
                  case a@Arithmetic("-", _, _) if right == Constant(0) => comparator(a.left, a.right)
                  case _ => comparator(left, right)
                }

                val trueStatement = invoke(instructions, instructions.indexOf(jump.label), stack, copyLocalVars())
                val falseStatement = invoke(instructions, index + 1, stack, copyLocalVars())
                if (condition == Constant(true)) {
                  trueStatement
                } else if (condition == Constant(false)) {
                  falseStatement
                } else {
                  if (trueStatement == falseStatement) {
                    trueStatement
                  } else {
                    If(condition, trueStatement, falseStatement)
                  }
                }
              }
            }

            if (instructions.indexOf(jump.label) <= index) {
              throw new UnsupportedOpcodeException(jump.getOpcode, "Backward jump is not " +
                "supported because it may create a loop")
            }

            jump.getOpcode match {
              case IF_ICMPEQ | IF_ACMPEQ =>
                result = Some(compareAndJump(compareEqual))
              case IF_ICMPNE | IF_ACMPNE =>
                result = Some(compareAndJump(compareNotEqual))
              case IF_ICMPLT =>
                result = Some(compareAndJump(lt))
              case IF_ICMPGT =>
                result = Some(compareAndJump(gt))
              case IF_ICMPLE =>
                result = Some(compareAndJump(le))
              case IF_ICMPGE =>
                result = Some(compareAndJump(ge))
              case IFNULL =>
                push(Constant(null))
                result = Some(compareAndJump(compareEqual))
              case IFNONNULL =>
                push(Constant(null))
                result = Some(compareAndJump(compareNotEqual))
              case IFEQ =>
                push(Constant(0))
                result = Some(compareAndJump(compareEqual))
              case IFNE =>
                push(Constant(0))
                result = Some(compareAndJump(compareNotEqual))
              case IFLT =>
                push(Constant(0))
                result = Some(compareAndJump(lt))
              case IFGT =>
                push(Constant(0))
                result = Some(compareAndJump(gt))
              case IFLE =>
                push(Constant(0))
                result = Some(compareAndJump(le))
              case IFGE =>
                push(Constant(0))
                result = Some(compareAndJump(ge))
              case GOTO =>
                index = instructions.indexOf(jump.label) - 1
            }
          case load: LdcInsnNode => {
            val constant = load.cst
            constant match {
              case i: java.lang.Integer => push(Constant[Int](i))
              case f: java.lang.Float => push(Constant[Float](f))
              case d: java.lang.Double => push(Constant[Double](d))
              case l: java.lang.Long => push(Constant[Long](l))
              case str: java.lang.String => push(Constant[String](str))
              case other =>
                throw new UnsupportedOpcodeException(load.getOpcode, s"LDC only supports type " +
                  s"Int, Float, Double, Long and String, current type is ${other.getClass.getName}")
            }
          }
          case localVar: VarInsnNode =>
            val index = localVar.`var`
            localVar.getOpcode match {
              case ILOAD | LLOAD | FLOAD | DLOAD | ALOAD =>
                push(localVars(index))
              case ISTORE | LSTORE | FSTORE | DSTORE | ASTORE =>
                val top = pop()
                localVars += index -> top
            }
          case op: InsnNode =>
            op.getOpcode match {
              case NOP => // Skip
              case ACONST_NULL => push(Constant(null))
              case ICONST_M1 => push(Constant(-1))
              case ICONST_0 => push(Constant(0))
              case ICONST_1 => push(Constant(1))
              case ICONST_2 => push(Constant(2))
              case ICONST_3 => push(Constant(3))
              case ICONST_4 => push(Constant(4))
              case ICONST_5 => push(Constant(5))
              case LCONST_0 => push(Constant(0L))
              case LCONST_1 => push(Constant(1L))
              case FCONST_0 => push(Constant(0D))
              case FCONST_1 => push(Constant(1D))
              case FCONST_2 => push(Constant(2D))
              case DCONST_0 => push(Constant(0D))
              case DCONST_1 => push(Constant(1D))
              case IADD | LADD | FADD | DADD =>
                val right = pop()
                val left = pop()
                push(plus(left, right))
              case ISUB | LSUB | FSUB | DSUB =>
                val right = pop()
                val left = pop()
                push(minus(left, right))
              case IMUL | LMUL | FMUL | DMUL =>
                val right = pop()
                val left = pop()
                push(mul(left, right))
              case IDIV | LDIV | FDIV | DDIV =>
                val right = pop()
                val left = pop()
                push(div(left, right))
              case IREM | LREM | FREM | DREM =>
                val right = pop()
                val left = pop()
                push(rem(left, right))
              case INEG =>
                val top = pop()
                push(minus(Constant(0), top))
              case LNEG =>
                val top = pop()
                push(minus(Constant(0L), top))
              case FNEG =>
                val top = pop()
                push(minus(Constant(0F), top))
              case DNEG =>
                val top = pop()
                push(minus(Constant(0D), top))
              case IAND | LAND =>
                val right = pop()
                val left = pop()
                push(and(left, right))
              case IOR | LOR =>
                val right = pop()
                val left = pop()
                push(or(left, right))
              case IXOR | LXOR =>
                val right = pop()
                val left = pop()
                push(xor(left, right))
              case I2L | F2L | D2L =>
                push(cast[Long](pop))
              case L2I | F2I | D2I =>
                push(cast[Int](pop))
              case I2F | L2F | D2F =>
                push(cast[Float](pop))
              case I2D | L2D | F2D =>
                push(cast[Double](pop))
              case I2B => push(cast[Byte](pop))
              case I2C => push(cast[String](pop))
              case I2S => push(cast[Short](pop))
              case LCMP | FCMPL | FCMPG | DCMPL | DCMPG =>

                val jump = instructions.get(index + 1).getOpcode match {
                  case IFEQ | IFNE | IFLT | IFGT | IFLE | IFGE =>
                    instructions.get(index + 1).asInstanceOf[JumpInsnNode]
                  case _ =>
                    throw new UnsupportedOpcodeException(
                      opcode,
                      s"${Printer.OPCODES(op.getOpcode)} need be followed by a jump " +
                        s"instruction like IFEQ, IFNE, IFLT, IFGT, IFLE, IFGE")
                }

                // Rewrite the op...
                jump.getOpcode match {
                  case IFEQ => jump.setOpcode(IF_ICMPEQ)
                  case IFNE => jump.setOpcode(IF_ICMPNE)
                  case IFLT => jump.setOpcode(IF_ICMPLT)
                  case IFGT => jump.setOpcode(IF_ICMPGT)
                  case IFLE => jump.setOpcode(IF_ICMPLE)
                  case IFGE => jump.setOpcode(IF_ICMPGE)
                }

              case POP | POP2 | DUP | DUP2 | DUP_X1 | DUP_X2 | DUP2_X1 | DUP2_X2 | SWAP =>
                // Each data type has a category, which affects the behavior of stack operations.
                // JVM Category 2 types: Long, Double.
                // JVM Category 1 types: Boolean, Byte, Char,Short, Int, Float, Reference,
                // ReturnAddress.
                // @See https://docs.oracle.com/javase/specs/jvms/se7/html/jvms-2.html#jvms-2.11.1
                val stackCategories = stack.toList.map(_.dataType).map { dataType =>
                  dataType match {
                    case LONG_TYPE | DOUBLE_TYPE => 2
                    case _ => 1
                  }
                }.slice(0, 4) // Stack operations at max use 4 stack slots.

                (op.getOpcode, stackCategories) match {
                  case (POP, 1::_) => pop()
                  case (POP2, 1::1::_) =>
                    pop()
                    pop()
                  case (POP2, 2::_) => pop()
                  case (DUP, 1::_) =>
                    val top = pop()
                    push(top)
                    push(top)
                  case (DUP2, 1::1::_) =>
                    val first = pop()
                    val second = pop()
                    push(second)
                    push(first)
                    push(second)
                    push(first)
                  case (DUP2, 2::_) =>
                    val top = pop()
                    push(top)
                    push(top)
                  case (DUP_X1, 1::1::_) =>
                    val first = pop()
                    val second = pop()
                    push(first)
                    push(second)
                    push(first)
                  case (DUP_X2, 1::1::1::_) =>
                    val first = pop()
                    val second = pop()
                    val third = pop()
                    push(first)
                    push(third)
                    push(second)
                    push(first)
                  case (DUP_X2, 1::2::_) =>
                    val first = pop()
                    val second = pop()
                    push(first)
                    push(second)
                    push(first)
                  case (DUP2_X1, 1::1::1::_) =>
                    val first = pop()
                    val second = pop()
                    val third = pop()
                    push(second)
                    push(first)
                    push(third)
                    push(second)
                    push(first)
                  case (DUP2_X1, 2::1::_) =>
                    val first = pop()
                    val second = pop()
                    push(first)
                    push(second)
                    push(first)
                  case (DUP2_X2, 1::1::1::1::_) =>
                    val first = pop()
                    val second = pop()
                    val third = pop()
                    val fourth = pop()
                    push(second)
                    push(first)
                    push(fourth)
                    push(third)
                    push(second)
                    push(first)
                  case (DUP2_X2, 2::1::1::_) =>
                    val first = pop()
                    val second = pop()
                    val third = pop()
                    push(first)
                    push(third)
                    push(second)
                    push(first)
                  case (op, _) =>
                    throw new UnsupportedOpcodeException(op, s"Stack's data type categories " +
                      s"(${stackCategories}) don't match the opcode's requirements: ")
                }
              case ARRAYLENGTH =>
                val array = pop()
                array match  {
                  case ArrayNode(length, _, _) => push(length)
                  case x => throw new ByteCodeParserException("Expects an array from stack, but " +
                    s"get ${x.getClass.getSimpleName}")
                }
              case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD =>
                val index = pop()
                val array = pop()
                (index, array) match {
                  case (Constant(index: Int), node@ ArrayNode(_, _, _)) =>
                    push(node.get(index))
                  case _ =>
                    throw new UnsupportedOpcodeException(op.getOpcode, "Failed to save data to " +
                      "an array because the array index is not a constant value")
                }
              case IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE =>
                val data = pop()
                val index = pop()
                val array = pop()
                (index, array) match {
                  case (Constant(index: Int), arrayNode@ ArrayNode(_, _, _)) =>
                    arrayNode.put(index, data)
                  case _ =>
                    throw new UnsupportedOpcodeException(op.getOpcode, "Failed to read data from " +
                      "an array because the array index is not a constant value")
                }
              case DRETURN | FRETURN | IRETURN | LRETURN | ARETURN =>
                result = Some(pop())
              case RETURN =>
                result = Some(VOID)
            }
          case label: LabelNode => // Skip pseudo code
          case lineNumber: LineNumberNode => // Skip pseudo code
          case frame: FrameNode => // Skip pseudo code
        }

        index += 1
      }

      tracer.flush()
      if (result.isEmpty) {
        throw new ByteCodeParserException("Failed to parse the closure for unknown reason")
      }
      result.get
    }
    val result = invoke(applyMethod.instructions, 0, Stack.empty[Node], localVars)
    // As JVM treats Boolean, Byte, Short as Integer in runtime, we need to do a cast to change
    // the return type back to expected type.
    cast(result, Type.getReturnType(applyMethod.desc))
  }
}
