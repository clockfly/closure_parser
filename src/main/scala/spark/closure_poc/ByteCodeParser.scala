package spark.closure_poc
import java.io.{DataOutputStream, OutputStream, PrintStream, PrintWriter}

import scala.reflect.ClassTag

import org.objectweb.asm.{ClassReader, ClassVisitor, MethodVisitor, Opcodes, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Type._
import org.objectweb.asm.util.{Printer, Textifier, TraceMethodVisitor}
import scala.reflect._

import org.objectweb.asm.tree.{AbstractInsnNode, FieldInsnNode, FrameNode, IincInsnNode, InsnList, InsnNode, IntInsnNode, JumpInsnNode, LabelNode, LdcInsnNode, LineNumberNode, LocalVariableNode, MethodInsnNode, MethodNode, TypeInsnNode, VarInsnNode}
import scala.collection.JavaConverters._
import scala.collection.immutable.Stack
import scala.collection.mutable
import scala.runtime.BoxesRunTime

// TODO: Proof there is NO risk in using stack... (Double, and Long use 2 stack slots instad of 1)
// https://docs.oracle.com/javase/specs/jvms/se7/html/jvms-2.html#jvms-2.11.1
// TODO: Besides Scala, prove this also works for Java
// TODO: Optimize the Arimetic operations to make it simper...
// TODO: Do a cast for the final type...
object ByteCodeParser {

  val UnsupportedOpcodes = Set(
    // InvokeDynamicInsnNode
    INVOKEDYNAMIC,
    // FieldInsnNode
    PUTFIELD, PUTSTATIC,
    // MultiANewArrayInsnNode
    MULTIANEWARRAY,
    // JumpInsnNode, JSR is not used by Java compile since JDK6.
    JSR,
    // VarInsnNode, RET is not used by Java compile since JDK6.
    RET,
    // TypeInsnNode
    NEW, CHECKCAST, INSTANCEOF,
    // InsnNode
    ISHL, LSHL, ISHR, LSHR,IUSHR, LUSHR,
    ATHROW,
    MONITORENTER, MONITOREXIT,
    // TableSwitchInsnNode
    TABLESWITCH,
    // LookupSwitchInsnNode
    LOOKUPSWITCH
  )

  class ByteCodeParserExecption(message: String) extends Exception(message)

  class UnsupportedOpcodeException(
      opcode: Int,
      message: String = "")
    extends ByteCodeParserExecption(s"Unsupported opcode ${Printer.OPCODES(opcode)}, $message")

  sealed trait Node {
    def nodeName: String = getClass.getSimpleName
    def children: List[Node]
    def dataType: Type
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
  }

  case class Argument(dataType: Type) extends NullaryNode

  case class This(dataType: Type) extends NullaryNode

  case class Field(fieldName: String, node: Node, dataType: Type) extends NullaryNode

  // if (condition == true) left else right
  case class If(condition: Node, left: Node, right: Node) extends BinaryNode {
    def dataType: Type = left.dataType
  }

  case class FunctionCall(className: String, method: String, obj: Node, arguments: List[Node], dataType: Type) extends Node {
    def children: List[Node] = arguments
  }

  case class Cast[T: ClassTag](node: Node) extends UnaryNode {
    override def nodeName: String = {
      s"Cast[${classTag[T].toString()}]"
    }
    override def dataType: Type = Type.getType(classTag[T].runtimeClass)
  }

  def treeString(node: Node): String = {
    val builder = new StringBuilder

    def simpleString: PartialFunction[Node, String] = {
      case product: Node with Product  =>
        val children = product.children.toSet[Any]
        val args = product.productIterator.filterNot {
          case l: Iterable[_] => l.toSet.subsetOf(children)
          case e => children.contains(e)
        }
        s"${product.nodeName} ${args.mkString(", ")}"
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

  case class ArrayNode[T: ClassTag](
    length: Node,
    defaultValue: T,
    data: mutable.Map[Int, Node] = mutable.Map.empty[Int, Node]) extends Node {

    if (length.dataType != Type.INT_TYPE) {
      throw new ByteCodeParserExecption("ArrayNode must have a size of Int type")
    }

    def elementDataType: Type = Type.getType(classTag[T].runtimeClass)
    override def dataType: Type = Type.getType(s"[${elementDataType.getDescriptor}")

    override def children: List[Node] = data.values.toList
    def get(index: Int): Node = data.getOrElse(index, Constant(defaultValue))
    def put(index: Int, value: Node): Unit = {
      if (value.dataType != elementDataType) {
        throw new ByteCodeParserExecption("element type's type mismatch ArrayNode's type argument")
      }
      data(index) = value
    }

    override def nodeName: String = {
      s"Array[${classTag[T].runtimeClass.getName}]"
    }
  }

  /**
   * @param operator +, -, *, /, <, >, ==, <=, >=,
   */
  case class Arithmetic(operator: String, left: Node, right: Node) extends BinaryNode {
    def dataType: Type = left.dataType
  }

  object DSL {
    // DO optimization before creating a node...

    def plus(left: Node, right: Node): Node = {
      // 1. check the type of left and right to make sure they match
      // 2. if there are Constant
      // 3. pick the left value and right value
      // do the math   ()
      // return value..

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
        case (Constant(a: Int), Constant(b: Int)) => Constant(a == b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a == b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a == b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a == b)
        case _ => Arithmetic("==", left, right)
      }
    }

    def compareNotEqual(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a != b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a != b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a != b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a != b)
        case _ => Arithmetic("!=", left, right)
      }
    }

    def lessThan(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a < b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a < b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a < b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a < b)
        case _ => Arithmetic("<", left, right)
      }
    }

    def greaterThan(left: Node, right: Node): Node = {
      (left, right) match {

        case (Constant(a: Int), Constant(b: Int)) => Constant(a > b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a > b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a > b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a > b)
        case _ => Arithmetic(">", left, right)
      }
    }

    def lessEqualThan(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a <= b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a <= b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a <= b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a <= b)
        case _ => Arithmetic("<=", left, right)
      }
    }

    def greaterEqualThan(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Int), Constant(b: Int)) => Constant(a >= b)
        case (Constant(a: Float), Constant(b: Float)) => Constant(a >= b)
        case (Constant(a: Long), Constant(b: Long)) => Constant(a >= b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a >= b)
        case _ => Arithmetic(">=", left, right)
      }
    }

    def cast[T: ClassTag](node: Node): Node = {
      Cast[T](node)
    }
  }

  class MethodTracer(method: MethodNode, trace: Boolean = true, out: PrintStream = System.out) {

    private val printer = new Textifier
    private val visitor = new TraceMethodVisitor(printer)
    private val text = printer.getText.asInstanceOf[java.util.List[AnyRef]]

    if (trace) {
      method.accept(visitor)
      flush()
      out.println(s"Start tracing method ${method.name}:")
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

  private def trace: Boolean = true

  def parse[T: ClassTag](closure: Class[_]): Unit = {
    var applyMethods = List.empty[MethodNode]

    val reader = new ClassReader(closure.getName)

    reader.accept(new ClassVisitor(ASM5, null) {
      override def visitMethod(access: Int, name: String, desc: String, signature: String, exceptions: Array[String]): MethodVisitor = {
        if (isApplyMethod[T](name, desc)) {
          val method = new MethodNode(access, name, desc, signature, exceptions)
          applyMethods = method :: applyMethods
          method
        } else {
          null
        }
      }

      // Check 1. name matches apply 2. single argument 3. argument type matches
      private def isApplyMethod[T: ClassTag](name: String, signature: String): Boolean = {
        val expectedArgumentClass = classTag[T].runtimeClass
        val argumentTypes = Type.getArgumentTypes(signature)
        val returnType = Type.getReturnType(signature)
        val namePattern = "apply(\\$mc.*\\$sp)?"
        if (argumentTypes.length == 1 &&
          argumentTypes(0).getClassName == expectedArgumentClass.getName &&
          name.matches(namePattern)) {
          Console.println("NAME MATCH " + name + ", " + namePattern)
          true
        } else {
          false
        }
      }
    }, 0)

    if (applyMethods.length == 0) {
      throw new ByteCodeParserExecption("We cannot find a apply emthod")
    }

    // Pick the first one if there are multiple apply method found
    val applyMethod = applyMethods.head

    analyze[T](closure, applyMethod)
  }

  private def analyze[T: ClassTag](closure: Class[_], applyMethod: MethodNode): Node = {
    if(applyMethod.tryCatchBlocks.size() != 0) {
      throw new ByteCodeParserExecption("try...catch... is not allowed in ByteCodeParser")
    }

    var localVars: Map[Int, Node] = Map.empty[Int, Node]
    localVars += 0 -> This(Type.getType(closure))
    localVars += 1 -> Argument(Type.getArgumentTypes(applyMethod.desc)(0))

    val tracer = new MethodTracer(applyMethod, trace = true)
    val instructions = applyMethod.instructions

    def invoke(
        instructions: InsnList,
        startIndex: Int,
        inputStack: Stack[Node] = new Stack[Node]()): ByteCodeParser.Node = {
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
                  push(Field(methodName, obj, returnType))
                } else {
                  push(FunctionCall(className, methodName, obj, arguments, returnType))
                }
            }
          // TODO: figure out this!!!
          case field: FieldInsnNode =>
            field.getOpcode match {
              case GETFIELD =>
                Console.println("Opcodes.GETFIELD")
              case GETSTATIC =>
                Console.println("GETSTATIC")
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
              case ANEWARRAY => ArrayNode[AnyRef](pop(), null)
            }
            push(array)
          case iinc: IincInsnNode =>
            val localVar = localVars(iinc.`var`)
            localVars += iinc.`var` -> DSL.plus(localVar, Constant(iinc.incr))
          case jump: JumpInsnNode =>
            // compareOperator: <, >, ==, <=, >=
            def compareAndJump(comparator: (Node, Node) => Node): Node = {
              val right = pop()
              val left = pop()

              val condition = left match {
                case a@Arithmetic("-", _, _) if right == Constant(0) => comparator(a.left, a.right)
                case _ => comparator(left, right)
              }

              val trueStatement = invoke(instructions, instructions.indexOf(jump.label), stack)
              val falseStatement = invoke(instructions, index + 1, stack)
              if (condition == Constant(true)) {
                trueStatement
              } else if (condition == Constant(false)) {
                falseStatement
              } else {
                If(condition, trueStatement, falseStatement)
              }
            }

            if (instructions.indexOf(jump.label) <= index) {
              throw new UnsupportedOpcodeException(jump.getOpcode, "Backward jump is not supported " +
                "because it may create a loop")
            }

            jump.getOpcode match {
              case IF_ICMPEQ | IF_ACMPEQ =>
                result = Some(compareAndJump(DSL.compareEqual))
              case IF_ICMPNE | IF_ACMPNE =>
                result = Some(compareAndJump(DSL.compareNotEqual))
              case IF_ICMPLT =>
                result = Some(compareAndJump(DSL.lessThan))
              case IF_ICMPGT =>
                result = Some(compareAndJump(DSL.greaterThan))
              case IF_ICMPLE =>
                result = Some(compareAndJump(DSL.lessEqualThan))
              case IF_ICMPGE =>
                result = Some(compareAndJump(DSL.greaterEqualThan))
              case IFNULL =>
                push(Constant(null))
                result = Some(compareAndJump(DSL.compareEqual))
              case IFNONNULL =>
                push(Constant(null))
                result = Some(compareAndJump(DSL.compareNotEqual))
              case GOTO =>
                index = instructions.indexOf(jump.label) - 1
              case IFEQ =>
                push(Constant(0))
                result = Some(compareAndJump(DSL.compareEqual))
              case IFNE =>
                push(Constant(0))
                result = Some(compareAndJump(DSL.compareNotEqual))
              case IFLT =>
                push(Constant(0))
                result = Some(compareAndJump(DSL.lessThan))
              case IFGT =>
                push(Constant(0))
                result = Some(compareAndJump(DSL.greaterThan))
              case IFLE =>
                push(Constant(0))
                result = Some(compareAndJump(DSL.lessEqualThan))
              case IFGE =>
                push(Constant(0))
                result = Some(compareAndJump(DSL.greaterEqualThan))
            }
          case loadConstant: LdcInsnNode => {
            val constant = loadConstant.cst
            constant match {
              case i: java.lang.Integer => push(Constant[Int](i))
              case f: java.lang.Float => push(Constant[Float](f))
              case d: java.lang.Double => push(Constant[Double](d))
              case l: java.lang.Long => push(Constant[Long](l))
              case str: java.lang.String => push(Constant[String](str))
              case other =>
                throw new UnsupportedOpcodeException(
                  loadConstant.getOpcode,
                  s"LDC only supports type Int, Float, Double, Long and String, current type is" +
                    s"${other.getClass.getName}")
            }
          }
          case localVarible: VarInsnNode =>
            localVarible.getOpcode match {
              case ILOAD | LLOAD | FLOAD | DLOAD | ALOAD =>
                push(localVars(localVarible.`var`))
              case ISTORE | LSTORE | FSTORE | DSTORE | ASTORE =>
                val top = pop()
                localVars += localVarible.`var` -> top
            }
          case instruction: InsnNode =>
            instruction.getOpcode match {
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
                push(DSL.plus(left, right))
              case ISUB | LSUB | FSUB | DSUB =>
                val right = pop()
                val left = pop()
                push(DSL.minus(left, right))
              case IMUL | LMUL | FMUL | DMUL =>
                val right = pop()
                val left = pop()
                push(DSL.mul(left, right))
              case IDIV | LDIV | FDIV | DDIV =>
                val right = pop()
                val left = pop()
                push(DSL.div(left, right))
              case IREM | LREM | FREM | DREM =>
                val right = pop()
                val left = pop()
                push(DSL.rem(left, right))
              case INEG =>
                val top = pop()
                push(DSL.minus(Constant(0), top))
              case LNEG =>
                val top = pop()
                push(DSL.minus(Constant(0L), top))
              case FNEG | DNEG =>
                val top = pop()
                push(DSL.minus(Constant(0F), top))
              case DNEG =>
                val top = pop()
                push(DSL.minus(Constant(0D), top))
              case IAND | LAND =>
                val right = pop()
                val left = pop()
                push(DSL.and(left, right))
              case IOR | LOR =>
                val right = pop()
                val left = pop()
                push(DSL.or(left, right))
              case IXOR | LXOR =>
                val right = pop()
                val left = pop()
                push(DSL.xor(left, right))
              case I2L | F2L | D2L =>
                push(DSL.cast[Long](pop))
              case L2I | F2I | D2I =>
                push(DSL.cast[Int](pop))
              case I2F | L2F | D2F =>
                push(DSL.cast[Float](pop))
              case I2D | L2D | F2D =>
                push(DSL.cast[Double](pop))
              case I2B => push(DSL.cast[Byte](pop))
              case I2C => push(DSL.cast[String](pop))
              case I2S => push(DSL.cast[Short](pop))
              case LCMP | FCMPL | FCMPG | DCMPL | DCMPG =>
                val jump = instructions.get(index + 1).getOpcode match {
                  case IFEQ | IFNE | IFLT | IFGT | IFLE | IFGE =>
                    instructions.get(index + 1).asInstanceOf[JumpInsnNode]
                  case _ =>
                    throw new UnsupportedOpcodeException(
                      opcode,
                      s"${Printer.OPCODES(instruction.getOpcode)} need be followed by a jump " +
                        s"instruction like IFEQ, IFNE, IFLT, IFGT, IFLE, IFGE")
                }

                // Rewrite the instruction...
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
                }

                (instruction.getOpcode, stackCategories) match {
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
                    throw new UnsupportedOpcodeException(op, "Stack mismatch")
                }
              case ARRAYLENGTH =>
                val array = pop()
                array match  {
                  case ArrayNode(length, _, _) => push(length)
                  case x => throw new ByteCodeParserExecption("Expect an array from stack, but " +
                    s"we get ${x.getClass.getSimpleName}")
                }
              case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD =>
                val index = pop()
                val array = pop()
                (index, array) match {
                  case (Constant(index: Int), node@ ArrayNode(_, _, _)) =>
                    push(node.get(index))
                  case _ =>
                    throw new UnsupportedOpcodeException(instruction.getOpcode)
                }
              case IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE =>
                val data = pop()
                val index = pop()
                val array = pop()
                (index, array) match {
                  case (Constant(index: Int), arrayNode@ ArrayNode(_, _, _)) =>
                    arrayNode.put(index, data)
                  case _ =>
                    throw new UnsupportedOpcodeException(instruction.getOpcode)
                }
              case DRETURN | FRETURN | IRETURN | LRETURN | ARETURN =>
                result = Some(pop())
              case RETURN =>
                result = Some(VOID)
            }
          case label: LabelNode => // Skip pesudo code
          case lineNumber: LineNumberNode => // Skip pesudo code
          case frame: FrameNode => // Skip pesudo code
        }

        index += 1
      }
      tracer.flush()

      if (result.isEmpty) {
        throw new ByteCodeParserExecption("Possibly not having return instructions")
      }
      result.get
    }

    val result = invoke(instructions, 0)
    Console.println(result)
    Console.println("------------------------")
    Console.println(treeString(result))
    result
  }
}
