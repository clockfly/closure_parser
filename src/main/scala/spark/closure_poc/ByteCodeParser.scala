package spark.closure_poc
import java.io.PrintWriter

import scala.reflect.ClassTag

import org.objectweb.asm.{ClassVisitor, MethodVisitor, Opcodes, Type}
import org.objectweb.asm.util.{Printer, Textifier}
import scala.reflect._

import org.objectweb.asm.tree.{FieldInsnNode, FrameNode, IincInsnNode, InsnList, InsnNode, IntInsnNode, JumpInsnNode, LabelNode, LdcInsnNode, LineNumberNode, LocalVariableNode, MethodInsnNode, MethodNode, TypeInsnNode, VarInsnNode}
import scala.collection.JavaConverters._
import scala.collection.mutable

object ByteCodeParser {

  val UnsupportedOpcodes = Set(
    // MethodInsnNode
    Opcodes.INVOKESPECIAL, Opcodes.INVOKEINTERFACE,

    // InvokeDynamicInsnNode
    Opcodes.INVOKEDYNAMIC,

    // FieldInsnNode
    Opcodes.PUTFIELD, Opcodes.PUTSTATIC,

    // MultiANewArrayInsnNode
    Opcodes.MULTIANEWARRAY,

    // TypeInsnNode
    Opcodes.NEW, Opcodes.CHECKCAST, Opcodes.INSTANCEOF,

    // JumpInsnNode, JSR is not used by Java compile since JDK6.
    Opcodes.JSR,

    // VarInsnNode, RET is not used by Java compile since JDK6.
    Opcodes.RET,

    // InsnNode
    Opcodes.POP, Opcodes.POP2, Opcodes.DUP, Opcodes.DUP_X1, Opcodes.DUP_X2, Opcodes.DUP2,
    Opcodes.DUP2_X1, Opcodes.DUP2_X2, Opcodes.SWAP,
    Opcodes.ISHL, Opcodes.LSHL, Opcodes.ISHR, Opcodes.LSHR,Opcodes.IUSHR, Opcodes.LUSHR,
    Opcodes.ARRAYLENGTH, Opcodes.ATHROW,
    Opcodes.MONITORENTER, Opcodes.MONITOREXIT,

    // TableSwitchInsnNode
    Opcodes.TABLESWITCH,

    // LookupSwitchInsnNode
    Opcodes.LOOKUPSWITCH
  )

  class UnsupportedOpCodeException(
      opCode: Int,
      message: String = "")
    extends Exception(s"Unsupported OpCode ${Printer.OPCODES(opCode)}, $message")

  trait Node {
    def children: List[Node]
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

  case class Constant(value: Any) extends NullaryNode

  case class Argument(name: String) extends NullaryNode

  case class Field(fieldName: String, node: Node) extends UnaryNode

  /**
   * @param operator +, -, *, /, <, >, ==, <=, >=,
   */
  case class Arithmetic(operator: String, left: Node, right: Node) extends BinaryNode

  object Arithmetic {
    def plus(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Long), Constant(b: Long)) => Constant(a + b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a + b)
        case _ => Arithmetic("+", left, right)
      }
    }

    def minus(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Long), Constant(b: Long)) => Constant(a - b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a - b)
        case _ => Arithmetic("-", left, right)
      }
    }

    def mul(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Long), Constant(b: Long)) => Constant(a * b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a * b)
        case _ => Arithmetic("*", left, right)
      }
    }

    def div(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Long), Constant(b: Long)) => Constant(a / b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a / b)
        case _ => Arithmetic("/", left, right)
      }
    }

    def compareEqual(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Long), Constant(b: Long)) => Constant(a == b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a == b)
        case _ => Arithmetic("==", left, right)
      }
    }

    def compareNotEqual(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Long), Constant(b: Long)) => Constant(a != b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a != b)
        case _ => Arithmetic("!=", left, right)
      }
    }

    def lessThan(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Long), Constant(b: Long)) => Constant(a < b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a < b)
        case _ => Arithmetic("<", left, right)
      }
    }

    def greaterThan(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Long), Constant(b: Long)) => Constant(a > b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a > b)
        case _ => Arithmetic(">", left, right)
      }
    }

    def lessEqualThan(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Long), Constant(b: Long)) => Constant(a <= b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a <= b)
        case _ => Arithmetic("<=", left, right)
      }
    }

    def greaterEqualThan(left: Node, right: Node): Node = {
      (left, right) match {
        case (Constant(a: Long), Constant(b: Long)) => Constant(a >= b)
        case (Constant(a: Double), Constant(b: Double)) => Constant(a >= b)
        case _ => Arithmetic(">=", left, right)
      }
    }
  }

  case class Cast[T: ClassTag](node: Node) extends UnaryNode

  // if (condition == true) left else right
  case class If(condition: Node, left: Node, right: Node) extends BinaryNode

  def treeString(node: Node): String = {
    val builder = new StringBuilder

    def simpleString: PartialFunction[Node, String] = {
      case product: Product =>
        val children: Set[Any] = product.children.toSet
        val args = product.productIterator.filterNot(children.contains(_))
        s"${product.getClass.getSimpleName} ${args.mkString(", ")}"
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

  case class ArrayNode[T](
      length: Node,
      data: mutable.Map[Long, Node] = mutable.Map.empty[Long, Node])
      (implicit val tag: ClassTag[T]) extends Node {
    override def children: List[Node] = data.values.toList
    def get(index: Long): Node = data.getOrElse(index, Constant(0L))
    def put(index: Long, value: Node): Unit = { data(index) = value }
  }
}

class ByteCodeParser[T: ClassTag](_cv: ClassVisitor, p: Printer, pw: PrintWriter)
  extends ClassVisitor(Opcodes.ASM5, _cv) {

  import spark.closure_poc.ByteCodeParser._

  val tag = classTag[T]

  def this(cv: ClassVisitor, pw: PrintWriter) {
    this(cv, new Textifier, pw)
  }

  def this(pw: PrintWriter) {
    this(null, pw)
  }

  private var applyMethods = List.empty[MethodNode]
  private var name: String = null

  override def visit(version: Int, access: Int, name: String, signature: String, superName: String, interfaces: Array[String]) {
    this.name = name
    Console.println(s"BEGIN ANALYZE CLOSURE $version, $access, $name, $signature, $superName, ${interfaces.mkString(", ")}" )
  }

  private def isApplyMethod(name: String, signature: String): Boolean = {
    val argumentTypes = Type.getArgumentTypes(signature)
    val returnType = Type.getReturnType(signature)
    val namePattern = "apply(\\$mc.*\\$sp)?"
    if (argumentTypes.length == 1 &&
      argumentTypes(0).getClassName == tag.runtimeClass.getName &&
      name.matches(namePattern)) {
      Console.println("NAME MATCH " + name + ", " + namePattern)
      true
    } else {
      false
    }
  }

  override def visitMethod(access: Int, name: String, desc: String, signature: String, exceptions: Array[String]): MethodVisitor = {
    if (isApplyMethod(name, desc)) {
      val method = new MethodNode(access, name, desc, signature, exceptions)
      applyMethods = method :: applyMethods
      method
    } else {
      null
    }
  }

  override def visitEnd: Unit = {
    Console.println(s"FINISH ANALYZE CLOSURE " + name)
    val myMethodTracer = new MyMethodTracer(null, p)
    val applyMethod = applyMethods.head
    applyMethod.accept(myMethodTracer)

    p.visitClassEnd
    if (pw != null) {
      p.print(pw)
      pw.flush
    }

    analyze(applyMethod)
    super.visitEnd
  }

  private def opcodeString(opcode: Int): String = {
    Printer.OPCODES(opcode)
  }

  private def analyze(applyMethod: MethodNode): Node = {
    // TODO: Add validation check to ensure this method can be converted to expressions.
    assert(applyMethod.tryCatchBlocks.size() == 0)

    var localVars: Map[Int, Node] = applyMethod
      .localVariables.asInstanceOf[java.util.List[LocalVariableNode]]
      .asScala.map(node => (node.index, Argument(node.name))).toMap

    val instructions = applyMethod.instructions

    def invoke(
        instructions: InsnList,
        startIndex: Int,
        stack: mutable.Stack[Node] = new mutable.Stack[Node]()): ByteCodeParser.Node = {
      var result: Option[Node] = None
      var index = startIndex

      while (index < instructions.size() && result.isEmpty) {
        val node = instructions.get(index)
        val opcode = node.getOpcode
        if (ByteCodeParser.UnsupportedOpcodes.contains(opcode)) {
          throw new UnsupportedOpCodeException(opcode)
        }

        node match {
          case method: MethodInsnNode =>
            method.getOpcode match {
              case Opcodes.INVOKEVIRTUAL =>
                Console.println("INVOKEVIRTUAL")
              case Opcodes.INVOKESTATIC =>
                if (method.owner == Type.getInternalName(classOf[Math])) {
                  Console.println("INVOKE STATIC MATH")
                }
            }
          case field: FieldInsnNode =>
            field.getOpcode match {
              case Opcodes.GETFIELD =>
                Console.println("Opcodes.GETFIELD")
              case Opcodes.GETSTATIC =>
                Console.println("Opcodes.GETSTATIC")
            }

          case intInstruction: IntInsnNode =>
            opcode match {
              case Opcodes.BIPUSH | Opcodes.SIPUSH => stack.push(Constant(intInstruction.operand))
              case Opcodes.NEWARRAY =>
                val count = stack.pop()
                val array = intInstruction.operand match {
                  case Opcodes.T_BOOLEAN => ArrayNode[Boolean](count)
                  case Opcodes.T_CHAR => ArrayNode[Char](count)
                  case Opcodes.T_FLOAT => ArrayNode[Float](count)
                  case Opcodes.T_DOUBLE => ArrayNode[Double](count)
                  case Opcodes.T_BYTE => ArrayNode[Byte](count)
                  case Opcodes.T_SHORT => ArrayNode[Short](count)
                  case Opcodes.T_INT => ArrayNode[Int](count)
                  case Opcodes.T_LONG => ArrayNode[Long](count)
                }
                stack.push(array)
            }

          case typeInstruction: TypeInsnNode =>
            val array = opcode match {
              case Opcodes.ANEWARRAY =>
                val count = stack.pop()
                val className = Type.getObjectType(typeInstruction.desc).getClassName
                val clazz = Thread.currentThread().getContextClassLoader.loadClass(className)
                ArrayNode[AnyRef](count)(ClassTag(clazz))
            }
            stack.push(array)
          case iinc: IincInsnNode =>
            val localVar = localVars(iinc.`var`)
            localVars += iinc.`var` -> Arithmetic.plus(localVar, Constant(iinc.incr))
          case jump: JumpInsnNode =>

            // compareOperator: <, >, ==, <=, >=
            def compareAndJump(comparator: (Node, Node)=> Node): Node = {
              val right = stack.pop()
              val left = stack.pop()
              val condition = left match {
                case a@Arithmetic("-", _, _) if right == Constant(0) => comparator(a.left, a.right)
                case _ => comparator(left, right)
              }

              val trueStatement = invoke(instructions, instructions.indexOf(jump.label), stack)
              val falseStatement = invoke(instructions, index + 1, stack)
              If(condition, trueStatement, falseStatement)
            }

            opcode match {
              case Opcodes.IF_ICMPEQ | Opcodes.IF_ACMPEQ => result = Some(compareAndJump(Arithmetic.compareEqual))
              case Opcodes.IF_ICMPNE | Opcodes.IF_ACMPNE => result = Some(compareAndJump(Arithmetic.compareNotEqual))
              case Opcodes.IF_ICMPLT => result = Some(compareAndJump(Arithmetic.lessThan))
              case Opcodes.IF_ICMPGT => result = Some(compareAndJump(Arithmetic.greaterThan))
              case Opcodes.IF_ICMPLE => result = Some(compareAndJump(Arithmetic.lessEqualThan))
              case Opcodes.IF_ICMPGE => result = Some(compareAndJump(Arithmetic.greaterEqualThan))
              case Opcodes.IFNULL =>
                stack.push(Constant(null))
                result = Some(compareAndJump(Arithmetic.compareEqual))
              case Opcodes.IFNONNULL =>
                stack.push(Constant(null))
                result = Some(compareAndJump(Arithmetic.compareNotEqual))
              case Opcodes.IFEQ =>
                stack.push(Constant(0L))
                result = Some(compareAndJump(Arithmetic.compareEqual))
              case Opcodes.IFNE =>
                stack.push(Constant(0L))
                result = Some(compareAndJump(Arithmetic.compareNotEqual))
              case Opcodes.IFLT =>
                stack.push(Constant(0L))
                result = Some(compareAndJump(Arithmetic.lessThan))
              case Opcodes.IFGT =>
                stack.push(Constant(0L))
                result = Some(compareAndJump(Arithmetic.greaterThan))
              case Opcodes.IFLE =>
                stack.push(Constant(0L))
                result = Some(compareAndJump(Arithmetic.lessEqualThan))
              case Opcodes.IFGE =>
                stack.push(Constant(0L))
                result = Some(compareAndJump(Arithmetic.greaterEqualThan))
              case Opcodes.GOTO =>
                index = instructions.indexOf(jump.label)
            }
          case loadConstant: LdcInsnNode => stack.push(Constant(loadConstant.cst))
          case localVarible: VarInsnNode =>
            opcode match {
              case Opcodes.ILOAD | Opcodes.LLOAD | Opcodes.FLOAD | Opcodes.DLOAD | Opcodes.ALOAD =>
                stack.push(localVars(localVarible.`var`))
              case Opcodes.ISTORE | Opcodes.LSTORE |
                   Opcodes.FSTORE | Opcodes.DSTORE | Opcodes.ASTORE =>
                val top = stack.pop()
                localVars += localVarible.`var` -> top
            }
          case instruction: InsnNode =>
            opcode match {
              case Opcodes.NOP => // Skip
              case Opcodes.ACONST_NULL => stack.push(Constant(null))
              case Opcodes.ICONST_M1 => stack.push(Constant(-1L))
              case Opcodes.ICONST_0 => stack.push(Constant(0L))
              case Opcodes.ICONST_1 => stack.push(Constant(1L))
              case Opcodes.ICONST_2 => stack.push(Constant(2L))
              case Opcodes.ICONST_3 => stack.push(Constant(3L))
              case Opcodes.ICONST_4 => stack.push(Constant(4L))
              case Opcodes.ICONST_5 => stack.push(Constant(5L))
              case Opcodes.LCONST_0 => stack.push(Constant(0L))
              case Opcodes.LCONST_1 => stack.push(Constant(1L))
              case Opcodes.FCONST_0 => stack.push(Constant(0D))
              case Opcodes.FCONST_1 => stack.push(Constant(1D))
              case Opcodes.FCONST_2 => stack.push(Constant(2D))
              case Opcodes.DCONST_0 => stack.push(Constant(0D))
              case Opcodes.DCONST_1 => stack.push(Constant(1D))
              case Opcodes.IADD | Opcodes.LADD | Opcodes.FADD | Opcodes.DADD =>
                val right = stack.pop()
                val left = stack.pop()
                stack.push(Arithmetic.plus(left, right))
              case Opcodes.ISUB | Opcodes.LSUB | Opcodes.FSUB | Opcodes.DSUB =>
                val right = stack.pop()
                val left = stack.pop()
                stack.push(Arithmetic.minus(left, right))

              case Opcodes.IMUL | Opcodes.LMUL | Opcodes.FMUL | Opcodes.DMUL =>
                val right = stack.pop()
                val left = stack.pop()
                stack.push(Arithmetic.mul(left, right))
              case Opcodes.IDIV | Opcodes.LDIV | Opcodes.FDIV | Opcodes.DDIV =>
                val right = stack.pop()
                val left = stack.pop()
                stack.push(Arithmetic.div(left, right))
              case Opcodes.IREM | Opcodes.LREM | Opcodes.FREM | Opcodes.DREM =>
                // TODO: support this
                throw new UnsupportedOpCodeException(opcode)
              case Opcodes.INEG | Opcodes.LNEG | Opcodes.FNEG | Opcodes.DNEG =>
                // TODO: support this
                throw new UnsupportedOpCodeException(opcode)
              case Opcodes.IAND | Opcodes.LAND | Opcodes.IOR | Opcodes.LOR |
                   Opcodes.IXOR | Opcodes.LXOR =>
                // TODO: support this
                throw new UnsupportedOpCodeException(opcode)
              case Opcodes.I2L | Opcodes.F2L | Opcodes.D2L =>
                stack.push(Cast[Long](stack.pop))
              case Opcodes.L2I | Opcodes.F2I | Opcodes.D2I =>
                stack.push(Cast[Int](stack.pop))
              case Opcodes.I2F | Opcodes.L2F | Opcodes.D2F =>
                stack.push(Cast[Float](stack.pop))
              case Opcodes.I2D | Opcodes.L2D | Opcodes.F2D =>
                stack.push(Cast[Double](stack.pop))
              case Opcodes.I2B => stack.push(Cast[Byte](stack.pop))
              case Opcodes.I2C => stack.push(Cast[String](stack.pop))
              case Opcodes.I2S => stack.push(Cast[Short](stack.pop))

              case Opcodes.LCMP | Opcodes.FCMPL | Opcodes.FCMPG | Opcodes.DCMPL | Opcodes.DCMPG =>
                val nextInstruction = instructions.get(index + 1)
                nextInstruction.getOpcode match {
                  case Opcodes.IFEQ | Opcodes.IFNE | Opcodes.IFLT | Opcodes.IFGT | Opcodes.IFLE |
                    Opcodes.IFGE =>
                    val right = stack.pop()
                    val left = stack.pop()
                    stack.push(Arithmetic.minus(left, right))
                  case _ =>
                    throw new UnsupportedOpCodeException(
                      opcode, s"${Printer.OPCODES(opcode)} need be followed by a jump instruction like " +
                        s"IFEQ, IFNE, IFLT, IFGT, IFLE, IFGE")
                }
              case Opcodes.IALOAD | Opcodes.LALOAD | Opcodes.FALOAD | Opcodes.DALOAD |
                   Opcodes.AALOAD | Opcodes.BALOAD | Opcodes.CALOAD | Opcodes.SALOAD =>
                val index = stack.pop()
                val array = stack.pop()
                (index, array) match {
                  case (Constant(index: Long), node@ ArrayNode(_, _)) =>
                    stack.push(node.get(index.toInt))
                  case _ =>
                    throw new UnsupportedOpCodeException(opcode)
                }

              case Opcodes.IASTORE | Opcodes.LASTORE | Opcodes.FASTORE | Opcodes.DASTORE |
                   Opcodes.AASTORE | Opcodes.BASTORE | Opcodes.CASTORE | Opcodes.SASTORE =>
                val data = stack.pop()
                val index = stack.pop()
                val array = stack.pop()

                (index, array) match {
                  case (Constant(index: Long), arrayNode@ ArrayNode(_, _)) =>
                    arrayNode.put(index, data)
                  case _ =>
                    throw new UnsupportedOpCodeException(opcode)
                }

              case Opcodes.DRETURN | Opcodes.FRETURN | Opcodes.IRETURN | Opcodes.LRETURN |
                   Opcodes.ARETURN =>
                result = Some(stack.pop())
              case Opcodes.RETURN =>
                throw new Exception("RETURN is NOT supported, MUST return something...")
            }
          case label: LabelNode => // Skip pesudo code
          case lineNumber: LineNumberNode => // Skip pesudo code
          case frame: FrameNode => // Skip pesudo code
        }
        index += 1
      }

      if (result.isEmpty) {
        throw new Exception("Possibly not having return instructions")
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
