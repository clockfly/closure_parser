package spark.closure_poc
import java.io.PrintWriter

import scala.reflect.ClassTag

import org.objectweb.asm.{ClassReader, ClassVisitor, MethodVisitor, Opcodes, Type}
import org.objectweb.asm.util.{Printer, Textifier, TraceMethodVisitor}
import scala.reflect._

import org.objectweb.asm.tree.{FieldInsnNode, FrameNode, IincInsnNode, InsnList, InsnNode, IntInsnNode, JumpInsnNode, LabelNode, LdcInsnNode, LineNumberNode, LocalVariableNode, MethodInsnNode, MethodNode, TypeInsnNode, VarInsnNode}
import scala.collection.JavaConverters._
import scala.collection.mutable

// TODO: Proof there is NO risk in using stack... (Double, and Long use 2 stack slots instad of 1)
// https://docs.oracle.com/javase/specs/jvms/se7/html/jvms-2.html#jvms-2.11.1
// TODO: Besides Scala, prove this also works for Java
// TODO: Optimize the Arimetic operations to make it simper...
// TODO: Do a cast for the final type...
object ByteCodeParser {

  val UnsupportedOpcodes = Set(
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
    Opcodes.POP2, Opcodes.DUP, Opcodes.DUP_X1, Opcodes.DUP_X2, Opcodes.DUP2,
    Opcodes.DUP2_X1, Opcodes.DUP2_X2, Opcodes.SWAP,
    Opcodes.ISHL, Opcodes.LSHL, Opcodes.ISHR, Opcodes.LSHR,Opcodes.IUSHR, Opcodes.LUSHR,
    Opcodes.ATHROW,
    Opcodes.MONITORENTER, Opcodes.MONITOREXIT,

    // TableSwitchInsnNode
    Opcodes.TABLESWITCH,

    // LookupSwitchInsnNode
    Opcodes.LOOKUPSWITCH
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

  case class Constant[T: ClassTag](value: T) extends NullaryNode {
    def dataType: Type = Type.getType(classTag[T].runtimeClass)
    override def equals(other: Any): Boolean = {
      other match {
        case Constant(v2) => value == v2
        case _ => false
      }
    }
    Console.println("DATATYPE: " + dataType)
  }

  case class Argument(dataType: Type) extends NullaryNode

  case class This(dataType: Type) extends NullaryNode

  case class Field(fieldName: String, node: Node, dataType: Type) extends NullaryNode

  val x = Cast[Long](null)

  // if (condition == true) left else right
  case class If(condition: Node, left: Node, right: Node) extends BinaryNode {
    def dataType: Type = left.dataType
  }

  case class FunctionCall(className: String, method: String, obj: Node, arguments: List[Node], dataType: Type) extends Node {
    def children: List[Node] = arguments
  }

  case class Cast[T: ClassTag](node: Node) extends UnaryNode {
    implicit val tag = classTag[T]
    override def nodeName: String = {
      s"Cast[${tag.toString()}]"
    }
    override def dataType: Type = Type.getType(tag.runtimeClass)
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
    data: mutable.Map[Int, Node] = mutable.Map.empty[Int, Node]) extends Node {

    if (length.dataType != Type.INT_TYPE) {
      throw new ByteCodeParserExecption("ArrayNode must have a size of Int type")
    }

    def elementDataType: Type = Type.getType(classTag[T].runtimeClass)
    override def dataType: Type = Type.getType(s"[${elementDataType.getDescriptor}")

    override def children: List[Node] = data.values.toList
    def get(index: Int): Node = data.getOrElse(index, Constant(0L))
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

  object Arithmetic {
    def plus(left: Node, right: Node): Node = {
      // 1. check the type of left and right to make sure they match
      // 2. if there are Constant
      // 3. pick the left value and right value
      // do the math   ()
      // return value..

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

    def rem(left: Node, right: Node): Node = {
      (left, right) match {
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
}

class ByteCodeParser {
  import spark.closure_poc.ByteCodeParser._
  private def trace: Boolean = true

  def parse[T: ClassTag](closure: Class[_]): Unit = {
    var applyMethods = List.empty[MethodNode]

    val reader = new ClassReader(closure.getName)

    reader.accept(new ClassVisitor(Opcodes.ASM5, null) {
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

    if (trace) {
      print(applyMethod)
    }
    analyze[T](closure, applyMethod)
  }

  private def print(method: MethodNode): Unit = {
    val printer = new Textifier
    method.accept(new TraceMethodVisitor(printer))
    val writer = new PrintWriter(System.out)
    printer.print(writer)
    writer.flush()
  }

  private def analyze[T: ClassTag](closure: Class[_], applyMethod: MethodNode): Node = {
    if(applyMethod.tryCatchBlocks.size() != 0) {
      throw new ByteCodeParserExecption("try...catch... is not allowed in ByteCodeParser")
    }

    var localVars: Map[Int, Node] = Map.empty[Int, Node]
    localVars += 0 -> This(Type.getType(closure))
    localVars += 1 -> Argument(Type.getArgumentTypes(applyMethod.desc)(0))

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
          throw new UnsupportedOpcodeException(opcode)
        }



        node match {
          case method: MethodInsnNode =>
            method.getOpcode match {
              case Opcodes.INVOKEVIRTUAL | Opcodes.INVOKESTATIC | Opcodes.INVOKESPECIAL |
                   Opcodes.H_INVOKEINTERFACE =>
                val className = Type.getObjectType(method.owner).getClassName
                val methodName = method.name
                val argumentTypes = Type.getArgumentTypes(method.desc)
                val returnType = Type.getReturnType(method.desc)
                val arguments = (0 until argumentTypes.length).toList.map {_ =>
                  stack.pop()
                }.reverse
                val obj = if (method.getOpcode == Opcodes.INVOKESTATIC) {
                  null
                } else {
                  stack.pop()
                }
                if (obj.isInstanceOf[Argument] && arguments.length == 0) {
                  stack.push(Field(methodName, obj, returnType))
                } else {
                  stack.push(FunctionCall(className, methodName, obj, arguments, returnType))
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
            intInstruction.getOpcode match {
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
            val array = typeInstruction.getOpcode match {
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

            if (instructions.indexOf(jump.label) <= index) {
              throw new UnsupportedOpcodeException(jump.getOpcode, "Backward jump is not supported " +
                "because it creates a loop")
            }

            jump.getOpcode match {
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
                stack.push(Constant(0))
                result = Some(compareAndJump(Arithmetic.compareEqual))
              case Opcodes.IFNE =>
                stack.push(Constant(0))
                result = Some(compareAndJump(Arithmetic.compareNotEqual))
              case Opcodes.IFLT =>
                stack.push(Constant(0))
                result = Some(compareAndJump(Arithmetic.lessThan))
              case Opcodes.IFGT =>
                stack.push(Constant(0))
                result = Some(compareAndJump(Arithmetic.greaterThan))
              case Opcodes.IFLE =>
                stack.push(Constant(0))
                result = Some(compareAndJump(Arithmetic.lessEqualThan))
              case Opcodes.IFGE =>
                stack.push(Constant(0))
                result = Some(compareAndJump(Arithmetic.greaterEqualThan))
              case Opcodes.GOTO =>
                index = instructions.indexOf(jump.label)
            }

          // TODO: Check this to make sure the type system works!!!
          case loadConstant: LdcInsnNode => stack.push(Constant(loadConstant.cst))
          case localVarible: VarInsnNode =>
            localVarible.getOpcode match {
              case Opcodes.ILOAD | Opcodes.LLOAD | Opcodes.FLOAD | Opcodes.DLOAD | Opcodes.ALOAD =>
                stack.push(localVars(localVarible.`var`))
              case Opcodes.ISTORE | Opcodes.LSTORE |
                   Opcodes.FSTORE | Opcodes.DSTORE | Opcodes.ASTORE =>
                val top = stack.pop()
                localVars += localVarible.`var` -> top
            }
          case instruction: InsnNode =>
            instruction.getOpcode match {
              case Opcodes.NOP => // Skip
              case Opcodes.ACONST_NULL => stack.push(Constant(null))
              case Opcodes.ICONST_M1 => stack.push(Constant(-1))
              case Opcodes.ICONST_0 => stack.push(Constant(0))
              case Opcodes.ICONST_1 => stack.push(Constant(1))
              case Opcodes.ICONST_2 => stack.push(Constant(2))
              case Opcodes.ICONST_3 => stack.push(Constant(3))
              case Opcodes.ICONST_4 => stack.push(Constant(4))
              case Opcodes.ICONST_5 => stack.push(Constant(5))
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
                val right = stack.pop()
                val left = stack.pop()
                stack.push(Arithmetic.rem(left, right))
              case Opcodes.INEG =>
                val top = stack.pop()
                stack.push(Arithmetic.minus(Constant(0), top))
              case Opcodes.LNEG =>
                val top = stack.pop()
                stack.push(Arithmetic.minus(Constant(0L), top))
              case Opcodes.FNEG | Opcodes.DNEG =>
                val top = stack.pop()
                stack.push(Arithmetic.minus(Constant(0F), top))
              case Opcodes.DNEG =>
                val top = stack.pop()
                stack.push(Arithmetic.minus(Constant(0D), top))
              case Opcodes.IAND | Opcodes.LAND =>
                val right = stack.pop()
                val left = stack.pop()
                stack.push(Arithmetic.and(left, right))
              case Opcodes.IOR | Opcodes.LOR =>
                val right = stack.pop()
                val left = stack.pop()
                stack.push(Arithmetic.or(left, right))
              case Opcodes.IXOR | Opcodes.LXOR =>
                val right = stack.pop()
                val left = stack.pop()
                stack.push(Arithmetic.xor(left, right))
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
                    throw new UnsupportedOpcodeException(
                      opcode, s"${Printer.OPCODES(instruction.getOpcode)} need be followed by a jump instruction like " +
                        s"IFEQ, IFNE, IFLT, IFGT, IFLE, IFGE")
                }
              case Opcodes.POP | Opcodes.POP2 =>
                // TODO: Long and Double element take two stack slots. We need to make sure POP2
                // only pop ONE element.
                stack.pop()

              case Opcodes.ARRAYLENGTH =>
                val array = stack.pop()
                array match  {
                  case ArrayNode(length, _) => stack.push(length)
                  case x => throw new ByteCodeParserExecption("Expect an array from stack, but " +
                    s"we get ${x.getClass.getSimpleName}")
                }
              case Opcodes.IALOAD | Opcodes.LALOAD | Opcodes.FALOAD | Opcodes.DALOAD |
                   Opcodes.AALOAD | Opcodes.BALOAD | Opcodes.CALOAD | Opcodes.SALOAD =>
                val index = stack.pop()
                val array = stack.pop()
                (index, array) match {
                  case (Constant(index: Int), node@ ArrayNode(_, _)) =>
                    stack.push(node.get(index))
                  case _ =>
                    throw new UnsupportedOpcodeException(instruction.getOpcode)
                }
              case Opcodes.IASTORE | Opcodes.LASTORE | Opcodes.FASTORE | Opcodes.DASTORE |
                   Opcodes.AASTORE | Opcodes.BASTORE | Opcodes.CASTORE | Opcodes.SASTORE =>
                val data = stack.pop()
                val index = stack.pop()
                val array = stack.pop()
                (index, array) match {
                  case (Constant(index: Int), arrayNode@ ArrayNode(_, _)) =>
                    arrayNode.put(index, data)
                  case _ =>
                    throw new UnsupportedOpcodeException(instruction.getOpcode)
                }
              case Opcodes.DRETURN | Opcodes.FRETURN | Opcodes.IRETURN | Opcodes.LRETURN |
                   Opcodes.ARETURN =>
                result = Some(stack.pop())
              case Opcodes.RETURN =>
                throw new UnsupportedOpcodeException(opcode)
            }
          case label: LabelNode => // Skip pesudo code
          case lineNumber: LineNumberNode => // Skip pesudo code
          case frame: FrameNode => // Skip pesudo code
        }
        index += 1
      }

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
