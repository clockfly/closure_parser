package spark.closure_poc

import org.objectweb.asm.{AnnotationVisitor, Attribute, Handle, Label, MethodVisitor, Opcodes, TypePath}
import org.objectweb.asm.util.{TraceAnnotationVisitor, Printer}

/**
 * Print message...
 */
class MyMethodTracer(_mv: MethodVisitor, p: Printer) extends MethodVisitor(Opcodes.ASM5, _mv) {

  def this(p: Printer) {
    this(null, p)
  }

  override def visitParameter(name: String, access: Int) {
    p.visitParameter(name, access)
    super.visitParameter(name, access)
  }
  override def visitAnnotation(desc: String, visible: Boolean): AnnotationVisitor = {
    val p: Printer = this.p.visitMethodAnnotation(desc, visible)
    val av: AnnotationVisitor = if (mv == null) null
    else mv.visitAnnotation(desc, visible)
    return new TraceAnnotationVisitor(av, p)
  }
  override def visitTypeAnnotation(typeRef: Int, typePath: TypePath, desc: String, visible: Boolean): AnnotationVisitor = {
    val p: Printer = this.p.visitMethodTypeAnnotation(typeRef, typePath, desc, visible)
    val av: AnnotationVisitor = if (mv == null) null
    else mv.visitTypeAnnotation(typeRef, typePath, desc, visible)
    return new TraceAnnotationVisitor(av, p)
  }
  override def visitAttribute(attr: Attribute) {
    p.visitMethodAttribute(attr)
    super.visitAttribute(attr)
  }
  override def visitAnnotationDefault: AnnotationVisitor = {
    val p: Printer = this.p.visitAnnotationDefault
    val av: AnnotationVisitor = if (mv == null) null
    else mv.visitAnnotationDefault
    return new TraceAnnotationVisitor(av, p)
  }
  override def visitParameterAnnotation(parameter: Int, desc: String, visible: Boolean): AnnotationVisitor = {
    val p: Printer = this.p.visitParameterAnnotation(parameter, desc, visible)
    val av: AnnotationVisitor = if (mv == null) null
    else mv.visitParameterAnnotation(parameter, desc, visible)
    return new TraceAnnotationVisitor(av, p)
  }
  override def visitCode {
    p.visitCode
    super.visitCode
  }
  override def visitFrame(`type`: Int, nLocal: Int, local: Array[AnyRef], nStack: Int, stack: Array[AnyRef]) {
    p.visitFrame(`type`, nLocal, local, nStack, stack)
    super.visitFrame(`type`, nLocal, local, nStack, stack)
  }
  override def visitInsn(opcode: Int) {
    p.visitInsn(opcode)
    super.visitInsn(opcode)
  }
  override def visitIntInsn(opcode: Int, operand: Int) {
    p.visitIntInsn(opcode, operand)
    super.visitIntInsn(opcode, operand)
  }
  override def visitVarInsn(opcode: Int, `var`: Int) {
    p.visitVarInsn(opcode, `var`)
    super.visitVarInsn(opcode, `var`)
  }
  override def visitTypeInsn(opcode: Int, `type`: String) {
    p.visitTypeInsn(opcode, `type`)
    super.visitTypeInsn(opcode, `type`)
  }
  override def visitFieldInsn(opcode: Int, owner: String, name: String, desc: String) {
    p.visitFieldInsn(opcode, owner, name, desc)
    super.visitFieldInsn(opcode, owner, name, desc)
  }
  @deprecated override def visitMethodInsn(opcode: Int, owner: String, name: String, desc: String) {
    if (api >= Opcodes.ASM5) {
      super.visitMethodInsn(opcode, owner, name, desc)
      return
    }
    p.visitMethodInsn(opcode, owner, name, desc)
    if (mv != null) {
      mv.visitMethodInsn(opcode, owner, name, desc)
    }
  }
  override def visitMethodInsn(opcode: Int, owner: String, name: String, desc: String, itf: Boolean) {
    if (api < Opcodes.ASM5) {
      super.visitMethodInsn(opcode, owner, name, desc, itf)
      return
    }
    p.visitMethodInsn(opcode, owner, name, desc, itf)
    if (mv != null) {
      mv.visitMethodInsn(opcode, owner, name, desc, itf)
    }
  }
  override def visitInvokeDynamicInsn(name: String, desc: String, bsm: Handle, bsmArgs: AnyRef*) {
    p.visitInvokeDynamicInsn(name, desc, bsm, bsmArgs: _*)
    super.visitInvokeDynamicInsn(name, desc, bsm, bsmArgs: _*)
  }
  override def visitJumpInsn(opcode: Int, label: Label) {
    p.visitJumpInsn(opcode, label)
    super.visitJumpInsn(opcode, label)
  }
  override def visitLabel(label: Label) {
    p.visitLabel(label)
    super.visitLabel(label)
  }
  override def visitLdcInsn(cst: Any) {
    p.visitLdcInsn(cst)
    super.visitLdcInsn(cst)
  }
  override def visitIincInsn(`var`: Int, increment: Int) {
    p.visitIincInsn(`var`, increment)
    super.visitIincInsn(`var`, increment)
  }
  override def visitTableSwitchInsn(min: Int, max: Int, dflt: Label, labels: Label*) {
    p.visitTableSwitchInsn(min, max, dflt, labels: _*)
    super.visitTableSwitchInsn(min, max, dflt, labels: _*)
  }
  override def visitLookupSwitchInsn(dflt: Label, keys: Array[Int], labels: Array[Label]) {
    p.visitLookupSwitchInsn(dflt, keys, labels)
    super.visitLookupSwitchInsn(dflt, keys, labels)
  }
  override def visitMultiANewArrayInsn(desc: String, dims: Int) {
    p.visitMultiANewArrayInsn(desc, dims)
    super.visitMultiANewArrayInsn(desc, dims)
  }
  override def visitInsnAnnotation(typeRef: Int, typePath: TypePath, desc: String, visible: Boolean): AnnotationVisitor = {
    val p: Printer = this.p.visitInsnAnnotation(typeRef, typePath, desc, visible)
    val av: AnnotationVisitor = if (mv == null) null
    else mv.visitInsnAnnotation(typeRef, typePath, desc, visible)
    return new TraceAnnotationVisitor(av, p)
  }
  override def visitTryCatchBlock(start: Label, end: Label, handler: Label, `type`: String) {
    p.visitTryCatchBlock(start, end, handler, `type`)
    super.visitTryCatchBlock(start, end, handler, `type`)
  }
  override def visitTryCatchAnnotation(typeRef: Int, typePath: TypePath, desc: String, visible: Boolean): AnnotationVisitor = {
    val p: Printer = this.p.visitTryCatchAnnotation(typeRef, typePath, desc, visible)
    val av: AnnotationVisitor = if (mv == null) null
    else mv.visitTryCatchAnnotation(typeRef, typePath, desc, visible)
    return new TraceAnnotationVisitor(av, p)
  }
  override def visitLocalVariable(name: String, desc: String, signature: String, start: Label, end: Label, index: Int) {
    p.visitLocalVariable(name, desc, signature, start, end, index)
    super.visitLocalVariable(name, desc, signature, start, end, index)
  }
  override def visitLocalVariableAnnotation(typeRef: Int, typePath: TypePath, start: Array[Label], end: Array[Label], index: Array[Int], desc: String, visible: Boolean): AnnotationVisitor = {
    val p: Printer = this.p.visitLocalVariableAnnotation(typeRef, typePath, start, end, index, desc, visible)
    val av: AnnotationVisitor = if (mv == null) null
    else mv.visitLocalVariableAnnotation(typeRef, typePath, start, end, index, desc, visible)
    return new TraceAnnotationVisitor(av, p)
  }
  override def visitLineNumber(line: Int, start: Label) {
    p.visitLineNumber(line, start)
    super.visitLineNumber(line, start)
  }
  override def visitMaxs(maxStack: Int, maxLocals: Int) {
    p.visitMaxs(maxStack, maxLocals)
    super.visitMaxs(maxStack, maxLocals)
  }
  override def visitEnd {
    p.visitMethodEnd
    super.visitEnd
  }
}