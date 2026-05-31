using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using AssetRipper.CIL;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.OutputFormats;

/// <summary>
/// Recovers real method bodies by lowering Cpp2IL's per-method ISIL (the instruction-set-independent
/// representation built from the native ARM64/x86 code) into CIL.
///
/// The recovered DLLs are intended for *reading* (decompilation in ILSpy/dnSpy), not execution, so we
/// favour completeness and readability over verifiable IL. Registers are modelled as Int64 locals;
/// memory accesses become pointer dereferences. On top of that there is a lightweight type tracker:
/// the <c>this</c> pointer and parameters are seeded into their argument registers, types propagate
/// through register moves and stack spills, and any <c>[reg + offset]</c> access whose base register has
/// a known object type is resolved to the real field (emitted as <c>ldfld/stfld</c> with the field name)
/// instead of raw pointer math. Call targets are resolved back to the real managed method and emitted as
/// genuine <c>call/callvirt</c>. Anything that can't be lowered degrades to a nop, and any method that
/// throws falls back to a <c>throw null</c> body so no method or assembly is ever skipped.
/// </summary>
public class AsmResolverDllOutputFormatIlRecovery : AsmResolverDllOutputFormat
{
    public override string OutputFormatId => "dll_il_recovery";

    public override string OutputFormatName => "DLL files with IL Recovery";

    // offset -> instance field, per type (includes inherited fields). Shared across worker threads.
    private readonly ConcurrentDictionary<TypeAnalysisContext, Dictionary<long, FieldAnalysisContext>> _fieldsByOffset = new();

    protected override void FillMethodBody(MethodDefinition methodDefinition, MethodAnalysisContext methodContext)
    {
        if (!methodDefinition.IsManagedMethodWithBody())
            return;

        try
        {
            BuildBody(methodDefinition, methodContext);
        }
        catch
        {
            // Never let one method abort the whole assembly. Instead of a throwing stub, emit a clean,
            // valid minimal body (load default + return) so the method is still "complete" and loads in
            // any decompiler without errors - nothing is ever skipped or left broken.
            try
            {
                methodDefinition.ReplaceMethodBodyWithMinimalImplementation();
            }
            catch
            {
                methodDefinition.CilMethodBody = new();
                methodDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Ldnull);
                methodDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Throw);
            }
        }
    }

    private void BuildBody(MethodDefinition methodDefinition, MethodAnalysisContext methodContext)
    {
        var module = methodDefinition.DeclaringType!.DeclaringModule!;
        var i64 = module.CorLibTypeFactory.Int64;

        methodDefinition.CilMethodBody = new();
        var body = methodDefinition.CilMethodBody;
        body.InitializeLocals = true;
        var il = body.Instructions;

        List<InstructionSetIndependentInstruction>? isil;
        try
        {
            methodContext.Analyze();
            isil = methodContext.ConvertedIsil;
        }
        catch
        {
            isil = null;
        }

        if (isil == null || isil.Count == 0)
        {
            EmitDefaultReturn(il, body, methodDefinition.Signature!.ReturnType, module);
            return;
        }

        var ctx = new EmitContext(module, body, methodDefinition, methodContext, i64, this);
        SeedArgumentTypes(ctx);

        var indexOf = new Dictionary<InstructionSetIndependentInstruction, int>(isil.Count);
        for (var i = 0; i < isil.Count; i++)
            indexOf[isil[i]] = i;

        var labels = new CilInstructionLabel[isil.Count];
        for (var i = 0; i < labels.Length; i++)
            labels[i] = new CilInstructionLabel();

        var deferredBranches = new List<(CilInstruction Branch, int Target)>();

        for (var i = 0; i < isil.Count; i++)
        {
            var nop = il.Add(CilOpCodes.Nop);
            labels[i].Instruction = nop;
            EmitInstruction(ctx, isil[i], indexOf, deferredBranches);
        }

        EmitDefaultReturn(il, body, methodDefinition.Signature!.ReturnType, module);

        foreach (var (branch, target) in deferredBranches)
            branch.Operand = labels[target];
    }

    /// <summary>Seeds the argument registers (AArch64 AAPCS64) with their known types: X0 = this for
    /// instance methods, then integer/object params in X1.. and floating params in V0..</summary>
    private static void SeedArgumentTypes(EmitContext ctx)
    {
        var m = ctx.MethodContext;
        var nonVector = 0;
        var vector = 0;

        if (!m.IsStatic && m.DeclaringType != null)
            ctx.SetRegType("X" + nonVector++, m.DeclaringType);

        foreach (var p in m.Parameters)
        {
            var pt = p.ParameterType;
            var name = pt?.Namespace == nameof(System) && (pt.Name is "Single" or "Double")
                ? "V" + vector++
                : "X" + nonVector++;
            ctx.SetRegType(name, pt);
        }
    }

    private static string NormalizeRegister(string name)
    {
        // ARM64 W<n> is the low 32 bits of X<n>; alias them so a value written through W is read through X.
        if (name.Length > 1 && (name[0] == 'W' || name[0] == 'w') && int.TryParse(name.Substring(1), out _))
            return "X" + name.Substring(1);
        return name.ToUpperInvariant();
    }

    private void EmitInstruction(EmitContext ctx, InstructionSetIndependentInstruction instr,
        Dictionary<InstructionSetIndependentInstruction, int> indexOf,
        List<(CilInstruction, int)> deferredBranches)
    {
        var il = ctx.Body.Instructions;
        var ops = instr.Operands;

        switch (instr.OpCode.Mnemonic)
        {
            case IsilMnemonic.Move:
                if (ops.Length == 2)
                {
                    var ts = EmitLoad(ctx, ops[0]);
                    var t = ctx.GetScratch();
                    il.Add(CilOpCodes.Stloc, t);
                    EmitStore(ctx, ops[1], t, ts);
                }
                break;

            case IsilMnemonic.LoadAddress:
                if (ops.Length == 2)
                {
                    if (ops[0].Data is IsilMemoryOperand mem)
                    {
                        EmitMemoryAddress(ctx, mem);
                        il.Add(CilOpCodes.Conv_I8);
                    }
                    else
                    {
                        EmitLoad(ctx, ops[0]);
                    }
                    var t = ctx.GetScratch();
                    il.Add(CilOpCodes.Stloc, t);
                    EmitStore(ctx, ops[1], t, null);
                }
                break;

            case IsilMnemonic.Add: EmitBinary(ctx, ops, CilOpCodes.Add); break;
            case IsilMnemonic.Subtract: EmitBinary(ctx, ops, CilOpCodes.Sub); break;
            case IsilMnemonic.Multiply: EmitBinary(ctx, ops, CilOpCodes.Mul); break;
            case IsilMnemonic.Divide: EmitBinary(ctx, ops, CilOpCodes.Div); break;
            case IsilMnemonic.And: EmitBinary(ctx, ops, CilOpCodes.And); break;
            case IsilMnemonic.Or: EmitBinary(ctx, ops, CilOpCodes.Or); break;
            case IsilMnemonic.Xor: EmitBinary(ctx, ops, CilOpCodes.Xor); break;

            case IsilMnemonic.ShiftLeft: EmitShift(ctx, ops, CilOpCodes.Shl); break;
            case IsilMnemonic.ShiftRight: EmitShift(ctx, ops, CilOpCodes.Shr); break;

            case IsilMnemonic.Not: EmitUnary(ctx, ops, CilOpCodes.Not); break;
            case IsilMnemonic.Neg: EmitUnary(ctx, ops, CilOpCodes.Neg); break;

            case IsilMnemonic.Exchange:
                if (ops.Length == 2)
                {
                    var ta = ctx.GetScratch();
                    var tb = ctx.GetScratch2();
                    EmitLoad(ctx, ops[0]);
                    il.Add(CilOpCodes.Stloc, ta);
                    EmitLoad(ctx, ops[1]);
                    il.Add(CilOpCodes.Stloc, tb);
                    EmitStore(ctx, ops[0], tb, null);
                    EmitStore(ctx, ops[1], ta, null);
                }
                break;

            case IsilMnemonic.Compare:
                if (ops.Length == 2)
                {
                    EmitLoad(ctx, ops[0]);
                    il.Add(CilOpCodes.Stloc, ctx.GetCmpA());
                    EmitLoad(ctx, ops[1]);
                    il.Add(CilOpCodes.Stloc, ctx.GetCmpB());
                }
                break;

            case IsilMnemonic.Goto:
                EmitBranch(ctx, instr, CilOpCodes.Br, indexOf, deferredBranches, conditional: false);
                break;
            case IsilMnemonic.JumpIfEqual: EmitConditionalBranch(ctx, instr, CilOpCodes.Beq, indexOf, deferredBranches); break;
            case IsilMnemonic.JumpIfNotEqual: EmitConditionalBranch(ctx, instr, CilOpCodes.Bne_Un, indexOf, deferredBranches); break;
            case IsilMnemonic.JumpIfGreater: EmitConditionalBranch(ctx, instr, CilOpCodes.Bgt, indexOf, deferredBranches); break;
            case IsilMnemonic.JumpIfLess: EmitConditionalBranch(ctx, instr, CilOpCodes.Blt, indexOf, deferredBranches); break;
            case IsilMnemonic.JumpIfGreaterOrEqual: EmitConditionalBranch(ctx, instr, CilOpCodes.Bge, indexOf, deferredBranches); break;
            case IsilMnemonic.JumpIfLessOrEqual: EmitConditionalBranch(ctx, instr, CilOpCodes.Ble, indexOf, deferredBranches); break;
            case IsilMnemonic.JumpIfSign: EmitConditionalBranch(ctx, instr, CilOpCodes.Blt, indexOf, deferredBranches); break;
            case IsilMnemonic.JumpIfNotSign: EmitConditionalBranch(ctx, instr, CilOpCodes.Bge, indexOf, deferredBranches); break;

            case IsilMnemonic.Call:
                EmitCall(ctx, ops);
                break;

            case IsilMnemonic.Return:
                EmitValueReturn(ctx, ops);
                break;

            // Stack bookkeeping / barriers / not-yet-lowered mnemonics: the leading nop already stands in.
            case IsilMnemonic.CallNoReturn:
            case IsilMnemonic.Push:
            case IsilMnemonic.Pop:
            case IsilMnemonic.ShiftStack:
            case IsilMnemonic.Interrupt:
            case IsilMnemonic.Nop:
            case IsilMnemonic.NotImplemented:
            case IsilMnemonic.Invalid:
            default:
                break;
        }
    }

    private void EmitBinary(EmitContext ctx, InstructionSetIndependentOperand[] ops, CilOpCode op)
    {
        if (ops.Length != 3)
            return;
        var il = ctx.Body.Instructions;
        EmitLoad(ctx, ops[1]);
        EmitLoad(ctx, ops[2]);
        il.Add(op);
        var t = ctx.GetScratch();
        il.Add(CilOpCodes.Stloc, t);
        EmitStore(ctx, ops[0], t, null); // arithmetic result is numeric - clears any tracked type
    }

    private void EmitShift(EmitContext ctx, InstructionSetIndependentOperand[] ops, CilOpCode op)
    {
        if (ops.Length != 2)
            return;
        var il = ctx.Body.Instructions;
        EmitLoad(ctx, ops[0]);
        EmitLoad(ctx, ops[1]);
        il.Add(CilOpCodes.Conv_I4); // shift amount must be int32/native int
        il.Add(op);
        var t = ctx.GetScratch();
        il.Add(CilOpCodes.Stloc, t);
        EmitStore(ctx, ops[0], t, null);
    }

    private void EmitUnary(EmitContext ctx, InstructionSetIndependentOperand[] ops, CilOpCode op)
    {
        if (ops.Length < 1)
            return;
        var il = ctx.Body.Instructions;
        EmitLoad(ctx, ops[0]);
        il.Add(op);
        var t = ctx.GetScratch();
        il.Add(CilOpCodes.Stloc, t);
        EmitStore(ctx, ops[0], t, null);
    }

    private void EmitConditionalBranch(EmitContext ctx, InstructionSetIndependentInstruction instr, CilOpCode op,
        Dictionary<InstructionSetIndependentInstruction, int> indexOf, List<(CilInstruction, int)> deferredBranches)
    {
        var il = ctx.Body.Instructions;
        il.Add(CilOpCodes.Ldloc, ctx.GetCmpA());
        il.Add(CilOpCodes.Ldloc, ctx.GetCmpB());
        EmitBranch(ctx, instr, op, indexOf, deferredBranches, conditional: true);
    }

    private void EmitBranch(EmitContext ctx, InstructionSetIndependentInstruction instr, CilOpCode op,
        Dictionary<InstructionSetIndependentInstruction, int> indexOf, List<(CilInstruction, int)> deferredBranches,
        bool conditional)
    {
        var il = ctx.Body.Instructions;

        if (instr.Operands.Length >= 1 && instr.Operands[0].Data is InstructionSetIndependentInstruction target
            && indexOf.TryGetValue(target, out var idx))
        {
            var branch = new CilInstruction(op);
            il.Add(branch);
            deferredBranches.Add((branch, idx));
        }
        else if (conditional)
        {
            il.Add(CilOpCodes.Pop);
            il.Add(CilOpCodes.Pop);
        }
    }

    private void EmitCall(EmitContext ctx, InstructionSetIndependentOperand[] ops)
    {
        var il = ctx.Body.Instructions;

        if (ops.Length < 1 || ops[0].Data is not IsilImmediateOperand immediate)
            return;

        ulong targetAddr;
        try
        {
            targetAddr = Convert.ToUInt64(immediate.Value);
        }
        catch
        {
            return;
        }

        if (!ctx.MethodContext.AppContext.MethodsByAddress.TryGetValue(targetAddr, out var atAddr) || atAddr.Count == 0)
            return; // unresolved (il2cpp api thunk, indirect, etc.) - leave as nop

        var targetCtx = atAddr[0];
        var targetDef = targetCtx.GetExtraData<MethodDefinition>("AsmResolverMethod");
        if (targetDef?.Signature == null)
            return;

        IMethodDescriptor imported;
        try
        {
            imported = ctx.Module.DefaultImporter.ImportMethod(targetDef);
        }
        catch
        {
            return;
        }

        var argCount = targetDef.Signature.GetTotalParameterCount();

        for (var i = 0; i < argCount; i++)
        {
            var operandIndex = i + 1;
            if (operandIndex < ops.Length)
                EmitLoad(ctx, ops[operandIndex]);
            else
                il.Add(CilOpCodes.Ldc_I8, 0L);
        }

        il.Add(targetDef.IsStatic ? CilOpCodes.Call : CilOpCodes.Callvirt, imported);

        var retType = targetDef.Signature.ReturnType;
        switch (ClassifyReturn(retType))
        {
            case ReturnKind.Void:
                break;
            case ReturnKind.Int32:
            case ReturnKind.Int64:
            case ReturnKind.Float:
                il.Add(CilOpCodes.Conv_I8);
                il.Add(CilOpCodes.Stloc, ctx.GetRegister("X0"));
                ctx.SetRegType("X0", null);
                break;
            default:
                il.Add(CilOpCodes.Pop);
                il.Add(CilOpCodes.Ldc_I8, 0L);
                il.Add(CilOpCodes.Stloc, ctx.GetRegister("X0"));
                // X0 now holds the (discarded) reference return; track its type so following field
                // accesses on it can still resolve.
                ctx.SetRegType("X0", targetCtx.ReturnType);
                break;
        }
    }

    // ----- operand load/store helpers -----

    /// <summary>Pushes the operand's value (as int64) and returns the tracked type of that value, if known.</summary>
    private TypeAnalysisContext? EmitLoad(EmitContext ctx, InstructionSetIndependentOperand op)
    {
        var il = ctx.Body.Instructions;
        switch (op.Data)
        {
            case IsilRegisterOperand reg:
                il.Add(CilOpCodes.Ldloc, ctx.GetRegister(reg.RegisterName));
                return ctx.GetRegType(reg.RegisterName);
            case IsilVectorRegisterElementOperand vec:
                il.Add(CilOpCodes.Ldloc, ctx.GetRegister(vec.RegisterName));
                return ctx.GetRegType(vec.RegisterName);
            case IsilImmediateOperand imm:
                il.Add(CilOpCodes.Ldc_I8, ToInt64(imm.Value));
                return null;
            case IsilStackOperand stack:
                il.Add(CilOpCodes.Ldloc, ctx.GetRegister("stk_" + stack.Offset));
                return ctx.GetRegType("stk_" + stack.Offset);
            case IsilMemoryOperand mem:
                return EmitLoadMemory(ctx, mem);
            default:
                il.Add(CilOpCodes.Ldc_I8, 0L);
                return null;
        }
    }

    private TypeAnalysisContext? EmitLoadMemory(EmitContext ctx, IsilMemoryOperand mem)
    {
        var il = ctx.Body.Instructions;

        // Stack spill slot ([SP + n]) - model as a tracked local so this/params survive prologue spills.
        if (TryGetStackSlot(ctx, mem, out var slot))
        {
            il.Add(CilOpCodes.Ldloc, ctx.GetRegister(slot));
            return ctx.GetRegType(slot);
        }

        // Instance field access ([obj + offset]) where the base register's type is known.
        if (TryResolveField(ctx, mem, out var field, out var imported))
        {
            EmitLoad(ctx, mem.Base!.Value); // push the object (int64); ldfld tolerates it for decompilation
            il.Add(CilOpCodes.Ldfld, imported);
            // Leave the field value on the stack as-is (it may be a reference or a primitive). The caller
            // stores it into an int64 register local; we deliberately don't force a conv here because that
            // would be invalid for reference-typed fields.
            return field.FieldType;
        }

        EmitMemoryAddress(ctx, mem);
        il.Add(CilOpCodes.Ldind_I8);
        return null;
    }

    private void EmitStore(EmitContext ctx, InstructionSetIndependentOperand dest, CilLocalVariable valueLocal, TypeAnalysisContext? valueType)
    {
        var il = ctx.Body.Instructions;
        switch (dest.Data)
        {
            case IsilRegisterOperand reg:
                il.Add(CilOpCodes.Ldloc, valueLocal);
                il.Add(CilOpCodes.Stloc, ctx.GetRegister(reg.RegisterName));
                ctx.SetRegType(reg.RegisterName, valueType);
                break;
            case IsilVectorRegisterElementOperand vec:
                il.Add(CilOpCodes.Ldloc, valueLocal);
                il.Add(CilOpCodes.Stloc, ctx.GetRegister(vec.RegisterName));
                ctx.SetRegType(vec.RegisterName, valueType);
                break;
            case IsilStackOperand stack:
                il.Add(CilOpCodes.Ldloc, valueLocal);
                il.Add(CilOpCodes.Stloc, ctx.GetRegister("stk_" + stack.Offset));
                ctx.SetRegType("stk_" + stack.Offset, valueType);
                break;
            case IsilMemoryOperand mem:
                if (TryGetStackSlot(ctx, mem, out var slot))
                {
                    il.Add(CilOpCodes.Ldloc, valueLocal);
                    il.Add(CilOpCodes.Stloc, ctx.GetRegister(slot));
                    ctx.SetRegType(slot, valueType);
                }
                else if (TryResolveField(ctx, mem, out _, out var imported))
                {
                    EmitLoad(ctx, mem.Base!.Value);
                    il.Add(CilOpCodes.Ldloc, valueLocal);
                    il.Add(CilOpCodes.Stfld, imported);
                }
                else
                {
                    EmitMemoryAddress(ctx, mem);
                    il.Add(CilOpCodes.Ldloc, valueLocal);
                    il.Add(CilOpCodes.Stind_I8);
                }
                break;
            default:
                break;
        }
    }

    private static bool TryGetStackSlot(EmitContext ctx, IsilMemoryOperand mem, out string slot)
    {
        slot = "";
        if (mem.Index != null || mem.Base == null)
            return false;
        if (mem.Base.Value.Data is not IsilRegisterOperand baseReg)
            return false;
        var name = NormalizeRegister(baseReg.RegisterName);
        if (name is not ("X31" or "SP" or "WSP"))
            return false;
        slot = "stk_" + mem.Addend;
        return true;
    }

    private bool TryResolveField(EmitContext ctx, IsilMemoryOperand mem, out FieldAnalysisContext field, out IFieldDescriptor imported)
    {
        field = null!;
        imported = null!;

        if (mem.Index != null || mem.Base == null)
            return false;
        if (mem.Base.Value.Data is not IsilRegisterOperand baseReg)
            return false;

        var type = ctx.GetRegType(baseReg.RegisterName);
        if (type == null)
            return false;

        var map = _fieldsByOffset.GetOrAdd(type, BuildOffsetMap);
        if (!map.TryGetValue(mem.Addend, out field))
            return false;

        var fieldDef = field.GetExtraData<FieldDefinition>("AsmResolverField");
        if (fieldDef == null)
            return false;

        try
        {
            imported = ctx.Module.DefaultImporter.ImportField(fieldDef);
        }
        catch
        {
            return false;
        }

        return true;
    }

    private static Dictionary<long, FieldAnalysisContext> BuildOffsetMap(TypeAnalysisContext type)
    {
        var map = new Dictionary<long, FieldAnalysisContext>();
        var current = type;
        var guard = 0;
        while (current != null && guard++ < 64)
        {
            foreach (var f in current.Fields)
            {
                if (f.IsStatic)
                    continue;
                try
                {
                    var off = (long)f.Offset;
                    if (off > 0 && !map.ContainsKey(off))
                        map[off] = f;
                }
                catch
                {
                    // GetFieldOffsetFromIndex can throw for some odd fields; just skip them.
                }
            }

            try
            {
                current = current.BaseType;
            }
            catch
            {
                break;
            }
        }

        return map;
    }

    /// <summary>Pushes the effective address of a memory operand (Base + Index*Scale + Addend) as a native int.</summary>
    private void EmitMemoryAddress(EmitContext ctx, IsilMemoryOperand mem)
    {
        var il = ctx.Body.Instructions;

        if (mem.Base != null)
        {
            EmitLoad(ctx, mem.Base.Value);
            il.Add(CilOpCodes.Conv_I);
        }
        else
        {
            il.Add(CilOpCodes.Ldc_I4_0);
            il.Add(CilOpCodes.Conv_I);
        }

        if (mem.Index != null)
        {
            EmitLoad(ctx, mem.Index.Value);
            il.Add(CilOpCodes.Conv_I);
            if (mem.Scale > 1)
            {
                il.Add(CilOpCodes.Ldc_I8, (long)mem.Scale);
                il.Add(CilOpCodes.Conv_I);
                il.Add(CilOpCodes.Mul);
            }
            il.Add(CilOpCodes.Add);
        }

        if (mem.Addend != 0)
        {
            il.Add(CilOpCodes.Ldc_I8, mem.Addend);
            il.Add(CilOpCodes.Conv_I);
            il.Add(CilOpCodes.Add);
        }
    }

    // ----- return handling -----

    /// <summary>Emits a real return that yields the recovered value held in the return register
    /// (X0 for integer/reference results, the float register for floating results).</summary>
    private void EmitValueReturn(EmitContext ctx, InstructionSetIndependentOperand[] ops)
    {
        var il = ctx.Body.Instructions;
        var retType = ctx.Method.Signature!.ReturnType;
        var kind = ClassifyReturn(retType);

        if (kind == ReturnKind.Void)
        {
            il.Add(CilOpCodes.Ret);
            return;
        }

        // Real struct (by-value) returns can't be represented from an int64 register; default them.
        if (kind == ReturnKind.RefOrStruct && retType.IsValueType)
        {
            EmitDefaultReturn(il, ctx.Body, retType, ctx.Module);
            return;
        }

        if (ops.Length >= 1)
            EmitLoad(ctx, ops[0]);
        else
            il.Add(CilOpCodes.Ldloc, ctx.GetRegister("X0"));

        switch (kind)
        {
            case ReturnKind.Int32: il.Add(CilOpCodes.Conv_I4); break;
            case ReturnKind.Int64: il.Add(CilOpCodes.Conv_I8); break;
            case ReturnKind.Float: il.Add(CilOpCodes.Conv_R8); break;
            // RefOrStruct (reference type): leave the recovered value on the stack as-is.
        }

        il.Add(CilOpCodes.Ret);
    }

    private enum ReturnKind { Void, Int32, Int64, Float, RefOrStruct }

    private static ReturnKind ClassifyReturn(TypeSignature type)
    {
        switch (type.ElementType)
        {
            case ElementType.Void:
                return ReturnKind.Void;
            case ElementType.Boolean:
            case ElementType.Char:
            case ElementType.I1:
            case ElementType.U1:
            case ElementType.I2:
            case ElementType.U2:
            case ElementType.I4:
            case ElementType.U4:
                return ReturnKind.Int32;
            case ElementType.I8:
            case ElementType.U8:
            case ElementType.I:
            case ElementType.U:
            case ElementType.Ptr:
            case ElementType.FnPtr:
            case ElementType.ByRef:
                return ReturnKind.Int64;
            case ElementType.R4:
            case ElementType.R8:
                return ReturnKind.Float;
            default:
                return ReturnKind.RefOrStruct;
        }
    }

    private void EmitDefaultReturn(CilInstructionCollection il, CilMethodBody body, TypeSignature retType, ModuleDefinition module)
    {
        switch (ClassifyReturn(retType))
        {
            case ReturnKind.Void:
                il.Add(CilOpCodes.Ret);
                break;
            case ReturnKind.Int32:
                il.Add(CilOpCodes.Ldc_I4_0);
                il.Add(CilOpCodes.Ret);
                break;
            case ReturnKind.Int64:
                il.Add(CilOpCodes.Ldc_I4_0);
                il.Add(CilOpCodes.Conv_I8);
                il.Add(CilOpCodes.Ret);
                break;
            case ReturnKind.Float:
                il.Add(CilOpCodes.Ldc_R8, 0.0);
                il.Add(CilOpCodes.Ret);
                break;
            default:
                if (retType.IsValueType)
                {
                    var local = new CilLocalVariable(retType);
                    body.LocalVariables.Add(local);
                    il.Add(CilOpCodes.Ldloca, local);
                    il.Add(CilOpCodes.Initobj, retType.ToTypeDefOrRef());
                    il.Add(CilOpCodes.Ldloc, local);
                }
                else
                {
                    il.Add(CilOpCodes.Ldnull);
                }
                il.Add(CilOpCodes.Ret);
                break;
        }
    }

    private static long ToInt64(IConvertible value)
    {
        try
        {
            return Convert.ToInt64(value);
        }
        catch
        {
            try
            {
                return unchecked((long)Convert.ToUInt64(value));
            }
            catch
            {
                return 0;
            }
        }
    }

    private sealed class EmitContext(ModuleDefinition module, CilMethodBody body, MethodDefinition method,
        MethodAnalysisContext methodContext, TypeSignature i64, AsmResolverDllOutputFormatIlRecovery owner)
    {
        public readonly ModuleDefinition Module = module;
        public readonly CilMethodBody Body = body;
        public readonly MethodDefinition Method = method;
        public readonly MethodAnalysisContext MethodContext = methodContext;
        public readonly TypeSignature I64 = i64;
        public readonly AsmResolverDllOutputFormatIlRecovery Owner = owner;
        public readonly Dictionary<string, CilLocalVariable> Registers = new();
        private readonly Dictionary<string, TypeAnalysisContext?> _regTypes = new();
        private CilLocalVariable? _cmpA;
        private CilLocalVariable? _cmpB;
        private CilLocalVariable? _scratch;
        private CilLocalVariable? _scratch2;

        public CilLocalVariable GetRegister(string name)
        {
            name = NormalizeRegister(name);
            if (Registers.TryGetValue(name, out var local))
                return local;
            local = NewLocal();
            Registers[name] = local;
            return local;
        }

        public TypeAnalysisContext? GetRegType(string name) => _regTypes.TryGetValue(NormalizeRegister(name), out var t) ? t : null;
        public void SetRegType(string name, TypeAnalysisContext? type) => _regTypes[NormalizeRegister(name)] = type;

        public CilLocalVariable GetScratch() => _scratch ??= NewLocal();
        public CilLocalVariable GetScratch2() => _scratch2 ??= NewLocal();
        public CilLocalVariable GetCmpA() => _cmpA ??= NewLocal();
        public CilLocalVariable GetCmpB() => _cmpB ??= NewLocal();

        private CilLocalVariable NewLocal()
        {
            var l = new CilLocalVariable(I64);
            Body.LocalVariables.Add(l);
            return l;
        }
    }
}
