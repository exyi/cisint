module Interpreter
open System.Collections.Concurrent
open System.Threading.Tasks
open Expression
open InterpreterState
open Mono.Cecil
open FSharp.Control.Tasks.V2
open Mono.Cecil.Cil
open System.Collections
open System.Collections.Generic
open System
open System.Threading.Tasks
open System.Collections.Immutable
open System.ComponentModel.Design
open Expression
open System.Collections.Generic
open TypesystemDefinitions
open StateProcessing
open Mono.Cecil.Rocks
open System.Collections.Generic
open System.Collections.Generic
open System.Collections.Generic
open Mono.Cecil.Cil
open System.Collections.Generic
open System.Collections.Generic
open Mono.Cecil.Cil
open System.Collections.Generic

type InterpreterFrameInfo = {
    FrameToken: obj
    Method: MethodRef
    Args: SExpr array
    BranchingFactor: int
    CurrentInstruction: Mono.Cecil.Cil.Instruction
}

type InterpreterFrameDispatcher = InterpreterFrameInfo clist -> (unit -> Task<ExecutionState * InterpreterReturnType>) -> Task<ExecutionState * InterpreterReturnType>

type ExecutionCacheEntry = {
    ArgParameters: SParameter array
    /// condition -> state; the condition may contain some references to the resulting execution state (i.e. be dependent on some side effect result), but the system should try to reduce these
    DefiniteStates: (SExpr * ExecutionState) array
}

type InstructionPrefixes = {
    Constained: TypeRef option
    NoCheck: bool
    ReadOnly: bool
    Tail: bool
    Unaligned: bool
    Volatile: bool
}

let noPrefixes = { Constained = None; InstructionPrefixes.NoCheck = false; ReadOnly = false; Tail = false; Unaligned = false; Volatile = true }

let private runAndMerge todoFunctions dispatchFrame =
    let result :Task<(ExecutionState * InterpreterReturnType) []> = Task.WhenAll<ExecutionState * InterpreterReturnType>(todoFunctions |> Seq.map (dispatchFrame))

    task {
        let! r = result
        return match r with
               | [| x |] -> x
               | [| (x, r1); (y, r2) |] ->
                    softAssert (r1 = r2) "Merging state with different control flow result, something is wrong"
                    mergeStates x y, r1
               | _ -> failwithf "NIE: merge %d states" r.Length
        // TODO: merge more than two states
    }

let stackArithmeticCoerce a b =
    if a.ResultType = b.ResultType then
        (a, b)
    else

    let unwrapEnum a =
        if a.ResultType.Definition.IsEnum then
            SExpr.Cast InstructionFunction.Convert (TypeRef(a.ResultType.Definition.GetEnumUnderlyingType())) a
        else a

    let a = unwrapEnum a
    let b = unwrapEnum b

    if a.ResultType = b.ResultType then
        (a, b)
    elif a.ResultType.IsObjectReference && b.ResultType.IsObjectReference then
        let commonCast = ExprSimplifier.findCommonAncestor a.ResultType b.ResultType
                         |> Option.defaultValue CecilTools.objType
        (SExpr.Cast InstructionFunction.Cast commonCast a, SExpr.Cast InstructionFunction.Cast commonCast b)
    elif a.ResultType = CecilTools.nintType && b.ResultType = CecilTools.intType then
        (a, SExpr.Cast InstructionFunction.Convert CecilTools.nintType b)
    elif a.ResultType = CecilTools.intType && b.ResultType = CecilTools.nintType then
        (SExpr.Cast InstructionFunction.Convert CecilTools.nintType a, b)
    else
        waitForDebug ()
        failwithf "coertion %O <-> %O not supported (expressions %s, %s)" a.ResultType b.ResultType (ExprFormat.exprToString a) (ExprFormat.exprToString b)

let rec interpretInstruction genericAssigner ((instr, prefixes): Cil.Instruction * InstructionPrefixes) ((locals, arguments): (SParameter array) * (SParameter array)) (state: ExecutionState) =
    let proc1stack (fn: SExpr -> SExpr) =
        let result, rest =
            match state.Stack with
            | a :: rest ->
                fn a, rest
            | _ -> failwithf "Can't pop a value from stack at %O" instr
        InterpretationResult.NewState ({ state with Stack = result :: rest })
    let proc2stack (fn: SExpr -> SExpr -> SExpr) =
        let result, rest =
            match state.Stack with
            | b :: a :: rest ->
                fn a b, rest
            | _ -> failwithf "Can't pop two values from stack at %O" instr
        InterpretationResult.NewState ({ state with Stack = result :: rest })
    let pushToStack (expr: SExpr) =
        InterpretationResult.NewState ({ state with Stack = expr :: state.Stack })

    let procArit fn =
        proc2stack (fun a b -> let (a, b) = stackArithmeticCoerce a b in fn a b)
    let procBasicArit fn preproc =
        procArit (fun a b ->
            let (a, b) = preproc a, preproc b
            SExpr.InstructionCall fn a.ResultType [a;b])

    let convert t preprocess =
        proc1stack (fun a -> SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType t) [preprocess a] |> stackLoadConvert)
    let convertChecked t preprocess =
        proc1stack (fun a -> SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType t) [preprocess a] |> stackLoadConvert)

    let doBranch (stack: SExpr clist) condition =
        let state = { state with Stack = stack }
        let cSimpl = SExpr.InstructionCall InstructionFunction.Convert (CecilTools.boolType) [ condition ] |> ExprSimplifier.simplify state.Assumptions
        // printfn "Branching at %O if %s -> %s" instr (ExprFormat.exprToString condition) (ExprFormat.exprToString cSimpl)
        if cSimpl.Node = SExprNode.Constant true then
            InterpretationResult.Branching [{ InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.CurrentMethod (instr.Operand :?> Cil.Instruction) }]
        elif cSimpl.Node = SExprNode.Constant false then
            InterpretationResult.NewState state
        else
            InterpretationResult.Branching [
                { InterpreterTodoItem.State = state.WithCondition [ cSimpl ]; Target = InterpreterTodoTarget.CurrentMethod (unbox instr.Operand) }
                { InterpreterTodoItem.State = state.WithCondition [ SExpr.BoolNot cSimpl ]; Target = InterpreterTodoTarget.CurrentMethod instr.Next }
            ]
    let doBranchWithCond opcode i2 =
        let state2 = match interpretInstruction genericAssigner (i2, noPrefixes) (locals, arguments) state with InterpretationResult.NewState s -> s | _ -> failwith "wtf"
        let bInst = Cil.Instruction.Create(opcode, instr.Operand :?> Cil.Instruction)
        bInst.Next <- instr.Next; bInst.Offset <- instr.Offset;
        interpretInstruction genericAssigner (bInst, prefixes) (locals, arguments) state2

    let getLocal p =
        pushToStack (state.Locals.[p] |> stackLoadConvert)
    let setLocal p =
        match state.Stack with
        | a :: rest ->
            InterpretationResult.NewState { state with Stack = rest; Locals = state.Locals.SetItem(p, stackConvert a p.Type) }
        | _ -> failwithf "Can't pop a value from stack at %O" instr

    let loadIndirect expectedTypes =
        let [addr], state = state.PopStack 1
        let result, state = dereference addr state
        if expectedTypes <> [] && not (List.contains result.ResultType expectedTypes) then failwithf "Can't load dereference to %O, one of %O was expected" result.ResultType expectedTypes
        InterpretationResult.NewState { state with Stack = stackLoadConvert result :: state.Stack }

    let typeOperand = lazy TypeRef ((instr.Operand :?> TypeReference).ResolvePreserve(genericAssigner))

    let op = instr.OpCode
    // arithmetic instructions:
    if op = OpCodes.Add || op = OpCodes.Add_Ovf || op = OpCodes.Add_Ovf_Un then
        procBasicArit InstructionFunction.Add id
    elif op = OpCodes.Sub || op = OpCodes.Sub_Ovf || op = OpCodes.Sub_Ovf_Un then
        procBasicArit InstructionFunction.Sub id
    elif op = OpCodes.And then procBasicArit InstructionFunction.And id
    elif op = OpCodes.Div then procBasicArit InstructionFunction.Div id
    elif op = OpCodes.Div_Un then procBasicArit InstructionFunction.Div stackConvertToUnsigned
    elif op = OpCodes.Mul || op = OpCodes.Mul_Ovf then procBasicArit InstructionFunction.Mul id
    elif op = OpCodes.Mul_Ovf_Un then procBasicArit InstructionFunction.Mul stackConvertToUnsigned
    elif op = OpCodes.Rem then procBasicArit InstructionFunction.Rem id
    elif op = OpCodes.Rem_Un then procBasicArit InstructionFunction.Rem stackConvertToUnsigned
    elif op = OpCodes.Or then procBasicArit InstructionFunction.Or id
    elif op = OpCodes.Xor then procBasicArit InstructionFunction.Xor id

    elif op = OpCodes.Shl then proc2stack (fun a b -> SExpr.InstructionCall InstructionFunction.Shl a.ResultType [a; b])
    elif op = OpCodes.Shr then proc2stack (fun a b -> SExpr.InstructionCall InstructionFunction.Shr a.ResultType [a; b])
    elif op = OpCodes.Shr_Un then proc2stack (fun a b -> let a = stackConvertToUnsigned a in SExpr.InstructionCall InstructionFunction.Shr a.ResultType [a; b])

    elif op = OpCodes.Ceq then procArit (fun a b -> SExpr.InstructionCall InstructionFunction.Convert CecilTools.intType [SExpr.InstructionCall InstructionFunction.C_Eq CecilTools.boolType [a;b]])
    elif op = OpCodes.Cgt then procArit (fun a b -> SExpr.InstructionCall InstructionFunction.Convert CecilTools.intType [SExpr.InstructionCall InstructionFunction.C_Gt CecilTools.boolType [a;b]])
    elif op = OpCodes.Cgt_Un then
        procArit (fun a b ->
            SExpr.InstructionCall InstructionFunction.Convert CecilTools.intType [
               (if a.ResultType.IsObjectReference && b.Node = SExprNode.Constant null then
                    // Special case for cgt.un for a != null, see note 2 on "Table III.4: Binary Comparison or Branch Operations"
                    SExpr.InstructionCall InstructionFunction.C_Eq CecilTools.boolType [a; b] |> SExpr.BoolNot
                else SExpr.InstructionCall InstructionFunction.C_Gt CecilTools.boolType [stackConvertToUnsigned a;stackConvertToUnsigned b])
            ]
        )
    elif op = OpCodes.Clt then procArit (fun a b -> SExpr.InstructionCall InstructionFunction.Convert CecilTools.intType [SExpr.InstructionCall InstructionFunction.C_Lt CecilTools.boolType [a;b]])
    elif op = OpCodes.Clt_Un then procArit (fun a b -> SExpr.InstructionCall InstructionFunction.Convert CecilTools.intType [SExpr.InstructionCall InstructionFunction.C_Lt CecilTools.boolType [stackConvertToUnsigned a;stackConvertToUnsigned b]])

    elif op = OpCodes.Neg then proc1stack (fun a -> SExpr.InstructionCall InstructionFunction.Negate a.ResultType [a])
    elif op = OpCodes.Not then proc1stack (fun a -> SExpr.InstructionCall InstructionFunction.BitNot a.ResultType [a])

    // primitive conversions
    elif op = OpCodes.Conv_I1 then convert typeof<int8> id
    elif op = OpCodes.Conv_U1 then convert typeof<uint8> id
    elif op = OpCodes.Conv_I2 then convert typeof<int16> id
    elif op = OpCodes.Conv_U2 then convert typeof<uint16> id
    elif op = OpCodes.Conv_I4 then convert typeof<int32> id
    elif op = OpCodes.Conv_U4 then convert typeof<uint32> id
    elif op = OpCodes.Conv_I8 then convert typeof<int64> id
    elif op = OpCodes.Conv_U8 then convert typeof<uint64> id
    elif op = OpCodes.Conv_R4 then convert typeof<System.Single> id
    elif op = OpCodes.Conv_R8 then convert typeof<System.Double> id
    elif op = OpCodes.Conv_R_Un then convert typeof<System.Double> stackConvertToUnsigned

    elif op = OpCodes.Conv_Ovf_I1 then convertChecked typeof<int8> id
    elif op = OpCodes.Conv_Ovf_U1 then convertChecked typeof<uint8> id
    elif op = OpCodes.Conv_Ovf_I2 then convertChecked typeof<int16> id
    elif op = OpCodes.Conv_Ovf_U2 then convertChecked typeof<uint16> id
    elif op = OpCodes.Conv_Ovf_I4 then convertChecked typeof<int32> id
    elif op = OpCodes.Conv_Ovf_U4 then convertChecked typeof<uint32> id
    elif op = OpCodes.Conv_Ovf_I8 then convertChecked typeof<int64> id
    elif op = OpCodes.Conv_Ovf_U8 then convertChecked typeof<uint64> id

    elif op = OpCodes.Conv_Ovf_I1_Un then convertChecked typeof<int8> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_U1_Un then convertChecked typeof<uint8> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_I2_Un then convertChecked typeof<int16> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_U2_Un then convertChecked typeof<uint16> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_I4_Un then convertChecked typeof<int32> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_U4_Un then convertChecked typeof<uint32> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_I8_Un then convertChecked typeof<int64> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_U8_Un then convertChecked typeof<uint64> stackConvertToUnsigned

    elif op = OpCodes.Conv_I then convert typeof<IntPtr> id
    elif op = OpCodes.Conv_Ovf_I then convertChecked typeof<IntPtr> id
    elif op = OpCodes.Conv_Ovf_I_Un then convertChecked typeof<IntPtr> stackConvertToUnsigned
    elif op = OpCodes.Conv_U then convert typeof<UIntPtr> id
    elif op = OpCodes.Conv_Ovf_U then convertChecked typeof<UIntPtr> id
    elif op = OpCodes.Conv_Ovf_U_Un then convertChecked typeof<UIntPtr> stackConvertToUnsigned


    elif op = OpCodes.Box then
        let [value], state = state.PopStack 1
        assertOrComplicated (not(value.ResultType.FullName.StartsWith "System.Nullable`1")) "Boxing nullable is not supported"
        let value, state = copyReference value state
        let value = SExpr.Cast InstructionFunction.Cast CecilTools.objType value
        InterpretationResult.NewState { state with Stack = value :: state.Stack }
    elif (op = OpCodes.Castclass || op = OpCodes.Unbox_Any) && typeOperand.Value.IsObjectReference then
        proc1stack (fun a -> SExpr.InstructionCall InstructionFunction.Cast typeOperand.Value [a])
    elif op = OpCodes.Isinst then proc1stack (fun a -> SExpr.InstructionCall InstructionFunction.IsInst typeOperand.Value [a])
    elif op = OpCodes.Unbox then
        // take reference to a boxed value
        proc1stack (fun a ->
            let a = SExpr.Cast InstructionFunction.Cast typeOperand.Value a |> ExprSimplifier.simplify state.Assumptions
            makeReference a
        )
    elif op = OpCodes.Unbox_Any then
        // upcast boxed value
        proc1stack (fun a ->
            SExpr.Cast InstructionFunction.Cast typeOperand.Value a
        )

    elif op = OpCodes.Dup then
        pushToStack <| List.head state.Stack
    elif op = OpCodes.Nop then InterpretationResult.NewState state
    elif op = OpCodes.Dup then InterpretationResult.NewState {state with Stack = List.tail state.Stack}

    elif op = OpCodes.Ldc_I4_0 then pushToStack (SExpr.ImmConstant 0)
    elif op = OpCodes.Ldc_I4_1 then pushToStack (SExpr.ImmConstant 1)
    elif op = OpCodes.Ldc_I4_2 then pushToStack (SExpr.ImmConstant 2)
    elif op = OpCodes.Ldc_I4_3 then pushToStack (SExpr.ImmConstant 3)
    elif op = OpCodes.Ldc_I4_4 then pushToStack (SExpr.ImmConstant 4)
    elif op = OpCodes.Ldc_I4_5 then pushToStack (SExpr.ImmConstant 5)
    elif op = OpCodes.Ldc_I4_6 then pushToStack (SExpr.ImmConstant 6)
    elif op = OpCodes.Ldc_I4_7 then pushToStack (SExpr.ImmConstant 7)
    elif op = OpCodes.Ldc_I4_8 then pushToStack (SExpr.ImmConstant 8)
    elif op = OpCodes.Ldc_I4_M1 then pushToStack (SExpr.ImmConstant -1)
    elif op = OpCodes.Ldc_I4 || op = OpCodes.Ldc_I4_S then pushToStack (SExpr.ImmConstant (instr.Operand |> Convert.ToInt32))
    elif op = OpCodes.Ldc_I8 then pushToStack (SExpr.ImmConstant (instr.Operand :?> int64))
    elif op = OpCodes.Ldc_R8 || op = OpCodes.Ldc_R4 then pushToStack (SExpr.ImmConstant (instr.Operand |> Convert.ToDouble))
    elif op = OpCodes.Ldnull then pushToStack (SExpr.ImmConstant (box null))
    elif op = OpCodes.Ldstr then pushToStack (SExpr.ImmConstant (instr.Operand :?> string))

    elif op = OpCodes.Ret then InterpretationResult.Return state

    elif op = OpCodes.Br || op = OpCodes.Br_S then doBranch state.Stack (SExpr.ImmConstant true)

    elif op = OpCodes.Brtrue || op = OpCodes.Brtrue_S then
        match state.Stack with
        | condition :: stack -> doBranch stack condition
        | _ -> failwithf "Nothing on stack at %O" instr

    elif op = OpCodes.Brfalse || op = OpCodes.Brfalse_S then
        match state.Stack with
        | condition :: stack -> doBranch stack (SExpr.BoolNot condition)
        | _ -> failwithf "Nothing on stack at %O" instr

    elif op = OpCodes.Beq || op = OpCodes.Beq_S then
        doBranchWithCond OpCodes.Brtrue (Cil.Instruction.Create(OpCodes.Ceq))
    elif op = OpCodes.Bge || op = OpCodes.Bge_S then
        doBranchWithCond OpCodes.Brfalse (Cil.Instruction.Create(OpCodes.Clt))
    elif op = OpCodes.Bge_Un || op = OpCodes.Bge_Un_S then
        doBranchWithCond OpCodes.Brfalse (Cil.Instruction.Create(OpCodes.Clt_Un))
    elif op = OpCodes.Bgt || op = OpCodes.Bgt_S then
        doBranchWithCond OpCodes.Brtrue (Cil.Instruction.Create(OpCodes.Cgt))
    elif op = OpCodes.Bgt_Un || op = OpCodes.Bgt_Un_S then
        doBranchWithCond OpCodes.Brtrue (Cil.Instruction.Create(OpCodes.Cgt_Un)) // TODO: float.NaN glitches
    elif op = OpCodes.Ble || op = OpCodes.Ble_S then
        doBranchWithCond OpCodes.Brfalse (Cil.Instruction.Create(OpCodes.Cgt))
    elif op = OpCodes.Ble_Un || op = OpCodes.Ble_Un_S then
        doBranchWithCond OpCodes.Brfalse (Cil.Instruction.Create(OpCodes.Cgt_Un)) // TODO: float.NaN glitches
    elif op = OpCodes.Blt || op = OpCodes.Blt_S then
        doBranchWithCond OpCodes.Brtrue (Cil.Instruction.Create(OpCodes.Clt))
    elif op = OpCodes.Blt_Un || op = OpCodes.Blt_Un_S then
        doBranchWithCond OpCodes.Brtrue (Cil.Instruction.Create(OpCodes.Clt_Un))
    elif op = OpCodes.Bne_Un || op = OpCodes.Bne_Un_S then
        doBranchWithCond OpCodes.Brfalse (Cil.Instruction.Create(OpCodes.Ceq))
    elif op = OpCodes.Pop then
        InterpretationResult.NewState { state with Stack = List.tail state.Stack }

    elif op = OpCodes.Call || op = OpCodes.Callvirt then
        let method = (instr.Operand :?> MethodReference).ResolvePreserve genericAssigner
        softAssert (not method.DeclaringType.ContainsGenericParameter) <| sprintf "%O contains generic parameters in DeclaringType" method
        // softAssert (not method.ContainsGenericParameter) <| sprintf "%O contains generic parameters" method
        let returnI = if prefixes.Tail then None; else Some instr.Next
        let args, state = state.PopStack (method.Parameters.Count + if method.HasThis then 1 else 0)
        if op = OpCodes.Callvirt && prefixes.Constained.IsSome then
            let overridenMethod = findOverridenMethod prefixes.Constained.Value (MethodRef method)
            if overridenMethod.DeclaringType = prefixes.Constained.Value then
                // the function is overriden -> invoke it directly
                InterpretationResult.Branching [ { InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.CallMethod (overridenMethod, args, returnI, false) } ]
            else
                // it's not overriden -> invoke the base implementation with boxing and stuff
                // it's only used for object.ToString, object.GetHashCode and so on, which don't mutate the object => we can ignore the copyReference
                let args = ((SExpr.InstructionCall InstructionFunction.Cast CecilTools.objType [ SExpr.Dereference args.Head ]) :: args.Tail)
                InterpretationResult.Branching [ { InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.CallMethod (MethodRef method, args, returnI, false) } ]
        else
            InterpretationResult.Branching [ { InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.CallMethod (MethodRef method, args, returnI, op = OpCodes.Callvirt) } ]

    elif op = OpCodes.Ldarg || op = OpCodes.Ldarg_S then getLocal (arguments.[(instr.Operand :?> ParameterDefinition).Sequence])
    elif op = OpCodes.Ldarg_0 then getLocal (arguments.[0])
    elif op = OpCodes.Ldarg_1 then getLocal (arguments.[1])
    elif op = OpCodes.Ldarg_2 then getLocal (arguments.[2])
    elif op = OpCodes.Ldarg_3 then getLocal (arguments.[3])
    elif op = OpCodes.Ldloc || op = OpCodes.Ldloc_S then getLocal (locals.[(instr.Operand :?> VariableDefinition).Index])
    elif op = OpCodes.Ldloc_0 then getLocal (locals.[0])
    elif op = OpCodes.Ldloc_1 then getLocal (locals.[1])
    elif op = OpCodes.Ldloc_2 then getLocal (locals.[2])
    elif op = OpCodes.Ldloc_3 then getLocal (locals.[3])
    elif op = OpCodes.Ldloca || op = OpCodes.Ldloca_S then
        pushToStack (SExpr.ParamReference (locals.[(instr.Operand :?> VariableDefinition).Index]))
    elif op = OpCodes.Ldarga || op = OpCodes.Ldarga_S then
        pushToStack (SExpr.ParamReference (arguments.[(instr.Operand :?> ParameterDefinition).Sequence]))

    elif op = OpCodes.Starg || op = OpCodes.Starg_S then setLocal (arguments.[(instr.Operand :?> ParameterDefinition).Sequence])
    elif op = OpCodes.Stloc || op = OpCodes.Stloc_S then setLocal (locals.[(instr.Operand :?> VariableDefinition).Index])
    elif op = OpCodes.Stloc_0 then setLocal (locals.[0])
    elif op = OpCodes.Stloc_1 then setLocal (locals.[1])
    elif op = OpCodes.Stloc_2 then setLocal (locals.[2])
    elif op = OpCodes.Stloc_3 then setLocal (locals.[3])

    elif op = OpCodes.Ldind_I1 then loadIndirect [CecilTools.convertType typeof<SByte>]
    elif op = OpCodes.Ldind_U1 then loadIndirect [CecilTools.convertType typeof<Byte>; CecilTools.boolType]
    elif op = OpCodes.Ldind_I2 then loadIndirect [CecilTools.convertType typeof<Int16>]
    elif op = OpCodes.Ldind_U2 then loadIndirect [CecilTools.convertType typeof<UInt16>]
    elif op = OpCodes.Ldind_I4 then loadIndirect [CecilTools.convertType typeof<Int32>]
    elif op = OpCodes.Ldind_U4 then loadIndirect [CecilTools.convertType typeof<UInt32>]
    elif op = OpCodes.Ldind_I8 then loadIndirect [CecilTools.convertType typeof<UInt64>; CecilTools.convertType typeof<Int64>] // it can load uint64 using this instruction too
    elif op = OpCodes.Ldind_R4 then loadIndirect [CecilTools.convertType typeof<Single>]
    elif op = OpCodes.Ldind_R8 then loadIndirect [CecilTools.convertType typeof<float>]
    elif op = OpCodes.Ldind_Ref then loadIndirect [] // may load any reference type
    elif op = OpCodes.Ldind_I then loadIndirect [CecilTools.nintType]

    elif op = OpCodes.Newobj then
        // TODO: Delegates
        let constructor = (instr.Operand :?> Mono.Cecil.MethodReference).ResolvePreserve genericAssigner
        let args, state = state.PopStack constructor.Parameters.Count
        let object, state = createEmptyHeapObject (TypeRef constructor.DeclaringType) state
        let state = { state with Stack = SExpr.Parameter object :: state.Stack }
        let returnI = if prefixes.Tail then None; else Some instr.Next
        let firstArg =
            if object.Type.Reference.IsValueType then
                SExpr.ParamReference object
            else SExpr.Parameter object
        InterpretationResult.Branching [
            { InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.CallMethod (MethodRef constructor, firstArg :: args, returnI, false) }
        ]
    elif op = OpCodes.Ldfld then
        let field = (instr.Operand :?> Mono.Cecil.FieldReference).ResolvePreserve genericAssigner |> FieldRef
        let [target], state = state.PopStack 1
        let result, state = accessField target (FieldOrElement.FieldRef field) state
        InterpretationResult.NewState { state with Stack = stackLoadConvert result :: state.Stack }

    elif op = OpCodes.Ldsfld then
        let field = (instr.Operand :?> Mono.Cecil.FieldReference).ResolvePreserve genericAssigner |> FieldRef
        let result, state = accessStaticField field state
        InterpretationResult.NewState { state with Stack = stackLoadConvert result :: state.Stack }

    elif op = OpCodes.Ldflda then
        // the address is simply loaded as an expression. The magic is handled when it's dereferenced
        let field = (instr.Operand :?> Mono.Cecil.FieldReference).ResolvePreserve genericAssigner |> FieldRef
        proc1stack (fun e -> SExpr.New (Mono.Cecil.ByReferenceType(field.FieldType.Reference) |> TypeRef) (SExprNode.Reference (SLExprNode.LdField (field, Some e))))
    elif op = OpCodes.Ldsflda then
        let field = instr.Operand :?> Mono.Cecil.FieldReference |> FieldRef
        pushToStack (SExpr.New (Mono.Cecil.ByReferenceType(field.FieldType.Reference) |> TypeRef) (SExprNode.Reference (SLExprNode.LdField (field, None))))

    elif op = OpCodes.Stfld then
        let field = (instr.Operand :?> Mono.Cecil.FieldReference).ResolvePreserve genericAssigner |> FieldRef
        let [target; value], state = state.PopStack 2
        let state = setField target field value state
        InterpretationResult.NewState state

    elif op = OpCodes.Stsfld then
        let field = (instr.Operand :?> Mono.Cecil.FieldReference).ResolvePreserve genericAssigner |> FieldRef
        let [value], state = state.PopStack 1
        let state = setStaticField field value state
        InterpretationResult.NewState state

    elif op = OpCodes.Newarr then
        let [len], state = state.PopStack 1
        let elType = instr.Operand :?> TypeReference |> TypeRef
        let object, state = newArray (Some len) elType state
        let objParam = getObjectParam object.Type
        let state = state.ChangeObject [ objParam, object ]
        let state = { state with Stack = SExpr.Parameter objParam :: state.Stack }
        InterpretationResult.NewState state

    elif op = OpCodes.Ldelem_Any ||
         op = OpCodes.Ldelem_Ref ||
         op = OpCodes.Ldelem_I ||
         op = OpCodes.Ldelem_I1 ||
         op = OpCodes.Ldelem_I2 ||
         op = OpCodes.Ldelem_I4 ||
         op = OpCodes.Ldelem_I8 ||
         op = OpCodes.Ldelem_R4 ||
         op = OpCodes.Ldelem_R8 ||
         op = OpCodes.Ldelem_U1 ||
         op = OpCodes.Ldelem_U2 ||
         op = OpCodes.Ldelem_U4 then
         let [target; index], state = state.PopStack 2
         let e, state = StateProcessing.accessField target (FieldOrElement.ElementRef (index, (target.ResultType.Reference :?> Mono.Cecil.ArrayType).ElementType |> TypeRef)) state
         InterpretationResult.NewState ({state with Stack = stackLoadConvert e :: state.Stack})
    elif op = OpCodes.Stelem_Any ||
         op = OpCodes.Stelem_Ref ||
         op = OpCodes.Stelem_I ||
         op = OpCodes.Stelem_I1 ||
         op = OpCodes.Stelem_I2 ||
         op = OpCodes.Stelem_I4 ||
         op = OpCodes.Stelem_I8 ||
         op = OpCodes.Stelem_R4 ||
         op = OpCodes.Stelem_R8 then
         let [target; index; value], state = state.PopStack 3
         let state = StateProcessing.setElement target index value state
         InterpretationResult.NewState (state)
    elif op = OpCodes.Ldlen then
        let [target], state = state.PopStack 1
        let r, state = StateProcessing.accessLength target state
        InterpretationResult.NewState ({state with Stack = stackLoadConvert r :: state.Stack})

    elif op = OpCodes.Leave || op = OpCodes.Leave_S then
        InterpretationResult.ExitExceptionHandler (state, Some(instr.Operand :?> _))
    elif op = OpCodes.Endfinally then
        InterpretationResult.ExitExceptionHandler (state, None)

    else tooComplicated <| sprintf "unsupported instruction %O" instr

let initializeExceptionHandler (handler: ExceptionHandler) (state: ExecutionState) =
    softAssert (state.Stack.IsEmpty) "Stack has to be empty when exception handler starts"
    let state2 = state.WithCondition []
    state2

let private takeInterpretationReturnState (t: Task<ExecutionState * InterpreterReturnType>) =
    task {
        let! (r, target) = t
        softAssert (target = NextMethod) "something's wrong with control-flow"
        return r
    }


let rec interpretMethodCore (methodref: MethodRef) (state: ExecutionState) (args: SExpr array) (dispatchFrame: InterpreterFrameDispatcher) =
    let methodDef = methodref.Definition
    let method = methodref.Reference
    let genericAssigner = methodref.GenericParameterAssigner
    assertOrComplicated (methodDef.Body <> null) "method does not have body"
    assertOrComplicated (not method.HasGenericParameters) "method contains unbound generic parameters"
    let allParameters = Seq.append (if methodDef.IsStatic then [] else [methodDef.Body.ThisParameter]) method.Parameters |> IArray.ofSeq
    softAssert (methodDef.Body.Variables |> Seq.mapi (fun i v -> v.Index = i) |> Seq.forall id) "variable indices don't fit"
    softAssert (allParameters |> Seq.mapi (fun i v -> v.Sequence = i) |> Seq.forall id) "parameter indices don't fit"
    softAssert (args |> Seq.zip methodref.ParameterTypes |> Seq.forall (fun (t, a) -> a.ResultType = t)) <| sprintf "Method argument mismatch %O <- %A" methodref (args |> Seq.map (fun a -> a.ResultType) |> Seq.toArray)

    let frameInfo = { InterpreterFrameInfo.Method = methodref; Args = args; FrameToken = obj(); CurrentInstruction = null; BranchingFactor = 1 }

    // printfn "Interpreting Core %O" methodref
    // method.Body.Instructions |> Seq.iter (printfn "\t%O")

    try
        IO.Directory.CreateDirectory "dasm" |> ignore
        IO.File.WriteAllLines("dasm/" + methodDef.FullName.Replace("/", "_") + ".il", methodDef.Body.Instructions |> Seq.map (sprintf "\t%O"))
    with _ -> ()

    let tryStarts = methodDef.Body.ExceptionHandlers |> Seq.map (fun h -> h.TryStart) |> Collections.Generic.HashSet

    let locals = methodDef.Body.Variables
                 |> IArray.ofSeq
                 |> IArray.map (fun var -> SParameter.New (TypeRef (var.VariableType.ResolvePreserve genericAssigner)) (sprintf "%s_loc%d" method.Name var.Index))
    let parameters = allParameters
                     |> IArray.map (fun var -> SParameter.New (TypeRef (var.ParameterType.ResolvePreserve genericAssigner)) (sprintf "%s_param%d" method.Name var.Index))
    let state = (initLocals locals) state
    let state = { state with Locals = state.Locals.AddRange(Seq.map2 (fun p a -> KeyValuePair(p, a)) parameters args) }

    let rec interpretBlock prefixes (i: Cil.Instruction) state =
        if i.OpCode = OpCodes.Constrained then
            interpretBlock { prefixes with Constained = Some ((i.Operand :?> TypeReference).ResolvePreserve(genericAssigner) |> TypeRef) } i.Next state
        elif i.OpCode = OpCodes.No then
            interpretBlock { prefixes with NoCheck = true } i.Next state
        elif i.OpCode = OpCodes.Readonly then
            interpretBlock { prefixes with ReadOnly = true } i.Next state
        elif i.OpCode = OpCodes.Tail then
            interpretBlock { prefixes with Tail = true } i.Next state
        elif i.OpCode = OpCodes.Unaligned then
            interpretBlock { prefixes with Unaligned = true } i.Next state
        elif i.OpCode = OpCodes.Volatile then
            interpretBlock { prefixes with Volatile = true } i.Next state
        else
            match interpretInstruction genericAssigner (i, prefixes) (locals, parameters) state with
            | InterpretationResult.NewState state ->
                if tryStarts.Contains i.Next then
                    InterpretationResult.Branching [ { InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.ExceptionHandlerEntry i.Next } ]
                else interpretBlock noPrefixes i.Next state
            | a -> a
    let mutable branchCount = 0
    let rec interpretFrom i state cycleDetection =
        let blockResult = interpretBlock noPrefixes i state
        match blockResult with
        | InterpretationResult.NewState _ -> assert false; failwith "wtf"
        | InterpretationResult.Return newState ->
            softAssert (LanguagePrimitives.PhysicalEquality newState.Parent state.Parent) "Can't change parent by interpreting"
            Task.FromResult (newState, NextMethod)
        | InterpretationResult.ExitExceptionHandler (newState, target) ->
            softAssert (LanguagePrimitives.PhysicalEquality newState.Parent state.Parent) "Can't change parent by interpreting an exception handler"
            Task.FromResult (newState, LeaveExceptionHandler target)
        | InterpretationResult.Branching todoItems ->
            let cycleDetection =
                if todoItems.Length > 1 then
                    assertOrComplicated (not <| List.contains i.Offset cycleDetection) (sprintf "Method contains unbounded cycle in block %O" i)
                    i.Offset :: cycleDetection
                else cycleDetection
            branchCount <- branchCount + 1
            assertOrComplicated (branchCount <= 100) (sprintf "Method branch limit reached")
            if todoItems.Length = 1 then
                softAssert (todoItems.Head.State.Parent = state.Parent) "Can't fork state to only one branch"
            else
                softAssert (todoItems |> List.forall (fun t -> t.State.Parent.IsSome)) "All state forks need to have a parent"
                softAssert (todoItems |> List.forall (fun t -> t.State.Parent.Value.Parent = state.Parent)) "All state forks need to be granchild of current parent"
            // printfn "Branching in %O:" method
            let todoFunctions =
                todoItems
                |> IArray.ofSeq
                |> IArray.map (fun t ->
                    match t.Target with
                    | InterpreterTodoTarget.CurrentMethod i ->
                        // printfn "Jumping to '%O', with condition %A" i (List.ofSeq t.State.Conditions |> List.map ExprFormat.exprToString)
                        fun () -> interpretFrom i t.State cycleDetection
                    | InterpreterTodoTarget.CallMethod (m, args, returnI, virt) ->
                        let state = t.State
                        let savedStack = state.Stack
                        let state = { state with Stack = [] }
                        let recurse = if virt then interpretVirtualMethod else interpretMethod
                        let args = IArray.ofSeq (Seq.map2 stackConvert args m.ParameterTypes) |> IArray.map (ExprSimplifier.simplify state.Assumptions)
                        fun () -> task {
                            let! resultState = recurse m state args dispatchFrame
                            softAssert (LanguagePrimitives.PhysicalEquality resultState.Parent state.Parent) "Can't change parent by interpreting"
                            let resultState = { resultState with Stack = List.append resultState.Stack savedStack }
                            match returnI with
                            | Some returnI -> return! interpretFrom returnI resultState cycleDetection
                            | None -> return (resultState, NextMethod)
                        }
                    | InterpreterTodoTarget.ExceptionHandlerEntry i ->
                        let handlers = methodDef.Body.ExceptionHandlers |> Seq.filter (fun h -> h.TryStart = i)
                        printfn "Doing some exception handler at %O" methodref
                        assertOrComplicated (handlers |> Seq.forall (fun h -> h.HandlerType = ExceptionHandlerType.Finally)) "Encountered handler other that finally"
                        softAssert t.State.Stack.IsEmpty "Stack has to be empty when exception handler block starts"
                        let initState = t.State.WithCondition []
                        initState.AssertSomeInvariants() |> ignore
                        let unwindToParent state =
                            let tState = state.Parent.Value
                            softAssert (tState = t.State) "Parent is wrong"
                            softAssert (tState.Conditions.IsEmpty) "Parent is wrong"
                            { tState with
                                     Assumptions = state.Assumptions
                                     ChangedHeapObjects = List.append state.ChangedHeapObjects tState.ChangedHeapObjects
                                     Locals = state.Locals
                                     SideEffects = tState.SideEffects.AddRange state.SideEffects
                                     Stack = state.Stack
                                      }
                        fun () -> task {
                            let! (tryState, LeaveExceptionHandler (Some tryTarget)) = interpretFrom i initState cycleDetection
                            softAssert tryState.Stack.IsEmpty "Stack has to be empty when try block ends"
                            let touchedLocals = initState.Locals
                                                |> Seq.filter (fun l -> not <| LanguagePrimitives.PhysicalEquality tryState.Locals.[l.Key] l.Value)
                            let touchedObjectFields = initState.ChangedHeapObjects
                                                      |> Seq.choose (fun o ->
                                                            match (initState.Assumptions.Heap.TryGet o, tryState.Assumptions.Heap.TryGet o) with
                                                            | (Some a, Some b) -> a.Fields
                                                                                  |> Seq.filter (fun (KeyValue(f, value)) -> not <| LanguagePrimitives.PhysicalEquality value (b.Fields.GetValueOrDefault f))
                                                                                  |> Seq.map (fun (KeyValue(f, _)) -> f)
                                                                                  |> fun a -> Some (o, a)
                                                            | _ -> None
                                                      )
                            let handlerStartingState =
                                let changedObjects = touchedObjectFields |> Seq.map (fun (o,fields) ->
                                    let object = initState.Assumptions.Heap.[o]
                                    o, { object with Fields = object.Fields.SetItems(fields |> Seq.map (fun f -> KeyValuePair(f, SExpr.Undecidable f.FieldType))) })
                                { initState with Locals = initState.Locals.SetItems(touchedLocals |> Seq.map (fun (KeyValue(k, _)) -> KeyValuePair(k, SExpr.Undecidable k.Type)))
                                                 Assumptions = { initState.Assumptions with Heap = initState.Assumptions.Heap.SetItems (changedObjects |> Seq.map KeyValuePair) } }.AssertSomeInvariants()
                            let handler = Seq.exactlyOne handlers // TODO: how multiple handlers starting at the same position work?
                            let isTryExceptionSafe =
                                // if the try block does not contain any sode-effect we are allowed to reorder everything out of the try block anyway
                                tryState.SideEffects.IsEmpty
                            if isTryExceptionSafe then
                                return! interpretFrom tryTarget (unwindToParent tryState) cycleDetection // ignore the finally block altogether and continue
                            else

                            let! (handlerState, LeaveExceptionHandler None) = interpretFrom handler.HandlerStart handlerStartingState cycleDetection

                            let isHandlerEmpty =
                                // I'm not interested in changes of local variables, since they could only be observed from other exception handlers, but they are undecidable here anyway
                                handlerState.SideEffects.IsEmpty &&
                                handlerState.ChangedHeapObjects |> Seq.forall (fun o -> initState.Assumptions.Heap.ContainsKey o |> not)
                            if isHandlerEmpty then
                                // simply execute the finally handler after the try-block (it may still change locals)
                                let! (afterHandler, LeaveExceptionHandler None) = interpretFrom handler.HandlerStart tryState cycleDetection
                                softAssert afterHandler.Stack.IsEmpty "Stack has to be empty when finally block ends"
                                afterHandler.AssertSomeInvariants() |> ignore
                                return! interpretFrom handler.HandlerEnd (unwindToParent afterHandler) cycleDetection
                            else

                            let clearedHandlerState =
                                let safeLocals = touchedLocals |> Seq.filter (fun (KeyValue (l, _)) -> LanguagePrimitives.PhysicalEquality (handlerStartingState.Locals.[l]) (handlerState.Locals.[l]))
                                let safeObjFields =
                                    touchedObjectFields |> Seq.map (fun (o, fields) ->
                                        let (oa, ob) = handlerStartingState.Assumptions.Heap.[o], handlerState.Assumptions.Heap.[o]
                                        o, (fields |> Seq.filter (fun f -> LanguagePrimitives.PhysicalEquality (oa.Fields.GetValueOrDefault f) (ob.Fields.GetValueOrDefault f)))
                                    )
                                let revertedObjects = safeObjFields |> Seq.map (fun (o,fields) ->
                                    let object = handlerState.Assumptions.Heap.[o]
                                    o, { object with Fields = object.Fields.SetItems(fields |> Seq.map (fun f -> KeyValuePair(f, initState.Assumptions.Heap.[o].Fields.[f]))) })

                                { handlerState with Locals = handlerState.Locals.SetItems(safeLocals |> Seq.map (fun (KeyValue(k, _)) -> KeyValuePair(k, initState.Locals.[k])))
                                                    Assumptions = { handlerState.Assumptions with Heap = handlerState.Assumptions.Heap.SetItems (revertedObjects |> Seq.map KeyValuePair) } }
                            return failwithf "NIE" // TODO: introduce a try-finally side-effect
                        }

                )
            runAndMerge todoFunctions (dispatchFrame [ { frameInfo with CurrentInstruction = i; BranchingFactor = todoFunctions.Length } ])

    let instructions = methodDef.Body.Instructions

    // printfn "interpreting method %s" (method.FullName)
    // instructions |> Seq.iter (printfn "\t%O")

    // a little hack for try block starting at the first instruction
    // traditionally the interpretFrom is not triggered by the try block when it starts at the first instruction, so that it can be invoked when the block is starting
    let startNopInstruction = Cil.Instruction.Create(OpCodes.Nop)
    startNopInstruction.Next <- instructions.[0]

    interpretFrom startNopInstruction state [] |> takeInterpretationReturnState

/// Cache of functions executed in full generality (from empty execution state and general parameters)
and private intCache : ConcurrentDictionary<MethodRef, Task<ExecutionCacheEntry>> = ConcurrentDictionary()
and private intAntiCycler : ConcurrentDictionary<MethodRef, bool> = ConcurrentDictionary()

and private getPreinterpretedMethod (method: MethodRef) =
    if intAntiCycler.TryAdd(method, true) then
        intCache.GetOrAdd(method, fun method -> task {
            return ({ ExecutionCacheEntry.ArgParameters = array<_>.Empty; DefiniteStates = array<_>.Empty })
        })
    else
        Task.FromResult({ ExecutionCacheEntry.ArgParameters = array<_>.Empty; DefiniteStates = array<_>.Empty })

and interpretMethod (method: MethodRef) (state: ExecutionState) (args: seq<SExpr>) (dispatcher: InterpreterFrameDispatcher) =
    let args = IArray.ofSeq args
    let nestedDispatcher = fun f -> dispatcher ({ InterpreterFrameInfo.FrameToken = obj(); Method = method; Args = args; BranchingFactor = 1; CurrentInstruction = null } :: f)
    softAssert (state.Stack.IsEmpty) "Stack needs to be empty"
    let resultAsserts result =
        // check that the method does not introduce new undecidables into the system
        if args |> Seq.forall (fun a -> not a.IsUndecidable) then
            assertOrComplicated (result.Stack |> List.forall (fun e -> match e.Node with SExprNode.InstructionCall (InstructionFunction.Undecidable, _, _) -> false | _ -> true)) "Method returns undecidable value"
        softAssert (System.Object.ReferenceEquals(result.Parent, state.Parent)) "State parent needs to be the same"
        if method.ReturnType.FullName = "System.Void" then
            softAssert (result.Stack.Length = 0) <| sprintf "%O - void method returns %d vals." method result.Stack.Length
        else
            softAssert (result.Stack.Length = 1) <| sprintf "%O - method returns %d vals." method result.Stack.Length
    task {
        // let! preinterpreted = getPreinterpretedMethod method

        try
            // printfn "Interpreting %O" method
            let! result = interpretMethodCore method state (IArray.ofSeq args) nestedDispatcher
            resultAsserts result
            return result
        with
          | FunctionTooComplicatedException msg ->
            // function is too complicated => it's a side effect

            printfn "Function %O is too complicated - %s" method msg

            let result = addCallSideEffect method (getMethodSideEffectInfo method) args (*virt*)false state
            resultAsserts result
            return result
          | otherException ->
            raise (new Exception(sprintf "Error occured during execution of %O" method, otherException))

            return state // dummy

    }
and interpretVirtualMethod method state args dispatcher =
    let devirtTargets = devirtualize method args state
    let states = ResizeArray()
    let jobs =
        devirtTargets
        |> List.map (fun (condition, method, isVirtual) ->
            let castTarget expr =
                let expr = SExpr.Cast InstructionFunction.Cast method.DeclaringType expr |> ExprSimplifier.simplify state.Assumptions
                if method.DeclaringType.Reference.IsValueType then
                    StateProcessing.makeReference expr
                else expr
            let forkedState = if condition = SExpr.ImmConstant true then state
                              else state.WithCondition [condition]
            states.Add forkedState
            let args = args.SetItem(0, castTarget args.[0])
            if isVirtual then
                // not devirtualizable -> side effect
                fun () -> (addCallSideEffect method (getMethodSideEffectInfo method) args (*virt*)true forkedState, NextMethod) |> Task.FromResult
            else
                fun () -> (task { let! r = interpretMethod method forkedState args dispatcher in return r, NextMethod })
        )
    if states.Count = 1 then softAssert (LanguagePrimitives.PhysicalEquality states.[0].Parent state.Parent) "One forked state can't have a different parent"
    else
        softAssert (states |> Seq.forall (fun s -> s.Parent.IsSome)) "Forked states must have a parent"
        softAssert (states |> Seq.forall (fun s -> LanguagePrimitives.PhysicalEquality s.Parent.Value.Parent state.Parent)) "Forked states must be grandchildren of current parent"
    runAndMerge jobs (dispatcher [ { InterpreterFrameInfo.FrameToken = obj(); Method = method; Args = args; BranchingFactor = devirtTargets.Length; CurrentInstruction = null } ]) |> takeInterpretationReturnState


let createDispatcher logger : InterpreterFrameDispatcher =
    fun frameInfo fn ->
        logger frameInfo
        Task.Run<ExecutionState * InterpreterReturnType>(fun () -> fn ())

let createSynchronousDispatcher logger : InterpreterFrameDispatcher =
    fun frameInfo fn ->
        logger frameInfo
        fn ()