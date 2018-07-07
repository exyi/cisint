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


type InterpreterFrameDispatcher = (MethodDefinition * SExpr array) clist -> (unit -> Task<ExecutionState>) -> Task<ExecutionState>

type ExecutionCacheEntry = {
    ArgParameters: SParameter array
    /// condition -> state; the condition may contain some references to the resulting execution state (i.e. be dependent on some side effect result), but the system should try to reduce these
    DefiniteStates: (SExpr * ExecutionState) array
}

type InstructionPrefixes = {
    Constained: TypeReference option
    NoCheck: bool
    ReadOnly: bool
    Tail: bool
    Unaligned: bool
    Volatile: bool
}

let noPrefixes = { Constained = None; InstructionPrefixes.NoCheck = false; ReadOnly = false; Tail = false; Unaligned = false; Volatile = true }

let stackLoadConvert (expr: SExpr) =
    let t = expr.ResultType
    if not t.Reference.IsValueType then
        expr
    elif not t.IsPrimitive then
        failwith "Can't load non-primitive value to CIL stack."
    elif t.FullName = typeof<int>.FullName || t.FullName = typeof<int64>.FullName || t.FullName = typeof<float>.FullName then
        expr
    elif t.FullName = typeof<uint64>.FullName then
        SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType typeof<int64>) [ expr ]
    elif t.FullName = typeof<System.Single>.FullName then
        SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType typeof<float>) [ expr ]
    elif t.FullName = typeof<bool>.FullName ||
            t.FullName = typeof<char>.FullName ||
            t.FullName = typeof<int8>.FullName ||
            t.FullName = typeof<uint8>.FullName ||
            t.FullName = typeof<int16>.FullName ||
            t.FullName = typeof<uint16>.FullName ||
            t.FullName = typeof<uint32>.FullName then
        SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType typeof<int32>) [ expr ]
    else
        failwithf "unsupported stack load conversion from '%O'." expr.ResultType

let stackArithmeticCoerce a b =
    if a.ResultType = b.ResultType then
        (a, b)
    else
        waitForDebug ()
        failwithf "coertion %O <-> %O not supported (expressions %s, %s)" a.ResultType b.ResultType (ExprFormat.exprToString a) (ExprFormat.exprToString b)

let stackConvertToUnsigned (a: SExpr) =
    if a.ResultType.FullName = typeof<int32>.FullName then
        SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType typeof<uint32>) [a]
    elif a.ResultType.FullName = typeof<int64>.FullName then
        SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType typeof<uint64>) [a]
    elif a.ResultType.FullName = typeof<float>.FullName then
        a // TODO: float.NaN glitches :(
    else
        failwithf "Coertion to unsigned '%O' not .supported" a.ResultType

let rec interpretInstruction ((instr, prefixes): Cil.Instruction * InstructionPrefixes) ((locals, arguments): (SParameter array) * (SParameter array)) (state: ExecutionState) =
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
        procArit (fun a b -> SExpr.InstructionCall fn a.ResultType [preproc a;preproc b])

    let convert t preprocess =
        proc1stack (fun a -> SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType t) [preprocess a] |> stackLoadConvert)
    let convertChecked t preprocess =
        proc1stack (fun a -> SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType t) [preprocess a] |> stackLoadConvert)

    let doBranch (stack: SExpr clist) condition =
        let state = { state with Stack = stack }
        let cSimpl = SExpr.InstructionCall InstructionFunction.Convert (CecilTools.boolType) [ condition ] |> ExprSimplifier.simplify state.Assumptions
        if condition.Node = SExprNode.Constant true then
            InterpretationResult.Branching [{ InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.CurrentMethod (instr.Operand :?> Cil.Instruction, false) }]
        elif condition.Node = SExprNode.Constant false then
            InterpretationResult.NewState state
        else
            InterpretationResult.Branching [
                { InterpreterTodoItem.State = state.WithCondition [ cSimpl ]; Target = InterpreterTodoTarget.CurrentMethod (unbox instr.Operand, false) }
                { InterpreterTodoItem.State = state.WithCondition [ SExpr.BoolNot cSimpl ]; Target = InterpreterTodoTarget.CurrentMethod (instr.Next, false) }
            ]
    let doBranchWithCond opcode i2 =
        let state2 = match interpretInstruction (i2, noPrefixes) (locals, arguments) state with InterpretationResult.NewState s -> s | _ -> failwith "wtf"
        let bInst = Cil.Instruction.Create(opcode, instr.Operand :?> Cil.Instruction)
        bInst.Next <- instr.Next; bInst.Offset <- instr.Offset;
        interpretInstruction (bInst, prefixes) (locals, arguments) state2

    let getLocal p =
        pushToStack (state.Locals.[p])
    let setLocal p =
        match state.Stack with
        | a :: rest ->
            InterpretationResult.NewState { state with Stack = rest; Locals = state.Locals.SetItem(p, a) }
        | _ -> failwithf "Can't pop a value from stack at %O" instr

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

    elif op = OpCodes.Ceq then procArit (fun a b -> SExpr.InstructionCall InstructionFunction.Convert CecilTools.intType [SExpr.InstructionCall InstructionFunction.C_Eq CecilTools.boolType [a;b]])
    elif op = OpCodes.Cgt then procArit (fun a b -> SExpr.InstructionCall InstructionFunction.Convert CecilTools.intType [SExpr.InstructionCall InstructionFunction.C_Gt CecilTools.boolType [a;b]])
    elif op = OpCodes.Cgt_Un then procArit (fun a b -> SExpr.InstructionCall InstructionFunction.Convert CecilTools.intType [SExpr.InstructionCall InstructionFunction.C_Gt CecilTools.boolType [stackConvertToUnsigned a;stackConvertToUnsigned b]])
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

    elif op = OpCodes.Conv_Ovf_I then convertChecked typeof<int8> id
    elif op = OpCodes.Conv_Ovf_U1 then convertChecked typeof<uint8> id
    elif op = OpCodes.Conv_Ovf_I2 then convertChecked typeof<int16> id
    elif op = OpCodes.Conv_Ovf_U2 then convertChecked typeof<uint16> id
    elif op = OpCodes.Conv_Ovf_I4 then convertChecked typeof<int32> id
    elif op = OpCodes.Conv_Ovf_U4 then convertChecked typeof<uint32> id
    elif op = OpCodes.Conv_Ovf_I8 then convertChecked typeof<int64> id
    elif op = OpCodes.Conv_Ovf_U8 then convertChecked typeof<uint64> id

    elif op = OpCodes.Conv_Ovf_I_Un then convertChecked typeof<int8> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_U1_Un then convertChecked typeof<uint8> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_I2_Un then convertChecked typeof<int16> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_U2_Un then convertChecked typeof<uint16> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_I4_Un then convertChecked typeof<int32> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_U4_Un then convertChecked typeof<uint32> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_I8_Un then convertChecked typeof<int64> stackConvertToUnsigned
    elif op = OpCodes.Conv_Ovf_U8_Un then convertChecked typeof<uint64> stackConvertToUnsigned

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
    elif op = OpCodes.Ldc_I4_M1 then pushToStack (SExpr.ImmConstant -1)
    elif op = OpCodes.Ldc_I4 || op = OpCodes.Ldc_I4_S then pushToStack (SExpr.ImmConstant (instr.Operand :?> int))
    elif op = OpCodes.Ldc_I8 then pushToStack (SExpr.ImmConstant (instr.Operand :?> int64))
    elif op = OpCodes.Ldc_R8 then pushToStack (SExpr.ImmConstant (instr.Operand :?> Double))
    elif op = OpCodes.Ldc_R4 then pushToStack (SExpr.ImmConstant (float (instr.Operand :?> Single)))
    elif op = OpCodes.Ldnull then pushToStack (SExpr.ImmConstant (box null))

    elif op = OpCodes.Ret then InterpretationResult.Return state

    elif op = OpCodes.Br || op = OpCodes.Br_S then doBranch state.Stack (SExpr.ImmConstant true)

    elif op = OpCodes.Brtrue || op = OpCodes.Brtrue_S then
        match state.Stack with
        | condition :: stack -> doBranch stack condition
        | _ -> failwithf "Nothing on stack at %O" instr

    elif op = OpCodes.Brfalse || op = OpCodes.Brfalse then
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

    elif op = OpCodes.Call || op = OpCodes.Callvirt then
        let method = instr.Operand :?> MethodReference
        let returnI = if prefixes.Tail then None; else Some instr.Next
        InterpretationResult.Branching [ { InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.CallMethod (MethodRef(method), returnI, op = OpCodes.Callvirt) } ]

    elif op = OpCodes.Ldarg || op = OpCodes.Ldarg_S then getLocal (arguments.[instr.Operand :?> int])
    elif op = OpCodes.Ldarg_0 then getLocal (arguments.[0])
    elif op = OpCodes.Ldarg_1 then getLocal (arguments.[1])
    elif op = OpCodes.Ldarg_2 then getLocal (arguments.[2])
    elif op = OpCodes.Ldarg_3 then getLocal (arguments.[3])
    elif op = OpCodes.Ldloc || op = OpCodes.Ldloc_S then getLocal (locals.[instr.Operand :?> int])
    elif op = OpCodes.Ldloc_0 then getLocal (locals.[0])
    elif op = OpCodes.Ldloc_1 then getLocal (locals.[1])
    elif op = OpCodes.Ldloc_2 then getLocal (locals.[2])
    elif op = OpCodes.Ldloc_3 then getLocal (locals.[3])

    elif op = OpCodes.Starg || op = OpCodes.Starg_S then setLocal (arguments.[instr.Operand :?> int])
    elif op = OpCodes.Stloc || op = OpCodes.Stloc_S then setLocal (locals.[instr.Operand :?> int])
    elif op = OpCodes.Stloc_0 then setLocal (locals.[0])
    elif op = OpCodes.Stloc_1 then setLocal (locals.[1])
    elif op = OpCodes.Stloc_2 then setLocal (locals.[2])
    elif op = OpCodes.Stloc_3 then setLocal (locals.[3])

    else failwithf "unsupported instruction %O" instr

let mutable private valueTypeCounter = 0L
let mutable private sideEffectCounter = 0L

let rec createDefaultValue (t: TypeRef) =
    if t.IsPrimitive then
        // just take default value
        SExpr.New t (SExprNode.Constant (Activator.CreateInstance (Type.GetType t.FullName))), Seq.empty
    elif t.Reference.IsValueType then
        // create default object for value type
        let obj1, moreObjs = initHeapObject t true
        let param = SParameter.New t (sprintf "v%d" (Threading.Interlocked.Increment(&valueTypeCounter)))
        SExpr.Parameter param, Seq.append [ param, obj1 ] moreObjs
    else
        // reference types default to null
        SExpr.New t (SExprNode.Constant null), Seq.empty

and initHeapObject (t: TypeRef) definiteType =
    let fieldsWithObjects =
        t.Definition.Fields
        |> Seq.map FieldRef
        |> Seq.map (fun f ->
            assert(f.FieldType <> t)
            let value, heapObjects = createDefaultValue f.FieldType
            KeyValuePair(f, value), heapObjects
        )
    { HeapObject.Type = t
      TypeIsDefinite = definiteType
      IsShared = SExpr.ImmConstant false
      Fields = Seq.map fst fieldsWithObjects |> ImmutableDictionary.CreateRange
    }, Seq.collect snd fieldsWithObjects

let initLocals (p: #seq<SParameter>) (state: ExecutionState) =
    let m = p
             |> Seq.map (fun p ->
                    let obj1, moreObj = createDefaultValue p.Type
                    KeyValuePair(p, obj1), moreObj
                )
    let state = state.AddObject (Seq.collect snd m)
    { state with Locals = state.Locals.AddRange(Seq.map fst m) }

let mergeStates a b =
    assert (a.Parent = b.Parent)
    assert (a.Parent.IsSome)
    let parent = a.Parent.Value
    let condition = a.Conditions |> Seq.reduce (fun a b -> SExpr.InstructionCall InstructionFunction.And CecilTools.boolType [a; b])
    // let conditions_b = b.Conditions
    let changedObjects =
        Seq.append a.ChangedHeapObjects b.ChangedHeapObjects |> Seq.distinct |> Seq.map (fun op ->
            match (a.Assumptions.Heap.TryGetValue op, b.Assumptions.Heap.TryGetValue op) with
            | ((true, obj_a), (true, obj_b)) ->
                assert (obj_a.Type = obj_b.Type) // TODO: type changes
                let combined =
                    { HeapObject.Type = obj_a.Type
                      TypeIsDefinite = obj_a.TypeIsDefinite && obj_b.TypeIsDefinite
                      IsShared = if obj_a.IsShared = obj_b.IsShared then obj_a.IsShared
                                 else SExpr.Condition condition obj_a.IsShared obj_b.IsShared |> ExprSimplifier.simplify AssumptionSet.empty
                      Fields =
                        obj_a.Fields.SetItems(obj_a.Fields |> Seq.map (fun (KeyValue(f, p_a)) ->
                            let p_b = obj_b.Fields.[f]
                            if p_b = p_a then KeyValuePair(f, p_a)
                            else KeyValuePair(f, SExpr.Condition condition p_a p_b |> ExprSimplifier.simplify AssumptionSet.empty)
                        ))
                    }
                op, combined
            | ((true, o), _) | (_, (true, o)) ->
                op, o
            | _ -> waitForDebug (); failwithf "wtf, %s was in the changed objects but not on heap." op.Name
        ) |> IArray.ofSeq

    let locals =
        parent.Locals.SetItems (
            parent.Locals
            |> Seq.choose (fun (KeyValue(loc, value)) ->
                let v_a = a.Locals.[loc]
                let v_b = b.Locals.[loc]
                if System.Object.ReferenceEquals(v_a, v_b) || v_a = v_b then
                    if System.Object.ReferenceEquals(v_a, value) || v_a = value then None else Some(KeyValuePair(loc, v_a))
                else
                    Some(KeyValuePair(loc, SExpr.Condition condition v_a v_b |> ExprSimplifier.simplify AssumptionSet.empty))
            ))

    assert (a.Stack.Length = b.Stack.Length)
    let stack =
        List.map2 (fun a b ->
            if a = b then a
            else SExpr.Condition condition a b |> ExprSimplifier.simplify AssumptionSet.empty)
            a.Stack b.Stack

    let sideEffects =
        let commonEffects =
            Seq.zip (Seq.rev a.SideEffects) (Seq.rev b.SideEffects)
            |> Seq.takeWhile (fun (a, b) -> a = b)
            |> Seq.map fst
            |> Seq.toArray
        let aEffects = Seq.take (a.SideEffects.Count - commonEffects.Length) (a.SideEffects) |> IArray.ofSeq
        let bEffects = Seq.take (b.SideEffects.Count - commonEffects.Length) (b.SideEffects) |> IArray.ofSeq
        seq {
            if aEffects.Length > 0 then
                yield (condition, SideEffect.Effects aEffects)
            if bEffects.Length > 0 then
                yield (SExpr.BoolNot condition |> ExprSimplifier.simplify AssumptionSet.empty, SideEffect.Effects bEffects)
            yield! commonEffects
        }

    { parent with
        ChangedHeapObjects = Seq.map fst changedObjects |> List.ofSeq
        Assumptions = AssumptionSet.addObj changedObjects parent.Assumptions
        Stack = stack
        Locals = locals
        SideEffects = parent.SideEffects.AddRange(sideEffects)
    }


let interpretMethodCore (methodref: MethodRef) (state: ExecutionState) (args: SExpr array) (dispatchFrame: InterpreterFrameDispatcher) =
    let method = methodref.Definition
    assert (method.Body.Variables |> Seq.mapi (fun i v -> v.Index = i) |> Seq.forall id)
    let locals = method.Body.Variables
                 |> Seq.map (fun var -> SParameter.New (TypeRef var.VariableType) (sprintf "%s_loc%d" method.Name var.Index))
                 |> IArray.ofSeq
    let parameters = Seq.append (if method.IsStatic then [] else [method.Body.ThisParameter]) method.Parameters
                     |> Seq.map (fun var -> SParameter.New (TypeRef var.ParameterType) (sprintf "%s_loc%d" method.Name var.Index))
                     |> IArray.ofSeq
    let state = (initLocals locals) state
    let state = { state with Locals = state.Locals.AddRange(Seq.map2 (fun p a -> KeyValuePair(p, a)) parameters args) }

    let rec interpretBlock prefixes (i: Cil.Instruction) state =
        if i.OpCode = OpCodes.Constrained then
            interpretBlock { prefixes with Constained = Some (i.Operand :?> TypeReference) } i.Next state
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
            match interpretInstruction (i, prefixes) (locals, parameters) state with
            | InterpretationResult.NewState state ->
                interpretBlock noPrefixes i.Next state
            | a -> a

    let rec interpretFrom i state =
        let blockResult = interpretBlock noPrefixes i state
        match blockResult with
        | InterpretationResult.NewState _ -> assert false; failwith "wtf"
        | InterpretationResult.Return state -> Task.FromResult state
        | InterpretationResult.Branching todoItems ->
            let todoFunctions = todoItems |> Seq.map (fun t () ->
                match t.Target with
                | InterpreterTodoTarget.CurrentMethod (i, leave) ->
                    assert (not leave) //TODO exceptions
                    // printfn "Jumping to '%O', with condition %A" i (List.ofSeq t.State.Conditions |> List.map ExprFormat.exprToString)
                    interpretFrom i t.State
                | InterpreterTodoTarget.CallMethod (m, returnI, virt) ->
                    let result = SParameter.New m.ReturnType (sprintf "se%d" (Threading.Interlocked.Increment(&sideEffectCounter)))
                    let argCount = if m.Reference.HasThis then 1 + m.Reference.Parameters.Count else m.Reference.Parameters.Count
                    let args = t.State.Stack |> Seq.take argCount |> Seq.rev |> IArray.ofSeq
                    // TODO: mark everything reachable as shared
                    let effect = SideEffect.MethodCall (m, result, args, virt, true)
                    let state = { t.State with Stack = List.skip argCount t.State.Stack }
                    let state = { state with SideEffects = state.SideEffects.Add(SExpr.ImmConstant true, effect) }
                    let state =
                        if m.ReturnType.FullName = "System.Void" then state
                        else
                            let state = state.AddObject [ result, { HeapObject.Type = m.ReturnType; TypeIsDefinite = m.ReturnType.Definition.IsSealed; Fields = dict<_, _>.Empty; IsShared = SExpr.ImmConstant true } ]
                            { state with Stack = SExpr.Parameter result :: state.Stack }
                    match returnI with
                    | Some returnI -> interpretFrom returnI state
                    | None -> Task.FromResult(state)
            )
            let result :Task<ExecutionState []> = Task.WhenAll<ExecutionState>(todoFunctions |> Seq.map (dispatchFrame [ method, args ]))

            task {
                let! r = result
                return match r with
                       | [| x |] -> x
                       | [| x; y |] -> mergeStates x y
                       | _ -> failwithf "NIE: merge %d states" r.Length
                // TODO: merge more than two states
            }

    let instructions = method.Body.Instructions

    // printfn "interpreting method %s" (method.FullName)
    // instructions |> Seq.iter (printfn "\t%O")

    interpretFrom instructions.[0] state


/// Cache of functions executed in full generality (from empty execution state and general parameters)
let private intCache : ConcurrentDictionary<MethodRef, Task<ExecutionCacheEntry>> = ConcurrentDictionary()
let private intAntiCycler : ConcurrentDictionary<MethodRef, bool> = ConcurrentDictionary()

let private getPreinterpretedMethod (method: MethodRef) =
    if intAntiCycler.TryAdd(method, true) then
        intCache.GetOrAdd(method, fun method -> task {
            return ({ ExecutionCacheEntry.ArgParameters = array<_>.Empty; DefiniteStates = array<_>.Empty })
        })
    else
        Task.FromResult({ ExecutionCacheEntry.ArgParameters = array<_>.Empty; DefiniteStates = array<_>.Empty })

let interpretMethod (method: MethodRef) (state: ExecutionState) (args: #seq<SExpr>) (dispatcher: InterpreterFrameDispatcher) = task {
    let! preinterpreted = getPreinterpretedMethod method

    let! result = interpretMethodCore method state (IArray.ofSeq args) dispatcher

    assert (System.Object.ReferenceEquals(result.Parent, state.Parent))

    return result
}

let createDispatcher logger : InterpreterFrameDispatcher =
    fun frameInfo fn ->
        logger frameInfo
        Task.Run<ExecutionState>(fun () -> fn ())