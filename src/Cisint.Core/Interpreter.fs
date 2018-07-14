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
open System.Collections.Generic
open StateProcessing
open System.Collections.Generic
open System.Collections.Generic

type InterpreterFrameInfo = {
    FrameToken: obj
    Method: MethodRef
    Args: SExpr array
    BranchingFactor: int
    CurrentInstruction: Mono.Cecil.Cil.Instruction
}

type InterpreterFrameDispatcher = InterpreterFrameInfo clist -> (unit -> Task<ExecutionState>) -> Task<ExecutionState>

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
    if not t.IsPrimitive then
        expr
    elif t.FullName = typeof<int>.FullName || t.FullName = typeof<int64>.FullName || t.FullName = typeof<float>.FullName then
        expr
    elif t.FullName = typeof<uint64>.FullName then
        SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType typeof<int64>) [ expr ]
    elif t.FullName = typeof<System.Single>.FullName then
        SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType typeof<float>) [ expr ]
    elif t.FullName = typeof<bool>.FullName ||
            t.FullName = typeof<char>.FullName ||
            t.FullName = typeof<Byte>.FullName ||
            t.FullName = typeof<SByte>.FullName ||
            t.FullName = typeof<Int16>.FullName ||
            t.FullName = typeof<UInt16>.FullName ||
            t.FullName = typeof<UInt32>.FullName then
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

let private runAndMerge todoFunctions dispatchFrame =
    let result :Task<ExecutionState []> = Task.WhenAll<ExecutionState>(todoFunctions |> Seq.map (dispatchFrame))

    task {
        let! r = result
        return match r with
               | [| x |] -> x
               | [| x; y |] -> mergeStates x y
               | _ -> failwithf "NIE: merge %d states" r.Length
        // TODO: merge more than two states
    }

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
        pushToStack (state.Locals.[p] |> stackLoadConvert)
    let setLocal p =
        match state.Stack with
        | a :: rest ->
            InterpretationResult.NewState { state with Stack = rest; Locals = state.Locals.SetItem(p, a) }
        | _ -> failwithf "Can't pop a value from stack at %O" instr

    let loadIndirect expectedType =
        proc1stack (fun addr ->
            let result = dereference addr state
            if expectedType <> Some result.ResultType && expectedType <> None then failwithf "Can't load dereference to %O, %O was expected" result.ResultType expectedType
            stackLoadConvert result
        )

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
    elif op = OpCodes.Ldc_I4 || op = OpCodes.Ldc_I4_S then pushToStack (SExpr.ImmConstant (instr.Operand |> Convert.ToInt32))
    elif op = OpCodes.Ldc_I8 then pushToStack (SExpr.ImmConstant (instr.Operand :?> int64))
    elif op = OpCodes.Ldc_R8 || op = OpCodes.Ldc_R4 then pushToStack (SExpr.ImmConstant (instr.Operand |> Convert.ToDouble))
    elif op = OpCodes.Ldnull then pushToStack (SExpr.ImmConstant (box null))

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

    elif op = OpCodes.Call || op = OpCodes.Callvirt then
        let method = instr.Operand :?> MethodReference
        let returnI = if prefixes.Tail then None; else Some instr.Next
        if op = OpCodes.Callvirt && prefixes.Constained.IsSome then
            let overridenMethod = findOverridenMethod (TypeRef prefixes.Constained.Value) (MethodRef method)
            if TypeRef.AreSameTypes overridenMethod.Reference.DeclaringType prefixes.Constained.Value then
                // the function is overriden -> invoke it directly
                InterpretationResult.Branching [ { InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.CallMethod (overridenMethod, returnI, false) } ]
            else
                // it's not overriden -> invoke the base implementation with boxing and stuff
                let args = List.take (method.Parameters.Count + 1) state.Stack |> List.rev
                let args = ((SExpr.InstructionCall InstructionFunction.Box CecilTools.objType [ SExpr.Dereference args.Head ]) :: args.Tail) |> List.rev
                let state = { state with Stack = List.append args (List.skip (method.Parameters.Count + 1) state.Stack) }
                InterpretationResult.Branching [ { InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.CallMethod (MethodRef method, returnI, false) } ]
        else
            InterpretationResult.Branching [ { InterpreterTodoItem.State = state; Target = InterpreterTodoTarget.CallMethod (MethodRef method, returnI, op = OpCodes.Callvirt) } ]

    elif op = OpCodes.Ldarg || op = OpCodes.Ldarg_S then getLocal (arguments.[(instr.Operand :?> ParameterDefinition).Index])
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
        pushToStack (SExpr.ParamReference (arguments.[(instr.Operand :?> ParameterDefinition).Index]))

    elif op = OpCodes.Starg || op = OpCodes.Starg_S then setLocal (arguments.[(instr.Operand :?> ParameterDefinition).Index])
    elif op = OpCodes.Stloc || op = OpCodes.Stloc_S then setLocal (locals.[(instr.Operand :?> VariableDefinition).Index])
    elif op = OpCodes.Stloc_0 then setLocal (locals.[0])
    elif op = OpCodes.Stloc_1 then setLocal (locals.[1])
    elif op = OpCodes.Stloc_2 then setLocal (locals.[2])
    elif op = OpCodes.Stloc_3 then setLocal (locals.[3])

    elif op = OpCodes.Ldind_I1 then loadIndirect (Some (CecilTools.convertType typeof<SByte>))
    elif op = OpCodes.Ldind_U1 then loadIndirect (Some (CecilTools.convertType typeof<Byte>))
    elif op = OpCodes.Ldind_I2 then loadIndirect (Some (CecilTools.convertType typeof<Int16>))
    elif op = OpCodes.Ldind_U2 then loadIndirect (Some (CecilTools.convertType typeof<UInt16>))
    elif op = OpCodes.Ldind_I4 then loadIndirect (Some (CecilTools.convertType typeof<Int32>))
    elif op = OpCodes.Ldind_U4 then loadIndirect (Some (CecilTools.convertType typeof<UInt32>))
    elif op = OpCodes.Ldind_I8 then loadIndirect (None) // it can load uint64 using this instruction too
    elif op = OpCodes.Ldind_R4 then loadIndirect (Some (CecilTools.convertType typeof<Single>))
    elif op = OpCodes.Ldind_R8 then loadIndirect (Some (CecilTools.convertType typeof<float>))
    elif op = OpCodes.Ldind_Ref then loadIndirect None // may load any reference type

    else tooComplicated <| sprintf "unsupported instruction %O" instr

let rec interpretMethodCore (methodref: MethodRef) (state: ExecutionState) (args: SExpr array) (dispatchFrame: InterpreterFrameDispatcher) =
    let method = methodref.Definition
    assertOrComplicated (method.Body <> null) "method does not have body"
    assert (method.Body.Variables |> Seq.mapi (fun i v -> v.Index = i) |> Seq.forall id)

    let frameInfo = { InterpreterFrameInfo.Method = methodref; Args = args; FrameToken = obj(); CurrentInstruction = null; BranchingFactor = 1 }

    printfn "Interpreting Core %O" methodref
    method.Body.Instructions |> Seq.iter (printfn "\t%O")

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
    let rec interpretFrom i state cycleDetection =
        let blockResult = interpretBlock noPrefixes i state
        match blockResult with
        | InterpretationResult.NewState _ -> assert false; failwith "wtf"
        | InterpretationResult.Return state -> Task.FromResult state
        | InterpretationResult.Branching todoItems ->
            let cycleDetection =
                if todoItems.Length > 1 then
                    assertOrComplicated (not <| List.contains i.Offset cycleDetection) (sprintf "Method contains unbounded cycle in block %O" i)
                    i.Offset :: cycleDetection
                else cycleDetection
            let todoFunctions =
                todoItems
                |> Seq.map (fun t () ->
                    match t.Target with
                    | InterpreterTodoTarget.CurrentMethod (i, leave) ->
                        assert (not leave) //TODO exceptions
                        // printfn "Jumping to '%O', with condition %A" i (List.ofSeq t.State.Conditions |> List.map ExprFormat.exprToString)
                        interpretFrom i t.State cycleDetection
                    | InterpreterTodoTarget.CallMethod (m, returnI, virt) ->
                        let argCount = if m.Reference.HasThis then 1 + m.Reference.Parameters.Count else m.Reference.Parameters.Count
                        let args = t.State.Stack |> Seq.take argCount |> Seq.rev |> IArray.ofSeq
                        let state = { t.State with Stack = List.skip argCount t.State.Stack }
                        let savedStack = state.Stack
                        let state = { state with Stack = [] }
                        let recurse = if virt then interpretVirtualMethod else interpretMethod
                        task {
                            let! resultState = recurse m state args dispatchFrame
                            let resultState = { resultState with Stack = List.append resultState.Stack savedStack }
                            match returnI with
                            | Some returnI -> return! interpretFrom returnI resultState cycleDetection
                            | None -> return resultState
                        }
                )
                |> IArray.ofSeq
            runAndMerge todoFunctions (dispatchFrame [ { frameInfo with CurrentInstruction = i; BranchingFactor = todoFunctions.Length } ])

    let instructions = method.Body.Instructions

    // printfn "interpreting method %s" (method.FullName)
    // instructions |> Seq.iter (printfn "\t%O")

    interpretFrom instructions.[0] state []

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
    assert (state.Stack.IsEmpty)
    // waitForDebug()
    task {
        // let! preinterpreted = getPreinterpretedMethod method

        try
            // printfn "Interpreting %O" method
            let! result = interpretMethodCore method state (IArray.ofSeq args) dispatcher
            assert (System.Object.ReferenceEquals(result.Parent, state.Parent))
            if method.ReturnType.FullName = "System.Void" then
                if result.Stack.Length <> 0 then
                    failwithf "%O - void method returns %d vals." method result.Stack.Length
            else
                if result.Stack.Length <> 1 then
                    failwithf "%O - method returns %d vals." method result.Stack.Length
            return result
        with
          | FunctionTooComplicatedException msg ->
            // function is too complicated => it's a side effect

            printfn "Function %O is too complicated - %s" method msg

            let result = addCallSideEffect method (getMethodSideEffectInfo method) args (*virt*)false state
            if method.ReturnType.FullName = "System.Void" then
                if result.Stack.Length <> 0 then
                    failwithf "%O - void method returns %d vals." method result.Stack.Length
            else
                if result.Stack.Length <> 1 then
                    failwithf "%O - method returns %d vals." method result.Stack.Length
            return result
          | otherException ->
            raise (new Exception(sprintf "Error occured during execution of %O" method, otherException))

            return state // dummy

    }
and interpretVirtualMethod method state args dispatcher =
    let devirtTargets = devirtualize method args state
    let jobs =
        devirtTargets
        |> Seq.map (fun (condition, method, isVirtual) ->
            let forkedState = if condition = SExpr.ImmConstant true then state
                              else state.WithCondition [condition]
            if isVirtual then
                // not devirtualizable -> side effect
                fun () -> addCallSideEffect method (getMethodSideEffectInfo method) args (*virt*)true forkedState |> Task.FromResult
            else
                fun () -> interpretMethod method forkedState args dispatcher
        )
    runAndMerge jobs (dispatcher [ { InterpreterFrameInfo.FrameToken = obj(); Method = method; Args = args; BranchingFactor = devirtTargets.Length; CurrentInstruction = null } ])


let createDispatcher logger : InterpreterFrameDispatcher =
    fun frameInfo fn ->
        logger frameInfo
        Task.Run<ExecutionState>(fun () -> fn ())

let createSynchronousDispatcher logger : InterpreterFrameDispatcher =
    fun frameInfo fn ->
        logger frameInfo
        fn ()