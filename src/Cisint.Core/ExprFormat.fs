module ExprFormat
open Expression
open InterpreterState
open System
open TypesystemDefinitions
open System.Collections
open System.Collections.Generic
open StateProcessing

let tabRight (str: string) =
    "\t" + str.Replace("\n", "\n\t")
let joinLines (lines: #seq<string>) = String.Join("\n", lines)

let rec exprToString expr =
    let procLValue =
        function
        | SLExprNode.Parameter p -> sprintf "%s" p.Name
        | SLExprNode.LdField (field, None) -> sprintf "ldsfld<%O>" field
        | SLExprNode.LdField (field, Some target) -> sprintf "%s.%s" (exprToString target) field.Name
        | SLExprNode.LdElement (target, index) -> sprintf "%s.[%s]" (exprToString target) (exprToString index)
        | SLExprNode.Dereference e -> sprintf "*%s" (exprToString e)
    match expr.Node with
    | SExprNode.Constant null -> sprintf "null<%s>" expr.ResultType.Name
    | SExprNode.Constant c ->
        if expr.ResultType.IsPrimitive then
            sprintf "%A" c
        else
            sprintf "c<%O>(%O)" expr.ResultType c
    | SExprNode.LValue l -> procLValue l
    | SExprNode.Reference l -> sprintf "&%s" (procLValue l)
    | SExprNode.PureCall (method, args) ->
        sprintf "%O(%s)" method (String.Join(", ", args.arr |> Seq.map exprToString))
    | SExprNode.InstructionCall (instr, _t, args) when (args.arr.Length = 2) ->
        let (a, b) = args.arr.[0], args.arr.[1]
        let op = match instr with
                    | InstructionFunction.Add -> "+"
                    | InstructionFunction.And -> "&"
                    | InstructionFunction.C_Eq -> "="
                    | InstructionFunction.C_Gt -> ">"
                    | InstructionFunction.C_Lt -> "<"
                    | InstructionFunction.Div -> "/"
                    | InstructionFunction.Mul -> "*"
                    | InstructionFunction.Or -> "|"
                    | InstructionFunction.Rem -> "%"
                    | InstructionFunction.Shr -> ">>"
                    | InstructionFunction.Shl -> "<<"
                    | InstructionFunction.Sub -> "-"
                    | InstructionFunction.Xor -> "^"
                    | InstructionFunction.Not
                    | InstructionFunction.Negate
                    | InstructionFunction.IsInst
                    | InstructionFunction.Convert_Checked
                    | InstructionFunction.Convert
                    | InstructionFunction.Box
                    | InstructionFunction.Unbox
                    | InstructionFunction.Cast -> failwith ""
                    | _ -> failwith ""
        sprintf "(%s %s %s)" (exprToString a) op (exprToString b)
    | SExprNode.InstructionCall (InstructionFunction.Not, _, args) -> sprintf "!%s" (args.arr |> Seq.exactlyOne |> exprToString)
    | SExprNode.InstructionCall (InstructionFunction.Negate, _, args) -> sprintf "-%s" (args.arr |> Seq.exactlyOne |> exprToString)
    | SExprNode.InstructionCall (instr, t, args) ->
        sprintf "%O<%O>(%s)" instr t (String.Join(", ", args.arr |> Seq.map exprToString))
    | SExprNode.Condition (cond, ifTrue, ifFalse) ->
        sprintf "if %s {\n%s\n} else {\n%s\n}" (exprToString cond) (exprToString ifTrue |> tabRight) (exprToString ifFalse |> tabRight)

let rec private csideEffectToString  (printObjectState) ((c, se): ConditionalEffect) =
    if c = SExpr.ImmConstant true then
        sideEffectToString printObjectState se
    else
        sprintf "if %s {\n%s\n}" (exprToString c) (sideEffectToString (fun a -> printObjectState (c :: a)) se |> tabRight)
and private sideEffectToString  (printObjectState) (se: SideEffect) =
    let heapStuff atState args =
        let objState = printObjectState [] atState args
        if String.IsNullOrEmpty objState then "" else sprintf ".heapStuff {\n%s\n}\n" (tabRight objState)
    match se with
    | SideEffect.MethodCall (m, resultValue, args, virt, globalEffect, atState) ->
        let core = sprintf "%O(%s)" m (String.Join(", ", args |> Seq.map exprToString))
        let core = if virt then "virt. " + core else core
        let core = if globalEffect then "global. " + core else core
        if m.ReturnType.FullName = "System.Void" then
            heapStuff atState args + core
        else
            heapStuff atState args + sprintf "%s := %s" resultValue.Name core
    | SideEffect.FieldRead (target, field, result, atState) ->
        let core = match target with Some(t) -> t.Name | _ -> ".static "
        let core = core + sprintf "[%O]" field
        heapStuff atState (Option.toArray target |> Seq.map SExpr.Parameter |> IArray.ofSeq) + sprintf "%s := " result.Name + core
    | SideEffect.FieldWrite (target, field, value, atState) ->
        let core = match target with Some(t) -> t.Name | _ -> ".static "
        let core = core + sprintf "[%O]" field
        heapStuff atState (Option.toArray target |> Seq.map SExpr.Parameter |> IArray.ofSeq) + sprintf "%s := %s" core (exprToString value)
    | SideEffect.Effects e ->
        e |> Seq.map (fun s -> sprintf " * %s" (csideEffectToString printObjectState s |> tabRight)) |> joinLines
    | _ -> failwith "NIE"

// and private getEffectDependencies (se: SideEffect) =
//     match se with
//     | SideEffect.MethodCall (_m, _result, args, _, _, _) ->
//         args
//     | SideEffect.Effects e ->
//         IArray.collect (fun (c, se) -> getEffectDependencies se) e
//     | _ -> failwith "NIE"

/// prints side effects and the state of object heap
let printStateFlow (state: ExecutionState) (heapRoots: #seq<SExpr>) =
    let writtenHeapState = Collections.Generic.Dictionary<SParameter, HeapObject>()
    let objectConditionScope = Collections.Generic.Dictionary<SParameter, SExpr clist>()
    let mutable endConditionScopeCleanup = ResizeArray<SParameter * FieldRef>()
    let mutable lastConditionScope = []

    let clearConditionScope () =
        for (o, f) in endConditionScopeCleanup |> Seq.groupBy (fst) do
            let mutable hobj = writtenHeapState.[o]
            for (_, field) in f do
                hobj <- { hobj with Fields = hobj.Fields.Remove(field) }
            writtenHeapState.[o] <- hobj
        endConditionScopeCleanup.Clear()

    let rec printObjectState (atState: AssumptionSet) (conditionScope: SExpr clist) (o: SParameter) =
        // clean condition scope if some conditions were removed
        let isSameConditionScope =
            lastConditionScope = conditionScope ||
            (conditionScope.Length > lastConditionScope.Length && List.take lastConditionScope.Length conditionScope = lastConditionScope)
        if not isSameConditionScope then
            clearConditionScope ()
        lastConditionScope <- conditionScope

        let heapObj = atState.Heap.[o]
        let todoObjects = ResizeArray()

        let printedObjectInitialization =
            match writtenHeapState.TryGetValue o with
            | (false, _) ->
                objectConditionScope.[o] <- conditionScope
                let fieldAssignments =
                    heapObj.Fields
                    |> Seq.sortBy (fun (KeyValue (f, _)) -> f.Name)
                    |> Seq.map (fun (KeyValue (field, value)) ->
                        todoObjects.Add value // recurse to objects
                        let fieldName = if heapObj.Type.Fields |> Seq.exists (fun f2 -> f2 = field) then
                                            field.Name
                                        else sprintf "[%O]" field
                        sprintf "%s.%s = %s" o.Name fieldName (exprToString value)
                    )
                [
                    if heapObj.TypeIsDefinite then
                        yield sprintf "let %s = new %O" o.Name o.Type
                    else
                        yield sprintf "def %s : %O" o.Name o.Type

                    if heapObj.IsShared = SExpr.ImmConstant true then
                        yield sprintf "shared %s" o.Name
                    else if heapObj.IsShared = SExpr.ImmConstant false then
                        yield! fieldAssignments
                    else
                        yield sprintf "shared %s iff %s" o.Name (exprToString heapObj.IsShared)
                        yield! fieldAssignments
                ]
            | (true, oldObj) when oldObj = heapObj ->
                []
            | (true, oldObj) ->
                let fieldAssignments =
                    heapObj.Fields
                    |> Seq.filter (fun (KeyValue (f, value)) -> not(oldObj.Fields.ContainsKey f && oldObj.Fields.[f] = value))
                    |> Seq.sortBy (fun (KeyValue (f, _)) -> f.Name)
                    |> Seq.map (fun (KeyValue (field, value)) ->
                        if objectConditionScope.[o] <> conditionScope then
                            endConditionScopeCleanup.Add (o, field)
                        todoObjects.Add value // recurse to objects
                        let fieldName = if Seq.exists (fun f2 -> FieldRef(f2) = field) heapObj.Type.Definition.Fields then // TODO: generic fields
                                            field.Name
                                        else sprintf "[%O]" field
                        sprintf "%s.%s = %s" o.Name fieldName (exprToString value)
                    )
                [
                    if heapObj.Type <> oldObj.Type then
                        yield sprintf "redef %s : %O%s" o.Name o.Type (if heapObj.TypeIsDefinite then "as definite" else "")

                    if heapObj.IsShared <> oldObj.IsShared then
                        yield sprintf "shared %s iff %s" o.Name (exprToString heapObj.IsShared)
                    if heapObj.IsShared <> SExpr.ImmConstant true then
                        yield! fieldAssignments
                ]
        writtenHeapState.[o] <- heapObj
        let printedDependecies = todoObjects |> getObjectsFromExpressions atState |> Seq.collect (printObjectState atState conditionScope)

        Seq.append printedDependecies printedObjectInitialization

    let printObjectState2 conditionScope atState (objects: #seq<SExpr>) =
        String.Join("\n", objects |> getObjectsFromExpressions atState |> Seq.collect (printObjectState atState conditionScope))

    let sideEffects = state.AllSideEffects |> Seq.map (csideEffectToString printObjectState2) |> joinLines
    let heapRoots = printObjectState2 [] state.Assumptions heapRoots

    if String.IsNullOrEmpty heapRoots then
        sideEffects
    else
        sprintf "%s\n.heapStuff {\n%s\n}" sideEffects (tabRight heapRoots)
let dumpState (state: ExecutionState) =
    let flow = printStateFlow state state.Stack
    sprintf "%s\n\nreturn [\n%s\n]" flow (state.Stack |> Seq.map exprToString |> joinLines |> tabRight)