module StateProcessing
open TypesystemDefinitions
open Expression
open InterpreterState
open System
open System.Collections.Generic
open System.Collections.Immutable
open System.Diagnostics.Contracts

let rec private accessObjectProperty (fn: SExpr -> SParameter option -> SExpr * (SExpr -> ExecutionState -> ExecutionState)) expr =
    let procLV lv =
        match lv with
        | SLExprNode.Parameter p ->
            fn expr (Some p)
        | SLExprNode.LdField (_field, None) ->
            fn expr None
        | SLExprNode.LdField (field, (Some target)) ->
            accessObjectProperty (fun e -> fn (SExpr.LdField field (Some e))) target
        | SLExprNode.LdElement (target, index) ->
            accessObjectProperty (fun e -> fn (SExpr.LdElement e index)) target
        | SLExprNode.Dereference d ->
            accessObjectProperty fn d
    match expr.Node with
    | SExprNode.LValue lv -> procLV lv
    | SExprNode.Reference lv -> procLV lv
    | SExprNode.Condition (cond, ifTrue, ifFalse) ->
        let ifTrue, s1 = accessObjectProperty fn ifTrue
        let ifFalse, s2 = accessObjectProperty fn ifFalse
        SExpr.Condition cond ifTrue ifFalse, (fun condition -> s1 (SExpr.BoolAnd condition cond) >> s2 (SExpr.BoolAnd condition cond |> SExpr.BoolNot))
    | SExprNode.InstructionCall (InstructionFunction.Box | InstructionFunction.Cast | InstructionFunction.IsInst as instruction, resultType, EqArray.AP [ arg ]) ->
        // cast instructions
        accessObjectProperty (fun e -> fn (SExpr.InstructionCall instruction resultType [ e ])) arg
    | SExprNode.PureCall _ ->
        fn expr None
    | e -> failwithf "Can't load field from %A" e


let getObjectsFromExpressions (atState: AssumptionSet) (expressions: #seq<SExpr>) =
    let resultObjects = Collections.Generic.List()
    let hashSet = Collections.Generic.HashSet()

    let markAsTodoExpression (expr: SExpr) =
        expr |> SExpr.Visitor (fun a _ ->
            match a.Node with
            | SExprNode.LValue (SLExprNode.Parameter x) ->
                if not (hashSet.Contains x) && atState.Heap.ContainsKey x then
                    hashSet.Add x |> ignore
                    resultObjects.Add x
            | _ -> ()
            None
        ) |> ignore
    Seq.iter markAsTodoExpression expressions
    resultObjects
let mutable private valueTypeCounter = 0L
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

let mutable private referenceTypeCounter = 0L

let createEmptyHeapObject (t: TypeRef) (state: ExecutionState) =
    let object, moreObj = initHeapObject t true
    let objParam = SParameter.New t (sprintf "o%d" (Threading.Interlocked.Increment(&referenceTypeCounter)))
    let state = state.ChangeObject (Seq.append moreObj [objParam, object])
    objParam, state

let initLocals (p: #seq<SParameter>) (state: ExecutionState) =
    let m = p
             |> Seq.map (fun p ->
                    let obj1, moreObj = createDefaultValue p.Type
                    KeyValuePair(p, obj1), moreObj
                )
    let state = state.ChangeObject (Seq.collect snd m)
    { state with Locals = state.Locals.AddRange(Seq.map fst m) }

let mergeStates a b =
    assert (a.Parent = b.Parent)
    assert (a.Parent.IsSome)
    let parent = a.Parent.Value
    let condition = a.Conditions |> Seq.reduce SExpr.BoolAnd
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
        Assumptions = AssumptionSet.changeObj changedObjects parent.Assumptions
        Stack = stack
        Locals = locals
        SideEffects = parent.SideEffects.AddRange(sideEffects)
    }

/// Returns an array of Condition * Result Type tuples, used for devirtualization
let rec analyseReturnType (expr: SExpr) state =
    if expr.ResultType.IsPrimitive || expr.ResultType.Definition.IsSealed || expr.ResultType.Definition.IsValueType then
        [ SExpr.ImmConstant true, expr.ResultType ]
    else

    match expr.Node with
    | SExprNode.LValue (SLExprNode.Parameter a) when state.Assumptions.Heap.ContainsKey a ->
        let hobj = state.Assumptions.Heap.[a]
        if hobj.TypeIsDefinite then
            [ SExpr.ImmConstant true, hobj.Type ]
        else []
    | _ -> [] // TODO: conditions, ...

let rec findOverridenMethod (t: TypeRef) (m: MethodRef) =
    if TypeRef(m.Reference.DeclaringType) = t then
        m
    else
        let methods = t.Definition.Methods
        let explicitOverride = methods |> Seq.tryFind (fun m2 -> m2.Overrides |> Seq.exists (fun ovr -> MethodRef.AreSameMethods ovr m.Reference))
        let matchedOverride () = methods |> Seq.tryFind (fun m2 -> m2.Name = m.Reference.Name && (m2.Parameters |> Seq.map (fun p -> TypeRef p.ParameterType) |> Seq.toList) = (m.Definition.Parameters |> Seq.map (fun p -> TypeRef p.ParameterType) |> Seq.toList))
        explicitOverride |> Option.orElseWith matchedOverride |> Option.map MethodRef |> Option.defaultWith (fun () -> findOverridenMethod (TypeRef t.Definition.BaseType) m)

/// Returns devirtualization info - list of (condition, method called, if it's virtual)
let devirtualize (m: MethodRef) (args: array<SExpr>) state =
    if not m.Definition.IsVirtual then
        [ SExpr.ImmConstant true, m, false ]
    else

    let targetTypes = analyseReturnType args.[0] state
    let restCondition =
        targetTypes
        |> Seq.map fst
        |> Seq.fold SExpr.BoolOr (SExpr.ImmConstant false)
        |> SExpr.BoolNot
        |> ExprSimplifier.simplify state.Assumptions
    [
        for (condition, t) in targetTypes do
            yield condition, findOverridenMethod t m, false
        if restCondition <> SExpr.ImmConstant false then
            yield restCondition, m, true
    ]

let private immutableTypes =
    Collections.Generic.HashSet([
        typeof<String>.FullName
    ])
let rec isTypeImmutable (m: TypeRef) =
    if m.Reference.IsPrimitive ||
        immutableTypes.Contains m.FullName ||
        m.Definition.CustomAttributes |> Seq.exists (fun a -> a.AttributeType.FullName = "System.Runtime.CompilerServices.IsReadOnlyAttribute")
        then true
    else

    let fields = m.Definition.Fields
    (m.Definition.IsSealed || m.Definition.IsValueType) && fields |> Seq.forall (fun f -> f.IsInitOnly && isTypeImmutable (TypeRef f.FieldType))

let getPureMethodSideEffectInfo (m: MethodRef) =
    let argCount = (if m.Reference.HasThis then 1 else 0) + m.Reference.Parameters.Count
    {
        MethodSideEffectInfo.IsGlobal = false
        IsPure = true
        ResultIsShared = false
        ArgumentBehavior = IArray.init argCount (fun _ -> MethodArgumentEffect.ReadOnly)
        ActualResultType = None
    }

let getDefensiveSideEffectInfo (m: MethodRef) =
    let args = m.ParameterTypes
    {
        MethodSideEffectInfo.IsGlobal = true
        IsPure = false
        ResultIsShared = true
        ArgumentBehavior = args |> IArray.map (fun p -> if isTypeImmutable p then MethodArgumentEffect.ReadOnly else MethodArgumentEffect.Shared)
        ActualResultType = None
    }

// let private knownMethods = Map.ofSeq [
// ]

let getMethodSideEffectInfo (m: MethodRef) =
    if m.Definition.CustomAttributes |> Seq.exists (fun a -> a.AttributeType.FullName = typeof<PureAttribute>.FullName) then
        getPureMethodSideEffectInfo m
    else
        getDefensiveSideEffectInfo m


let rec markObjectShared (o: SParameter) (condition: SExpr) state =
    let hobj = state.Assumptions.Heap.[o]
    if hobj.IsShared = condition then
        state
    else

    let shared = SExpr.BoolOr hobj.IsShared condition |> ExprSimplifier.simplify state.Assumptions
    if shared = hobj.IsShared then
        state
    else

    let state = state.ChangeObject [ o, { hobj with IsShared = shared } ]
    markUsedObjectsShared hobj.Fields.Values condition state
and markUsedObjectsShared (exprs: seq<SExpr>) condition state =
    // TODO: `field = a ? objX : objY` should mark synchronized the objX only if a
    let fieldObjects = exprs |> getObjectsFromExpressions state.Assumptions
    fieldObjects |> Seq.fold (fun state fieldObj ->
        markObjectShared fieldObj condition state
    ) state

let markUsedObjectsUnknown (exprs: seq<SExpr>) (state: ExecutionState) =
    let fieldObjects = exprs |> getObjectsFromExpressions state.Assumptions
    fieldObjects |> Seq.fold (fun (state: ExecutionState) fieldObj ->
        state.ChangeObject [ fieldObj, { state.Assumptions.Heap.[fieldObj] with Fields = dict<_, _>.Empty } ]
    ) state

/// Disallows a pure call if the function could touch some unexpected unpure virtual functions
let private isCallNonVirtual (m: MethodRef) (args: seq<SExpr>) state =
    // skip `this` argument, it's handled by devirtualization
    let args = if m.Reference.HasThis then Seq.skip 1 args else args
    let suspiciousArgs =
        Seq.zip args m.Reference.Parameters
        |> Seq.choose (fun (a, p) ->
            let resultTypes = analyseReturnType a state
            match resultTypes |> Seq.tryFind (fun (c, t) -> t = TypeRef(p.ParameterType)) with
            | Some (condition_same, _) when condition_same = SExpr.ImmConstant true ->
                None
            | _ ->

            Some (a, p, resultTypes)
        )
        |> IArray.ofSeq
    if suspiciousArgs.Length = 0 then
        true
    else
        false // TODO: more checks

let markSideEffectArguments (args: SExpr array) (argInfo: MethodArgumentEffect array) =
    let zip = Seq.zip args argInfo
    let sharedOnes = zip |> Seq.filter (fun (_, i) -> i = MethodArgumentEffect.Shared) |> Seq.map fst
    let mutableOnes = zip |> Seq.filter (fun (_, i) -> i = MethodArgumentEffect.Mutable) |> Seq.map fst

    markUsedObjectsShared sharedOnes (SExpr.ImmConstant true) >> markUsedObjectsUnknown mutableOnes


let mutable private sideEffectCounter = 0L
let private sideEffectResult t =
    SParameter.New t (sprintf "se%d" (Threading.Interlocked.Increment(&sideEffectCounter)))
let private addResultObject (result: SParameter) heapType (isShared: bool) (state: ExecutionState) =
    if result.Type.FullName = "System.Void" then state
    else
        state.ChangeObject [
            result, { HeapObject.Type = heapType |> Option.defaultValue result.Type
                      TypeIsDefinite = heapType.IsSome || result.Type.Definition.IsSealed
                      Fields = dict<_, _>.Empty
                      IsShared = SExpr.ImmConstant isShared } ]

let addCallSideEffect (m: MethodRef) (seInfo: MethodSideEffectInfo) args virt state =
    let args = IArray.ofSeq args
    let hasNonvirtualArgs = virt || isCallNonVirtual m args state
    if seInfo.IsPure && hasNonvirtualArgs then
        let expressionResult = SExpr.PureCall m args
        { state with Stack = expressionResult :: state.Stack }
    else

    let result = sideEffectResult m.ReturnType
    // mark everything reachable as shared
    let state =  markSideEffectArguments args seInfo.ArgumentBehavior state
    let effect = SideEffect.MethodCall (m, result, args, virt, seInfo.IsGlobal, state.Assumptions)
    let state = { state with SideEffects = state.SideEffects.Add(SExpr.ImmConstant true, effect) }

    let state = addResultObject result seInfo.ActualResultType seInfo.ResultIsShared state
    if result.Type.FullName = "System.Void" then state
    else { state with Stack = SExpr.Parameter result :: state.Stack }
let private addFieldReadSideEffect (target: SParameter option) (field: FieldRef) =
    let result = sideEffectResult (TypeRef field.Reference.FieldType)
    result, (fun condition state ->
        let effect = SideEffect.FieldRead (target, field, result, state.Assumptions)
        let state = { state with SideEffects = state.SideEffects.Add(condition |> ExprSimplifier.simplify state.Assumptions, effect) }
        addResultObject result None true state
    )

let accessField target field state =
    let result, s = target |> accessObjectProperty (fun expr objectParam ->
        let hobj = objectParam |> Option.bind (state.Assumptions.Heap.TryGet)
        match hobj with
        | (Some hobj) when hobj.IsShared <> SExpr.ImmConstant false ->
            // side effect...
            let result, s = addFieldReadSideEffect objectParam field
            SExpr.Parameter result, s
        | (Some hobj) when hobj.Fields.ContainsKey field ->
            hobj.Fields.[field], (fun _ a -> a)
        | _ ->
            SExpr.LdField field (Some expr), (fun _ a -> a)
    )
    result, s (SExpr.ImmConstant true) state

let accessStaticField field state =
    // TODO: immutable static fields
    let result, s = addFieldReadSideEffect None field
    SExpr.Parameter result, s (SExpr.ImmConstant true) state

let readLValue (expr: SLExprNode) (state: ExecutionState) =
    match expr with
    | SLExprNode.Parameter p ->
        if state.Locals.ContainsKey p then
            state.Locals.[p], state
        else
            failwithf "Can't read LValue parameter %A" p
    | SLExprNode.LdField (field, Some target) ->
        accessField target field state
    | SLExprNode.LdField (field, None) ->
        accessStaticField field state
    | _ -> failwithf "Can't read LValue, expression of type %O" (expr.GetType())
let dereference (expr: SExpr) (state: ExecutionState) =
    match expr.Node with
    | SExprNode.Reference lv -> readLValue lv state
    | _ -> failwithf "Can't deref"