module StateProcessing
open TypesystemDefinitions
open Expression
open InterpreterState
open System
open System.Collections.Generic
open System.Collections.Immutable
open System.Diagnostics.Contracts
open Mono.Cecil.Rocks
open ExprSimplifier
let rec stackLoadConvert (expr: SExpr) =
    let t = expr.ResultType
    if not t.IsPrimitive then
        expr
    elif t.FullName = typeof<int>.FullName || t.FullName = typeof<int64>.FullName || t.FullName = typeof<float>.FullName || t.FullName = typeof<System.UIntPtr>.FullName || t.FullName = typeof<System.IntPtr>.FullName || t = CecilTools.nintType || t = CecilTools.nuintType then
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
    elif t.BaseType = Some (CecilTools.enumType) then
        let underlyingType = TypeRef (t.Definition.GetEnumUnderlyingType())
        stackLoadConvert (SExpr.Cast InstructionFunction.Convert underlyingType expr)
    else
        tooComplicated <| sprintf "unsupported stack load conversion from '%O'." expr.ResultType

let stackConvert (expr: SExpr) (targetType: TypeRef) =
    if expr.ResultType = targetType then expr
    elif expr.ResultType.IsPrimitive && targetType.IsPrimitive then
        SExpr.Cast InstructionFunction.Convert targetType expr
    elif expr.ResultType.IsPrimitive && targetType.Definition.IsEnum then
        SExpr.Cast InstructionFunction.Convert targetType (SExpr.Cast InstructionFunction.Convert (targetType.Definition.GetEnumUnderlyingType() |> TypeRef) expr)
    elif expr.ResultType.IsObjectReference && targetType.IsObjectReference && isDownCast expr.ResultType targetType then
        SExpr.Cast InstructionFunction.Cast targetType expr
    elif expr.ResultType.IsObjectReference && targetType.IsObjectReference &&
        expr.Node = SExprNode.Constant null then
        SExpr.New targetType (expr.Node)
    elif targetType.FullName = "System.Array" && expr.ResultType.Reference.IsArray then
        SExpr.Cast InstructionFunction.Cast targetType expr
    elif targetType.IsObjectReference && expr.ResultType.IsObjectReference then
        let resultTypeAnalysis = analyseReturnType expr ExecutionState.Empty
        if resultTypeAnalysis |> Seq.forall (fun (_, t, _) -> isDownCast t targetType) then
            SExpr.Cast InstructionFunction.Cast targetType expr
        else
            waitForDebug()
            failwithf "Can't do implicit stack conversion %O -> %O, the result type was analysed and does not fit" expr.ResultType targetType
    else
        assertOrComplicated (not expr.ResultType.Reference.IsPointer && not targetType.Reference.IsPointer) "Can't work with pointers (implicit conversion)"
        softAssert false <| sprintf "Can't do implicit stack conversion %O -> %O" expr.ResultType targetType
        failwith ""

let stackConvertToUnsigned (a: SExpr) =
    if a.ResultType.FullName = typeof<int32>.FullName then
        SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType typeof<uint32>) [a]
    elif a.ResultType.FullName = typeof<int64>.FullName then
        SExpr.InstructionCall InstructionFunction.Convert (CecilTools.convertType typeof<uint64>) [a]
    elif a.ResultType = CecilTools.nintType then
        SExpr.InstructionCall InstructionFunction.Convert (CecilTools.nuintType) [a]
    elif a.ResultType.FullName = typeof<float>.FullName then
        a // TODO: float.NaN glitches :(
    elif a.Node = SExprNode.Constant null then
        SExpr.ImmConstant 0u
    else
        softAssert false <| sprintf "Coertion to unsigned '%O' not .supported" a.ResultType
        failwith ""

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
    | SExprNode.InstructionCall (InstructionFunction.Cast | InstructionFunction.IsInst as instruction, resultType, EqArray.AP [ arg ]) ->
        // cast instructions
        accessObjectProperty (fun e -> fn (SExpr.InstructionCall instruction resultType [ e ])) arg
    | SExprNode.PureCall _ ->
        fn expr None
    | SExprNode.Constant c ->
        fn expr None
    | e -> failwithf "Can't access property at %A" e


let getObjectsFromExpressions (atState: AssumptionSet) (expressions: #seq<SExpr>) =
    let resultObjects = Collections.Generic.List()
    let hashSet = Collections.Generic.HashSet()

    let markAsTodoExpression (expr: SExpr) =
        expr |> SExpr.Visitor (fun a _ ->
            match a.Node with
            | SExprNode.LValue (SLExprNode.Parameter x) | SExprNode.Reference (SLExprNode.Parameter x) ->
                if not (hashSet.Contains x) && atState.Heap.ContainsKey x then
                    hashSet.Add x |> ignore
                    resultObjects.Add x
            | _ -> ()
            None
        ) |> ignore
    Seq.iter markAsTodoExpression expressions
    resultObjects

// let rec private enumerateFields (t: TypeRef) =
//     seq {
//         yield! t.Definition.Fields
//         if t.Definition.BaseType <> null then
//             yield! enumerateFields (TypeRef t.Definition.BaseType)
//     }
let private createValueTypeParameter =
    let mutable valueTypeCounter = 0L
    fun t -> SParameter.New t (sprintf "v%d" (Threading.Interlocked.Increment(&valueTypeCounter)))
let rec createDefaultValue (t: TypeRef) =
    if t.IsPrimitive then
        // just take default value
        SExpr.New t (SExprNode.Constant (Activator.CreateInstance (Type.GetType t.FullName))), Seq.empty
    elif t.Reference.IsValueType then
        // create default object for value type
        let obj1, moreObjs = initHeapObject t true
        let param = createValueTypeParameter t
        SExpr.Parameter param, Seq.append [ param, obj1 ] moreObjs
    else
        // reference types default to null
        SExpr.New t (SExprNode.Constant null), Seq.empty

and initHeapObject (t: TypeRef) definiteType =
    let fieldsWithObjects =
        t.Fields
        |> Seq.filter (fun f -> not f.Definition.IsStatic)
        |> Seq.map (fun f ->
            softAssert (not t.Reference.IsValueType || f.FieldType <> t) "Value type can't contain field of itself"
            let value, heapObjects = createDefaultValue f.FieldType
            KeyValuePair(f, value), heapObjects
        )
    { HeapObject.Type = t
      TypeIsDefinite = definiteType
      IsShared = SExpr.ImmConstant false
      Fields = Seq.map fst fieldsWithObjects |> ImmutableDictionary.CreateRange
      Array = None
    }, (Seq.collect snd fieldsWithObjects |> IArray.ofSeq)

let rec copyReference (expr: SExpr) (state: ExecutionState) =
    if expr.ResultType.IsPrimitive || not expr.ResultType.Reference.IsValueType || expr.ResultType.Definition.CustomAttributes |> Seq.exists (fun a -> a.AttributeType.FullName = "System.Runtime.CompilerServices.IsReadOnlyAttribute") then
        expr, state
    else

    let result, procState =
        accessObjectProperty (fun expr param ->
            softAssert param.IsSome "Must have value"
            let fields =
                match state.Assumptions.Heap.TryGet(param.Value) with
                | Some hobj -> softAssert hobj.TypeIsDefinite ""; hobj.Fields
                | None -> dict<_, _>.Empty
            let fields =
                param.Value.Type.Fields
                |> IArray.map (fun f -> f, fields.TryGet f |> Option.defaultWith (fun () -> SExpr.LdField f (Some expr)))
            let t = param.Value.Type
            let objParam = createValueTypeParameter t
            let result = ExprSimplifier.assignParameters (fun p -> if p = param.Value then Some (SExpr.Parameter param.Value) else None) expr
            let procState _condition state =
                let fields, state =
                    fields
                    |> Seq.mapFold (fun state (field, value) ->
                        let value, state = copyReference value state
                        KeyValuePair(field, value), state
                    ) state
                let newObj =
                    { HeapObject.Type = t
                      TypeIsDefinite = true
                      IsShared = SExpr.ImmConstant false
                      Fields = fields |> ImmutableDictionary.CreateRange
                      Array = None
                    }
                state.ChangeObject [objParam, newObj]
            result, procState
        ) expr

    result, (procState (SExpr.ImmConstant true) state)


let mutable private referenceTypeCounter = 0L
let getObjectParam t = SParameter.New t (sprintf "o%d" (Threading.Interlocked.Increment(&referenceTypeCounter)))

let createEmptyHeapObject (t: TypeRef) (state: ExecutionState) =
    let object, moreObj = initHeapObject t true
    let objParam = getObjectParam t
    // printfn "Adding object %s : %O to %A" objParam.Name objParam.Type (List.ofSeq (state.Assumptions.Heap.Keys |> Seq.map (fun p -> p.Name)))
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

let private createCondition (cond:SExpr) (a:SExpr) (b:SExpr) =
    let a, b =
        if a.ResultType = b.ResultType then a, b
        else if isDownCast a.ResultType b.ResultType then SExpr.Cast InstructionFunction.Cast b.ResultType a, b
        else if isDownCast b.ResultType a.ResultType then a, SExpr.Cast InstructionFunction.Cast a.ResultType b
        else if a.ResultType.IsObjectReference && b.ResultType.IsObjectReference then
            SExpr.Cast InstructionFunction.Cast CecilTools.objType a, SExpr.Cast InstructionFunction.Cast CecilTools.objType b
        else failwithf "Can't implicitly create condition from expressions of type %O and %O" a.ResultType b.ResultType
    SExpr.Condition cond a b

/// combines (condition * expression) list into a conditional exception
let private mergeBranches (branches: (SExpr * SExpr) seq) =
    let groups = branches |> Seq.groupBy snd |> Seq.toArray
    if groups.Length = 1 then
        fst groups.[0]
    else
        let groupedBranches = groups
                              |> Seq.map (fun (value, conditions) ->
                                   let condition = conditions |> Seq.map fst |> Seq.reduce SExpr.BoolAnd
                                   condition, value
                              )
        groupedBranches |> Seq.reduce (fun (_, a) (c, b) ->
            c, createCondition c b a
        ) |> snd
let private mergeObjects (objects: (SExpr * HeapObject) clist) =
    let objType = objects |> Seq.map (fun (_, o) -> o.Type) |> Seq.distinct |> Seq.exactlyOne // TODO: type changes
    let combined =
        { HeapObject.Type = objType
          TypeIsDefinite = objects |> Seq.forall (fun (_, o) -> o.TypeIsDefinite)
          IsShared = objects |> Seq.map (fun (c, o) -> c, o.IsShared) |> mergeBranches |> ExprSimplifier.simplify AssumptionSet.empty
          Fields =
            let fields =
                objects
                |> Seq.collect (fun (_, o) -> o.Fields.Keys)
                |> Seq.distinct
            objects.[0].Item2.Fields.SetItems(fields |> Seq.map (fun field ->
                let value =
                    objects
                    |> Seq.choose (fun (c, o) -> o.Fields.TryGet field |> Option.map (fun v -> c, v))
                    |> mergeBranches |> ExprSimplifier.simplify AssumptionSet.empty
                KeyValuePair (field, value)
            ))
          Array =
            softAssert (objects |> Seq.forall (fun (_, o) -> o.Array.IsNone)) "Merging arrays is not implemented" // TODO:
            None
        }
    combined
let mergeStates (states: ExecutionState seq) =
    let states = IArray.ofSeq states
    softAssert (states.Length > 0) "There has to be some states"
    let parent = states |> Seq.map (fun s -> s.Parent) |> Utils.getOnlyElement |> Option.bind id |> Utils.optionExpect "Merged states must have the same parent"
    let conditions = states |> IArray.map (fun a -> a.Conditions |> Seq.reduce SExpr.BoolAnd)
    let changedObjects =
        states
        |> Seq.collect (fun s -> s.ChangedHeapObjects)
        |> Seq.distinct
        |> Seq.map (fun op ->
            let objectsFromHeaps = Seq.zip conditions states
                                   |> Seq.choose (fun (cond, s) ->
                                        s.Assumptions.Heap.TryGet op |> Option.map (fun o -> cond, o))
                                   |> Seq.toList
            match objectsFromHeaps with
            | [] -> softAssert false (sprintf "wtf, %s was in the changed objects but not on heap." op.Name); failwith ""
            | [_cond, o] -> op, o
            | objects -> op, (mergeObjects objects)
        ) |> IArray.ofSeq
    let locals =
        parent.Locals
        |> Seq.choose (fun (KeyValue(loc, value)) ->
            let newValue = states |> Seq.map2 (fun cond state -> cond, state.Locals.[loc]) conditions |> mergeBranches |> ExprSimplifier.simplify parent.Assumptions
            if LanguagePrimitives.PhysicalEquality newValue value || newValue = value then
                None
            else Some (KeyValuePair(loc, newValue))
        )
        |> parent.Locals.SetItems
    let stack =
        states
        |> Seq.map (fun s -> s.Stack)
        |> Seq.toList
        |> List.transpose
        |> List.map (Seq.zip conditions >> mergeBranches >> ExprSimplifier.simplify parent.Assumptions)
    let sideEffects =
        let commonEffects =
            Seq.transpose (states |> IArray.map (fun s -> s.SideEffects.Reverse()))
            |> Seq.take 0
            |> Seq.takeWhile (Utils.getOnlyElement >> Option.isSome)
            |> Seq.map Seq.head
            |> Seq.toArray |> Array.rev
        seq {
            for (a, condition) in Seq.zip states conditions do
                let effects = Seq.take (a.SideEffects.Count - commonEffects.Length) (a.SideEffects) |> IArray.ofSeq
                softAssert (condition <> SExpr.ImmConstant false) "Condition of a state should not be false"
                if effects.Length > 0 then
                    yield (condition, SideEffect.Effects effects)
            yield! commonEffects
        }
    { parent.ChangeObject changedObjects with
        Stack = stack
        Locals = locals
        SideEffects = parent.SideEffects.AddRange(sideEffects)
    }

/// Returns an array of Condition * Result Type * Is Definite tuples, used for devirtualization and type check reduction
let rec analyseReturnType (expr: SExpr) state =
    if expr.ResultType.IsPrimitive || expr.ResultType.Definition.IsSealed || expr.ResultType.Definition.IsValueType then
        [ SExpr.ImmConstant true, expr.ResultType, true ]
    else

    match expr.Node with
    | SExprNode.LValue (SLExprNode.Parameter a) when state.Assumptions.Heap.ContainsKey a ->
        let hobj = state.Assumptions.Heap.[a]
        [ SExpr.ImmConstant true, hobj.Type, hobj.TypeIsDefinite ]
    | SExprNode.Constant a -> [ SExpr.ImmConstant true, (if isNull a then expr.ResultType else CecilTools.convertType (a.GetType())), not (isNull a) ]
    | SExprNode.InstructionCall ((InstructionFunction.Cast | InstructionFunction.IsInst), castTo, EqArray.AP [ expr ]) ->
        analyseReturnType expr state
            |> List.map (fun (c, t, d) ->
                if d || ExprSimplifier.isDownCast t castTo then
                    (c, t, d)
                else (c, castTo, false)
            )
    | SExprNode.Condition (cond, ifTrue, ifFalse) ->
        List.append
            (analyseReturnType ifTrue state |> List.map (fun (c, e, d) -> ExprSimplifier.simplify state.Assumptions (SExpr.BoolAnd cond c), e, d))
            (analyseReturnType ifFalse state |> List.map (fun (c, e, d) -> ExprSimplifier.simplify state.Assumptions (SExpr.BoolAnd (SExpr.BoolNot cond) c), e, d))
    | _ -> [ SExpr.ImmConstant true, expr.ResultType, false ]

let rec findOverridenMethod (t: TypeRef) (m: MethodRef) =
    if TypeRef(m.Reference.DeclaringType) = t || t.Definition.IsInterface then
        m
    else
        let genericResolver = if t.Reference.IsGenericInstance then (fun (mm: Mono.Cecil.MethodReference) -> mm.RebaseOn(t.Reference).ResolvePreserve(t.GenericParameterAssigner).ResolvePreserve(m.GenericParameterAssigner)) else id
        let methods = t.Methods
        let explicitOverride = methods |> Seq.tryFind (fun m2 ->
            m2.Overrides |> Seq.exists ((=) m))
        let matchedOverride () =
            methods
            |> Seq.filter (fun m2 -> m2.Name = m.Reference.Name && m.Reference.HasThis)
            |> Seq.tryFind (fun m2 -> (m2.ParameterTypes |> Seq.toList).Tail = (m.ParameterTypes |> Seq.toList).Tail)
        explicitOverride
            |> Option.orElseWith matchedOverride
            |> Option.defaultWith (fun () ->
                softAssert t.BaseType.IsSome <| sprintf "Can't find overriden method %O on type %O" m t
                findOverridenMethod t.BaseType.Value m)
/// Returns devirtualization info - list of (condition, method called, if it's virtual)
let devirtualize (m: MethodRef) (args: array<SExpr>) state =
    if not m.Definition.IsVirtual then
        [ SExpr.ImmConstant true, m, false ]
    else

    let targetTypes = analyseReturnType args.[0] state
                      |> List.map (fun (condition, t, definite) ->
                          condition, findOverridenMethod t m, not (definite || t.Definition.IsSealed || t.Definition.IsValueType)
                      )
                      |> List.groupBy (fun (_c, m, d) -> m, d)
    if targetTypes.Length = 1 then
        targetTypes |> List.map (fun ((m, d), _) -> SExpr.ImmConstant true, m, d)
    else
        targetTypes |> List.map (fun ((m, d), branches) ->
            let condition = branches |> List.map (fun (c, _, _) -> c) |> List.reduce SExpr.BoolOr
            (condition, m, d)
        )

let private immutableTypes =
    Collections.Generic.HashSet([
        typeof<String>.FullName
    ])
let rec isTypeImmutable (m: TypeRef) =
    if m.Reference.IsPrimitive ||
        immutableTypes.Contains m.FullName
        then true
    else if not m.HasDefinition then
        false
    else if m.Definition.CustomAttributes |> Seq.exists (fun a -> a.AttributeType.FullName = "System.Runtime.CompilerServices.IsReadOnlyAttribute") then
        true
    else if m.Reference.IsValueType then
        false // value types may be mutated in strange ways
    else

    let fields = m.Fields
    fields |> Seq.forall (fun f -> f.Definition.IsInitOnly && (f.FieldType.Definition.IsSealed || f.FieldType.Definition.IsValueType) && isTypeImmutable f.FieldType)

let rec isObjectImmutable (object: HeapObject) haveReferenceToIt (state: ExecutionState) =
    let t = object.Type
    if not object.TypeIsDefinite then
        softAssert (not t.Definition.IsValueType && not t.Definition.IsSealed) "The type actually is definite"
        false
    elif object.Array.IsSome then
        object.Array.Value.Length = Some (SExpr.ImmConstant IntPtr.Zero)
    elif t.Reference.IsPrimitive || immutableTypes.Contains t.FullName then
        true
    elif t.Definition.CustomAttributes |> Seq.exists (fun a -> a.AttributeType.FullName = "System.Runtime.CompilerServices.IsReadOnlyAttribute") then
        true
    elif t.Reference.IsValueType && haveReferenceToIt then
        false
    else
    let fields = t.Fields
    fields |> Seq.forall (fun f ->
        f.Definition.IsInitOnly && (isTypeImmutable f.FieldType ||
            match object.Fields.TryGet f with
            | None -> false
            | Some fValue ->
                let parameters = new ResizeArray<SParameter>()
                SExpr.Visitor (fun expr _ ->
                    match expr.Node with
                    | SExprNode.LValue (SLExprNode.Parameter p) | SExprNode.Reference (SLExprNode.Parameter p) ->
                        parameters.Add p
                    | _ -> ()
                    None) fValue |> ignore
                parameters |> Seq.forall (fun p ->
                    match state.Assumptions.Heap.TryGet p with
                    | None -> false
                    | Some h -> isObjectImmutable h false state
                )
        ))

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
        ArgumentBehavior = args |> IArray.map (fun p -> if (p.Definition.IsSealed || p.Definition.IsValueType) && isTypeImmutable p then MethodArgumentEffect.ReadOnly else MethodArgumentEffect.Shared)
        ActualResultType = None
    }

// let private knownMethods = Map.ofSeq [
// ]

let getMethodSideEffectInfo (m: MethodRef) =
    if m.Definition.CustomAttributes |> Seq.exists (fun a -> a.AttributeType.FullName = typeof<PureAttribute>.FullName) then
        getPureMethodSideEffectInfo m
    else if m.ToString() = "System.Void Cisint.Tests.TestInputs.Something::EffectOutObject(System.Object)" then
        {
            MethodSideEffectInfo.IsGlobal = true
            IsPure = false
            ResultIsShared = true
            ArgumentBehavior = ImmutableArray.Create MethodArgumentEffect.ReadOnly
            ActualResultType = None
        }
    else
        getDefensiveSideEffectInfo m


let rec markObjectShared (o: SParameter) (condition: SExpr) state =
    let hobj = state.Assumptions.Heap.[o]
    if hobj.IsShared = condition || isObjectImmutable hobj false state then
        state
    else

    let shared = SExpr.BoolOr hobj.IsShared condition |> ExprSimplifier.simplify state.Assumptions
    if shared = hobj.IsShared then
        state
    else

    let state = state.ChangeObject [ o, { hobj with IsShared = shared } ]
    markUsedObjectsShared hobj.Fields.Values condition state
and markUsedObjectsShared (exprs: seq<SExpr>) condition state =
    if condition = SExpr.ImmConstant false then
        state
    else
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
            match resultTypes |> Seq.tryFind (fun (c, t, d) -> t = TypeRef(p.ParameterType.ResolvePreserve(m.GenericParameterAssigner))) with
            | Some (condition_same, _, _) when condition_same = SExpr.ImmConstant true ->
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

let newArray len (elType: TypeRef) (state: ExecutionState) =
    let defaultVal, newObjects = createDefaultValue elType
    let state = state.ChangeObject newObjects
    let array = { ArrayInfo.Initialize defaultVal with Length = len |> Option.map (fun e -> stackConvert e CecilTools.nintType) }
    let heapObj =
        { HeapObject.Type = TypeRef.CreateArray elType
          TypeIsDefinite = true
          IsShared = SExpr.ImmConstant false
          Fields = dict<_, _>.Empty
          Array = Some array
        }
    heapObj, state

let mutable private sideEffectCounter = 0L
let private sideEffectResult t =
    SParameter.New t (sprintf "se%d" (Threading.Interlocked.Increment(&sideEffectCounter)))
let private addResultObject (result: SParameter) heapType (isShared: bool) (state: ExecutionState) =
    if result.Type.FullName = "System.Void" then state
    else
        let array, state =
            if result.Type.Reference.IsArray then
                let elType = (result.Type.Reference :?> Mono.Cecil.ArrayType).ElementType |> TypeRef
                let a, state = newArray None elType state
                a.Array, state
            else None, state
        state.ChangeObject [
            result, { HeapObject.Type = heapType |> Option.defaultValue result.Type
                      TypeIsDefinite = heapType.IsSome || result.Type.Definition.IsSealed
                      Fields = dict<_, _>.Empty
                      IsShared = SExpr.ImmConstant isShared
                      Array = array } ]

let assertDecidableArgs (args: SExpr seq) =
    assertOrComplicated (args |> Seq.forall (fun a -> not a.IsUndecidable)) "Can't create a side effect with undecidable args."
    assertOrComplicated (args |> Seq.forall (fun a -> not a.ResultType.Reference.IsByReference)) "passing reference to a side effect"

let addCallSideEffect (m: MethodRef) (seInfo: MethodSideEffectInfo) args virt state =
    let args = IArray.ofSeq args
    assertDecidableArgs args
    let hasNonvirtualArgs = virt || isCallNonVirtual m args state
    if seInfo.IsPure && hasNonvirtualArgs then
        let expressionResult = SExpr.PureCall m args
        { state with Stack = stackLoadConvert expressionResult :: state.Stack }
    else

    let result = sideEffectResult (TypeRef (m.ReturnType.Reference.ResolvePreserve m.GenericParameterAssigner))
    // mark everything reachable as shared
    let state = markSideEffectArguments args seInfo.ArgumentBehavior state
    let effect = SideEffect.MethodCall (m, result, args, virt, seInfo.IsGlobal, state.Assumptions)
    let state = { state with SideEffects = state.SideEffects.Add(SExpr.ImmConstant true, effect) }

    let state = addResultObject result seInfo.ActualResultType seInfo.ResultIsShared state
    if result.Type.FullName = "System.Void" then state
    else { state with Stack = stackLoadConvert (SExpr.Parameter result) :: state.Stack }
let private addFieldReadSideEffect (target: SParameter option) (field: FieldOrElement) =
    let result = sideEffectResult field.ResultType
    result, (fun condition state ->
        let condition = condition |> ExprSimplifier.simplify state.Assumptions
        if condition <> SExpr.ImmConstant false then
            let effect = SideEffect.FieldRead (target, field, result, state.Assumptions)
            let state = { state with SideEffects = state.SideEffects.Add(condition, effect) }
            addResultObject result None true state
        else
            state
    )
let private addFieldWriteSideEffect (target: SParameter option) (field: FieldOrElement) (value: SExpr) condition state =
    let condition = condition |> ExprSimplifier.simplify state.Assumptions
    if condition <> SExpr.ImmConstant false then
        assertDecidableArgs [value]
        let state =
            let sharedCondition = target |> Option.bind (state.Assumptions.Heap.TryGet) |> Option.map (fun o -> o.IsShared) |> Option.defaultValue (SExpr.ImmConstant true)
            markUsedObjectsShared [value] sharedCondition state
        let value = stackConvert value field.ResultType
        let effect = SideEffect.FieldWrite (target, field, value, state.Assumptions)
        { state with SideEffects = state.SideEffects.Add(condition |> ExprSimplifier.simplify state.Assumptions, effect) }
    else
        state

let private getArrayElement (arrayInfo: ArrayInfo) index =
    let gExpr = arrayInfo.GeneralExpression
    let gExpr = lazy ExprSimplifier.assignParameters (fun p -> if p = InterpreterState.indexParameter then Some index else None) gExpr
    let resultExpr =
        match index.Node with
        | SExprNode.Constant c ->
            arrayInfo.Constants.TryGet(c :?> int) |> Option.defaultWith (fun () -> gExpr.Value)
        | _ ->
            let constants = arrayInfo.Constants |> Seq.map (fun a -> a.Key, a.Value)
            constants
                |> Seq.fold (fun expr (indexC, value) ->
                    SExpr.Condition (SExpr.InstructionCall InstructionFunction.C_Eq CecilTools.boolType [ SExpr.ImmConstant indexC; index ]) value expr
                ) gExpr.Value
    resultExpr

let accessField target field state =
    let result, s = target |> accessObjectProperty (fun expr objectParam ->
        let hobj = objectParam |> Option.bind (state.Assumptions.Heap.TryGet)
        match hobj, field with
        | (Some hobj), _ when hobj.IsShared <> SExpr.ImmConstant false ->
            // side effect...
            let result, s = addFieldReadSideEffect objectParam field
            SExpr.Parameter result, s
        | (Some hobj), (FieldOrElement.FieldRef field) when hobj.Fields.ContainsKey field ->
            hobj.Fields.[field], (fun _ -> id)
        | (Some hobj), (FieldOrElement.ElementRef (index, _returnType)) ->
            // return expression
            let array = hobj.Array.Value
            getArrayElement array index, (fun _ -> id)
        | _, (FieldOrElement.FieldRef field) ->
            match expr.Node with
            | SExprNode.Constant a when not(isNull a) ->
                let t = a.GetType().GetField(field.Name, System.Reflection.BindingFlags.Instance ||| System.Reflection.BindingFlags.NonPublic||| System.Reflection.BindingFlags.Public)
                t.GetValue a |> SExprNode.Constant |> SExpr.New field.FieldType, (fun _ a -> a)
            | _ -> SExpr.LdField field (Some expr), (fun _ a -> a)
        | _, (FieldOrElement.ElementRef (index, _retType)) ->
            match expr.Node with
            // TODO: constant folding with array access
            // | SExprNode.Constant a when not(isNull a) ->
            //     let t = a.GetType().GetField(field.Name, System.Reflection.BindingFlags.Instance ||| System.Reflection.BindingFlags.NonPublic||| System.Reflection.BindingFlags.Public)
            //     t.GetValue a |> SExprNode.Constant |> SExpr.New field.FieldType, (fun _ a -> a)
            | _ -> SExpr.LdElement expr index, (fun _ a -> a)
    )
    ExprSimplifier.simplify state.Assumptions result, s (SExpr.ImmConstant true) state

let accessLength target state =
    let result, s = target |> accessObjectProperty (fun expr objectParam ->
        let hobj = objectParam |> Option.bind (state.Assumptions.Heap.TryGet)
        match hobj with
        | (Some { Array = Some({ Length = Some(l) }) }) ->
            l, fun _ -> id
        | _ ->
            SExpr.InstructionCall InstructionFunction.ArrLen CecilTools.nintType [ expr ], fun _ -> id
    )
    ExprSimplifier.simplify state.Assumptions result, s (SExpr.ImmConstant true) state

let setField target field value state =
    assertDecidableArgs [target; value]
    let _, s = target |> accessObjectProperty (fun expr objectParam ->
        let hobj = objectParam |> Option.bind (state.Assumptions.Heap.TryGet)
        match hobj with
        | (Some hobj) when hobj.IsShared <> SExpr.ImmConstant false ->
            // side effect...
            let s = addFieldWriteSideEffect objectParam (FieldOrElement.FieldRef field) value
            expr, s
        | (Some _) ->
            expr, (fun condition state ->
                let hobj = state.Assumptions.Heap.[objectParam.Value]
                let newValue =
                    (
                    if condition = SExpr.ImmConstant true then
                        value
                    else
                        let currentValue = hobj.Fields.TryGet field |> Option.defaultWith (fun () -> SExpr.LdField field (Some (SExpr.Parameter objectParam.Value)))
                        SExpr.Condition condition value currentValue
                    ) |> ExprSimplifier.simplify state.Assumptions
                // match newValue.Node with
                // | SExprNode.InstructionCall (InstructionFunction.Add, _, EqArray.AP [ { Node = SExprNode.Constant (:? int as c) }; rest ]) when c = -1640531527 ->
                //     waitForDebug()
                // | _ -> ()
                let hobj = { hobj with Fields = hobj.Fields.SetItem(field, newValue) }
                state.ChangeObject [ objectParam.Value, hobj ]
            )
        | _ ->
            // TODO: support this - create a new object, assign it to the field and assign a field on the object
            failwithf "Can't assign to field on non-object, expr = %A, heap objects = %A" hobj (List.ofSeq (state.Assumptions.Heap.Keys |> Seq.map (fun p -> p.Name)))
    )
    s (SExpr.ImmConstant true) state

let setElement target index value state =
    assertDecidableArgs [target; value]
    let elType = (target.ResultType.Reference :?> Mono.Cecil.ArrayType).ElementType |> TypeRef
    let value = stackConvert value elType
    let _, s = target |> accessObjectProperty (fun expr objectParam ->
        let hobj = objectParam |> Option.bind (state.Assumptions.Heap.TryGet)
        match hobj with
        | (Some hobj) when hobj.IsShared <> SExpr.ImmConstant false ->
            // side effect...
            let s = addFieldWriteSideEffect objectParam (FieldOrElement.ElementRef (index, elType)) value
            expr, s
        | (Some _) ->
            expr, (fun condition state ->
                let hobj = state.Assumptions.Heap.[objectParam.Value]
                softAssert hobj.Array.IsSome "Object must be array for indexing"
                let array = hobj.Array.Value
                let newValue =
                    if condition = SExpr.ImmConstant true then
                        value
                    else
                        let currentValue = getArrayElement array index
                        SExpr.Condition condition value currentValue |> ExprSimplifier.simplify state.Assumptions
                let newArray =
                    match index.Node with
                    | SExprNode.Constant ( :? int as index) ->
                        { array with Constants = array.Constants.SetItem(index, newValue) }
                    | _ ->
                        let gExpr = getArrayElement array (SExpr.Parameter InterpreterState.indexParameter)
                        { array with
                            GeneralExpression =
                                (SExpr.Condition
                                    (SExpr.InstructionCall InstructionFunction.C_Eq CecilTools.boolType [index; SExpr.Parameter InterpreterState.indexParameter])
                                    newValue
                                    gExpr
                                 |> ExprSimplifier.simplify state.Assumptions)
                            Constants = dict<_, _>.Empty }

                let hobj = { hobj with Array = Some newArray }
                state.ChangeObject [ objectParam.Value, hobj ]
            )
        | _ ->
            // TODO: support this - create a new object, assign it to the field and assign a field on the object
            failwithf "Can't assign to field on non-object, expr = %A, heap objects = %A" hobj (List.ofSeq (state.Assumptions.Heap.Keys |> Seq.map (fun p -> p.Name)))
    )
    s (SExpr.ImmConstant true) state

let accessStaticField field state =
    let result, s = addFieldReadSideEffect None (FieldOrElement.FieldRef field)
    SExpr.Parameter result, s (SExpr.ImmConstant true) state

let setStaticField field value state =
    addFieldWriteSideEffect None (FieldOrElement.FieldRef field) value (SExpr.ImmConstant true) state

let readLValue (expr: SLExprNode) (state: ExecutionState) =
    match expr with
    | SLExprNode.Parameter p ->
        if state.Locals.ContainsKey p then
            state.Locals.[p], state
        else
            SExpr.Parameter p, state
    | SLExprNode.LdField (field, Some target) ->
        accessField target (FieldOrElement.FieldRef field) state
    | SLExprNode.LdField (field, None) ->
        accessStaticField field state
    | SLExprNode.LdElement (target, index) ->
        accessField target (FieldOrElement.ElementRef(index, (target.ResultType.Reference :?> Mono.Cecil.ArrayType).ElementType |> TypeRef)) state
    | _ -> failwithf "Can't read LValue, expression of type %O" (expr.GetType())
let dereference (expr: SExpr) (state: ExecutionState) =
    match expr.Node with
    | SExprNode.Reference lv -> readLValue lv state
    | _ ->
        tooComplicated (sprintf "Can't deref node %O" expr)

let setLValue (expr: SLExprNode) (value: SExpr) (state: ExecutionState) =
    match expr with
    | SLExprNode.Parameter p ->
        if state.Locals.ContainsKey p then
            { state with Locals = state.Locals.SetItem(p, value) }
        else
            tooComplicated (sprintf "Can't assign to parameter %s" p.Name)
    | SLExprNode.LdField (field, Some target) ->
        setField target field value state
    | SLExprNode.LdField (field, None) ->
        setStaticField field value state
    | SLExprNode.LdElement (target, index) ->
        setElement target index value state
    | _ -> failwithf "Can't read LValue, expression %A" expr

let setReference (expr: SExpr) (value: SExpr) (state: ExecutionState) =
    softAssert (expr.ResultType = TypeRef.CreateByref value.ResultType) "Reference and value don't fit"
    match expr.Node with
    | SExprNode.Reference lv -> setLValue lv value state
    | _ ->
        tooComplicated (sprintf "Can't deref node %O" expr)

let rec makeReference (expr: SExpr) =
    match expr.Node with
    | SExprNode.Condition (c, a, b) ->
        SExpr.Condition c (makeReference a) (makeReference b)
    | SExprNode.LValue lv -> SExpr.Reference expr.ResultType lv
    | _ -> failwithf "Can't make reference of %O" expr