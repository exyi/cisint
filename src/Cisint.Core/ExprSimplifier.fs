module ExprSimplifier
open System.Collections.Immutable
open System.Reflection
open Expression
open Mono.Cecil
open System.Collections.Generic
open System.Linq
open InterpreterState
open System.Collections.Generic
open TypesystemDefinitions
open Cisint.DynamicEvaluator

type SimplifierPattern = {
    Variables: SParameter array
    TypeVars: TypeRef array
    EqExpressions: (SExpr) array
}

module QP = Quotations.Patterns

let createExprFromQuot (quotation: Quotations.Expr) (parameters: #seq<_>) =
    let rec stripLambdas q =
        match q with
        | QP.Lambda (var, body) ->
            let (vars, body) = stripLambdas body
            var::vars, body
        | a -> [], a
    let vars, quotationbody = stripLambdas quotation

    let typeAliases = Seq.map2 (fun (v: Quotations.Var) (t: SParameter) -> if t.Type = CecilTools.generalSentinelType then Some (KeyValuePair(v.Type, t.Type)) else None) vars parameters |> Seq.choose id |> ImmutableDictionary.CreateRange
    let convertType t =
        typeAliases.TryGet t |> Option.defaultWith (fun () -> CecilTools.convertType t)

    let rec translate (aliases: Map<_, _>) q =
        match q with
        | QP.Var v when aliases.ContainsKey v -> aliases.[v]
        | QP.Let (var, value, next) ->
            let v = translate aliases value
            translate (Map.add var v aliases) next
        | QP.Call (target, m, args) ->
            let target = Option.map (translate aliases) target
            let args = List.map (translate aliases) args
            let instuctionFunction =
                if m.DeclaringType.FullName = "Microsoft.FSharp.Core.Operators" then
                    match m.Name with
                    | "op_Addition" -> Some InstructionFunction.Add
                    | "op_Subtraction" -> Some InstructionFunction.Sub
                    | "op_Multiply" -> Some InstructionFunction.Mul
                    | "op_Division" -> Some InstructionFunction.Div
                    | "op_Modulus" -> Some InstructionFunction.Rem
                    | "Box" -> Some InstructionFunction.Box
                    | "Unbox" -> Some InstructionFunction.Unbox
                    | "op_BitwiseAnd" -> Some InstructionFunction.And
                    | "op_BitwiseOr" -> Some InstructionFunction.Or
                    | "op_LogicalNot" | "Not" -> Some InstructionFunction.Not
                    | "op_UnaryNegation" -> Some InstructionFunction.Negate
                    | "op_ExclusiveOr" -> Some InstructionFunction.Xor
                    | "op_LeftShift" -> Some InstructionFunction.Shl
                    | "op_RightShift" -> Some InstructionFunction.Shr
                    | "op_LessThan" -> Some InstructionFunction.C_Lt
                    | "op_Equality" -> Some InstructionFunction.C_Eq
                    | "op_GreaterThan" -> Some InstructionFunction.C_Gt
                    | "UnboxGeneric" -> Some InstructionFunction.Cast
                    | "Not" -> Some InstructionFunction.Not
                    | a when a.StartsWith "To" -> Some InstructionFunction.Convert
                    | _ -> failwith "nevim jak"
                elif m.IsGenericMethod && m.GetGenericMethodDefinition() = typeof<Marker>.DeclaringType.GetMethod("castAs") then
                    Some InstructionFunction.IsInst
                elif m = typeof<Marker>.DeclaringType.GetMethod("justOr") then
                    Some InstructionFunction.Or
                elif m = typeof<Marker>.DeclaringType.GetMethod("justAnd") then
                    Some InstructionFunction.And
                else
                    None
            match instuctionFunction with
            | Some i ->
                SExpr.InstructionCall i (convertType m.ReturnType) (IArray.ofSeq args)
            | _ ->
                SExpr.PureCall (CecilTools.convertMethodInfo m) (List.append (Option.toList target) args |> IArray.ofSeq)
        | QP.TupleGet (var, index) ->
            let f = var.Type.GetField("m_Item" + string index, BindingFlags.Instance ||| BindingFlags.NonPublic)
            SExpr.LdField (CecilTools.convertFieldInfo f) (Some <| translate aliases var)
        | QP.FieldGet (var, f) ->
            SExpr.LdField (CecilTools.convertFieldInfo f) (Option.map (translate aliases) var)
        | QP.Value (value, vtype) ->
            SExpr.New (CecilTools.convertType vtype) (SExprNode.Constant value)
        | QP.IfThenElse (c, a, b) ->
            SExpr.Condition (translate aliases c) (translate aliases a) (translate aliases b)
        | _ -> failwithf "Not supported quotation: %A" q

    let aliases = Seq.zip vars (parameters |> Seq.map SExpr.Parameter) |> Map.ofSeq

    translate aliases quotationbody

let createPattern (parameters: #seq<TypeRef>) (patterns: #seq<array<SParameter> -> SExpr>) =
    let p = parameters |> IArray.ofSeq |> IArray.mapi (fun index a -> SParameter.New a (sprintf "p%d" index))
    let exprs = patterns |> IArray.ofSeq |> IArray.map (fun f -> f p)
    { SimplifierPattern.Variables = p
      TypeVars = if p |> Seq.exists (fun p -> p.Type = CecilTools.generalSentinelType) then
                     IArray.ofSeq [CecilTools.generalSentinelType]
                 else
                     array<_>.Empty
      EqExpressions = exprs }

let createPatternFromQuot (parameters: #seq<System.Type>) (patterns: #seq<Quotations.Expr>) =
    createPattern (Seq.map CecilTools.convertType parameters) (Seq.map createExprFromQuot patterns)

let private assignTypeParam (typeParameter: TypeRef) (assignee: TypeRef) =
    let rec v = SExpr.Visitor (fun node visitChildren ->
        let node = visitChildren node
        if node.ResultType = typeParameter then
            Some { node with ResultType = assignee }
        else
            Some node
    )
    v

let private mergeAssignments (a: #seq<(SExpr option) array>) =
    let a = IArray.ofSeq a
    let (length, _) = a |> Seq.countBy(fun t -> t.Length) |> Seq.exactlyOne
    let mutable ok = true
    let result = IArray.init length (fun i ->
        let b = a |> Seq.choose(fun b -> b.[i]) |> Seq.distinct |> Seq.toArray
        if b.Length = 1 then
            Some b.[0]
        elif b.Length = 0 then
            None
        else
            ok <- false
            None
    )
    if ok then Ok result else Error ()

/// Returns resolved variables of the pattern based on the provided expression
let rec patternMatch (expr: SExpr) (pattern: SExpr) (vars: SParameter array) (typeVars: TypeRef array) : Result<(SExpr option) array, unit> =
    let recurse (args: (SExpr * SExpr) seq) =
        Seq.foldBack (fun (e, p) state ->
            state |> Result.bind (fun state_p ->
                patternMatch e p vars typeVars |> Result.map (fun r -> r :: state_p)
            )
        ) args (Ok []) |> Result.bind mergeAssignments

    let pattern =
        if typeVars.Contains(pattern.ResultType) then
            assignTypeParam pattern.ResultType expr.ResultType pattern
        else
            pattern
    match pattern with
    | _ when pattern.ResultType <> expr.ResultType ->
        Error ()
    | { SExpr.Node = (SExprNode.LValue (SLExprNode.Parameter p)); } ->
        Ok (vars |> IArray.map (fun t -> if t = p then Some expr else None))
    | _ ->
        let procLValue expr pattern =
            match (expr, pattern) with
            | (SLExprNode.Dereference e, SLExprNode.Dereference e_p) ->
                recurse [ e, e_p ]
            | (SLExprNode.LdField (field, Some e), SLExprNode.LdField (field_p, Some e_p))
                when field = field_p ->
                recurse [ e, e_p ]
            | (SLExprNode.LdElement (target, index), SLExprNode.LdElement (target_p, index_p)) ->
                recurse [ target, target_p ; index, index_p ]
            | _ -> Error ()
        match (expr.Node, pattern.Node) with
        | (n, p) when n = p -> Ok (vars |> IArray.map (fun _ -> None))
        | (SExprNode.Condition (cond, ifTrue, ifFalse), SExprNode.Condition (cond_p, ifTrue_p, ifFalse_p)) ->
            recurse [
                cond, cond_p
                ifTrue, ifTrue_p
                ifFalse, ifFalse_p
            ]
        | (SExprNode.InstructionCall (instruction, itype, args), SExprNode.InstructionCall(instruction_p, itype_p, args_p))
            when instruction = instruction_p && itype = itype_p && args.arr.Length = args_p.arr.Length ->
            recurse (Seq.zip args.arr args_p.arr)
        | (SExprNode.PureCall (method, args), SExprNode.PureCall (method_p, args_p))
            when method = method_p && args.arr.Length = args_p.arr.Length ->
            recurse (Seq.zip args.arr args_p.arr)
        | (SExprNode.LValue lv, SExprNode.LValue lv_p) -> procLValue lv lv_p
        | (SExprNode.Reference lv, SExprNode.Reference lv_p) -> procLValue lv lv_p
        | _ -> Error ()

/// Asssigns symbolic parameters of the expression using the specified function
let assignParameters (mapping: SParameter -> SExpr option) =
    SExpr.Visitor (fun e visitChildren ->
        match e.Node with
        | LValue (Parameter a) | Reference (Parameter a) ->
            mapping a
        | _ -> None
    )

/// (from, to) set
let private lossLessConversions =
    new HashSet<struct (TypeRef * TypeRef)>(
        [
            struct (CecilTools.boolType, CecilTools.intType)
            struct (CecilTools.convertType typeof<System.Byte>, CecilTools.intType)
            struct (CecilTools.convertType typeof<System.SByte>, CecilTools.intType)
            struct (CecilTools.convertType typeof<System.Int16>, CecilTools.intType)
            struct (CecilTools.convertType typeof<System.UInt16>, CecilTools.intType)
            struct (CecilTools.convertType typeof<System.UInt32>, CecilTools.intType)
            struct (CecilTools.intType, CecilTools.convertType typeof<System.UInt32>)
            struct (CecilTools.convertType typeof<System.UInt64>, CecilTools.convertType typeof<System.Int64>)
            struct (CecilTools.convertType typeof<System.Int64>, CecilTools.convertType typeof<System.UInt64>)
            struct (CecilTools.convertType typeof<System.Int16>, CecilTools.convertType typeof<System.UInt16>)
            struct (CecilTools.convertType typeof<System.UInt16>, CecilTools.convertType typeof<System.Int16>)
            struct (CecilTools.convertType typeof<System.Byte>, CecilTools.convertType typeof<System.SByte>)
            struct (CecilTools.convertType typeof<System.SByte>, CecilTools.convertType typeof<System.Byte>)
            struct (CecilTools.intType, CecilTools.nintType)
            struct (CecilTools.intType, CecilTools.nuintType)
            struct (CecilTools.nintType, CecilTools.convertType typeof<System.Int64>)
            struct (CecilTools.nuintType, CecilTools.convertType typeof<System.Int64>)
            struct (CecilTools.nuintType, CecilTools.convertType typeof<System.UInt64>)
        ])
let isDownCast (fromType: TypeRef) (toType: TypeRef) =
    fromType.BaseTypeChain.Contains toType || toType.Interfaces.Contains toType
let findCommonAncestor (a: TypeRef) (b: TypeRef) =
    let (cA, cB) = List.rev a.BaseTypeChain, List.rev b.BaseTypeChain
    Seq.init (min cA.Length cB.Length) (fun i -> (cA.[i], cB.[i])) |> Seq.tryFindBack (fun (a, b) -> a = b) |> Option.map fst

let private convertTo (t: TypeRef) isChecked =
    let reflectionType = System.Type.GetType t.FullName
    let invoke =
        if reflectionType <> typeof<bool> then
            let method = typeof<Evaluator>.GetMethod(if isChecked then "ConvertToChecked" else "ConvertTo").MakeGenericMethod([|reflectionType|])
            fun a -> method.Invoke(null, [|a|])
        else
            fun (a: obj) -> System.Convert.ToBoolean a |> box
    fun a ->
        let a =
            if isNull a then box 0
            elif (true).Equals(a) then box 1
            elif (false).Equals(a) then box 0
            elif not (a.GetType().IsPrimitive) then box 1
            else a
        invoke a
// let private castAs (t: TypeRef) throwOnFail =
//     let reflectionType = System.Type.GetType t.FullName
//     let method = typeof<Evaluator>.GetMethod(if checked then "Cast" else "ConvertTo").MakeGenericMethod([|reflectionType|])
//     fun a -> method.Invoke(null, [|a|])
let private executeConstantInstruction i resultType (args: obj array) =
    match i with
    | InstructionFunction.Add -> Evaluator.Add(args.[0], args.[1])
    | InstructionFunction.And -> Evaluator.And(args.[0], args.[1])
    | InstructionFunction.C_Eq -> Evaluator.Eq(args.[0], args.[1]) |> box
    | InstructionFunction.C_Gt -> Evaluator.GreaterThan(args.[0], args.[1]) |> box
    | InstructionFunction.C_Lt -> Evaluator.LessThan(args.[0], args.[1]) |> box
    | InstructionFunction.Div -> Evaluator.Divide(args.[0], args.[1])
    | InstructionFunction.Mul -> Evaluator.Multiply(args.[0], args.[1])
    | InstructionFunction.Or -> Evaluator.Or(args.[0], args.[1])
    | InstructionFunction.Rem -> Evaluator.Rem(args.[0], args.[1])
    | InstructionFunction.Shl -> Evaluator.Shl(args.[0], args.[1])
    | InstructionFunction.Shr -> Evaluator.Shr(args.[0], args.[1])
    | InstructionFunction.Sub -> Evaluator.Sub(args.[0], args.[1])
    | InstructionFunction.Xor -> Evaluator.Xor(args.[0], args.[1])
    | InstructionFunction.Negate -> Evaluator.Negate(args.[0])
    | InstructionFunction.BitNot -> Evaluator.BitNot(args.[0])
    | InstructionFunction.Not -> box(not(unbox args.[0]))
    | InstructionFunction.Box -> args.[0]
    | InstructionFunction.Convert -> convertTo resultType false args.[0]
    | InstructionFunction.Convert_Checked -> convertTo resultType true args.[0]
    | (InstructionFunction.Cast | InstructionFunction.IsInst) when isNull args.[0] -> null
    | (InstructionFunction.Cast | InstructionFunction.IsInst) when resultType = CecilTools.objType -> args.[0]
    | (InstructionFunction.Cast | InstructionFunction.IsInst) when isDownCast (args.[0].GetType() |> CecilTools.convertType) resultType -> args.[0]
    | (InstructionFunction.IsInst) -> null
    | _ ->
        failwithf "Unsupported constant folding - %O %A : %O" i args resultType

let private simplifyHardcoded (assumptions: AssumptionSet) (expr: SExpr) =
    match expr.Node with
    // constant folding
    | SExprNode.InstructionCall (i, resultT, args) when args.arr |> IArray.forall (fun a -> match a.Node with SExprNode.Constant _ -> true | _ -> false) ->
        let args = args.arr |> IArray.map (fun a -> match a.Node with SExprNode.Constant a -> a | _ -> failwith "wtf")
        let result = executeConstantInstruction i resultT args
        SExpr.New expr.ResultType (SExprNode.Constant result)
    // conversion to and back
    | SExprNode.InstructionCall (InstructionFunction.Convert, convertTo, EqArray.AP [ { Node = SExprNode.InstructionCall(InstructionFunction.Convert, convertFrom, EqArray.AP [insideExpr]) } as convExpr ])
        when convertTo = insideExpr.ResultType && lossLessConversions.Contains (struct (convertTo, convertFrom)) ->
        SExpr.Cast InstructionFunction.Convert convertTo insideExpr
    // take only outer conversion
    | SExprNode.InstructionCall ((InstructionFunction.Cast | InstructionFunction.IsInst | InstructionFunction.Box) as ifc, castTo, EqArray.AP [ { Node = SExprNode.InstructionCall((InstructionFunction.Cast | InstructionFunction.IsInst | InstructionFunction.Box), castFrom, EqArray.AP [insideExpr]) } as convExpr ])
        when isDownCast convExpr.ResultType castFrom || not(isDownCast castFrom castTo) ->
        SExpr.Cast ifc castTo insideExpr
    // redundant conversions and casts
    | SExprNode.InstructionCall ((InstructionFunction.Convert | InstructionFunction.Cast | InstructionFunction.IsInst), convertTo, EqArray.AP [ insideExpr ])
        when insideExpr.ResultType = convertTo ->
        insideExpr
    // propagate unary expressions into conditionals
    | SExprNode.InstructionCall (ifc, resultType, EqArray.AP [ { Node = SExprNode.Condition (condition, ifTrue, ifFalse) } as _innerNode ]) ->
        SExpr.Condition condition (SExpr.InstructionCall ifc resultType [ifTrue]) (SExpr.InstructionCall ifc resultType [ifFalse])
    // boxing reference type is like a downcast
    | SExprNode.InstructionCall (InstructionFunction.Box, resultType, EqArray.AP [ arg ]) when arg.ResultType.IsObjectReference ->
        softAssert (resultType = CecilTools.objType) "Boxing to non-object type."
        SExpr.Cast InstructionFunction.Cast resultType arg
    // downcast will always use Cast instruction
    | SExprNode.InstructionCall (InstructionFunction.IsInst, resultType, EqArray.AP [ arg ]) when arg.ResultType.IsObjectReference && isDownCast arg.ResultType resultType ->
        SExpr.Cast InstructionFunction.Cast resultType arg
    // reference comparison with conversions
    | SExprNode.InstructionCall (InstructionFunction.C_Eq as ifc, resultType, EqArray.AP [
            { Node = SExprNode.InstructionCall (InstructionFunction.Cast, _, EqArray.AP [expr1]) } as cast1
            { Node = SExprNode.InstructionCall (InstructionFunction.Cast, _, EqArray.AP [expr2]) } as cast2
        ]) when isDownCast expr1.ResultType cast1.ResultType && isDownCast expr2.ResultType cast2.ResultType ->
        match findCommonAncestor expr1.ResultType expr2.ResultType with
        | Some commonCast ->
            SExpr.InstructionCall ifc resultType [ SExpr.Cast InstructionFunction.Cast commonCast expr1; SExpr.Cast InstructionFunction.Cast commonCast expr2 ]
        | _ -> expr
    // cast and null compare
    | SExprNode.InstructionCall (InstructionFunction.C_Eq, _, EqArray.AP [
            { Node = SExprNode.Constant null } as nullLiteral
            { Node = SExprNode.InstructionCall ((InstructionFunction.Cast | InstructionFunction.IsInst | InstructionFunction.Box), _, EqArray.AP [expr2]) } as cast
        ]) when isDownCast expr2.ResultType cast.ResultType ->
        SExpr.InstructionCall InstructionFunction.C_Eq CecilTools.boolType [ SExpr.New expr2.ResultType (SExprNode.Constant null); expr2 ]
    // null compare -> bool cast
    | SExprNode.InstructionCall (InstructionFunction.C_Eq, _, EqArray.AP [ { Node = SExprNode.Constant null } as nullLiteral; e ])
    | SExprNode.InstructionCall (InstructionFunction.C_Eq, _, EqArray.AP [ e; { Node = SExprNode.Constant null } as nullLiteral ]) ->
        if e.ResultType.Definition.IsValueType then
            SExpr.ImmConstant false
        else
            SExpr.Cast InstructionFunction.Convert CecilTools.boolType e |> SExpr.BoolNot
    // obj -> bool cast unwrap
    | SExprNode.InstructionCall (InstructionFunction.Convert, rBool, EqArray.AP [ { Node = SExprNode.InstructionCall ((InstructionFunction.Cast | InstructionFunction.Box | InstructionFunction.IsInst), _, EqArray.AP [ e ]) } as cast ]) when rBool = CecilTools.boolType && isDownCast e.ResultType cast.ResultType ->
        if e.ResultType.Definition.IsValueType then
            SExpr.ImmConstant true
        else SExpr.Cast InstructionFunction.Convert CecilTools.boolType e
    // null check
    | SExprNode.InstructionCall (InstructionFunction.Convert, rBool, EqArray.AP [ { Node = SExprNode.LValue (SLExprNode.Parameter p) } as pExpr ])
        when
            rBool = CecilTools.boolType &&
                (match assumptions.Heap.TryGet(p) with
                 | Some (hobj) -> hobj.TypeIsDefinite
                 | None -> false
             ) ->
        SExpr.ImmConstant true
    | SExprNode.InstructionCall (InstructionFunction.IsInst, resultType, EqArray.AP [ { Node = SExprNode.LValue (SLExprNode.Parameter p) } as pExpr ])
        when assumptions.Heap.ContainsKey p ->
        let hobj = assumptions.Heap.[p]
        if hobj.TypeIsDefinite then
            // downcast is catched by other pattern
            SExpr.New resultType (SExprNode.Constant null)
        elif hobj.Type.BaseType.IsSome && resultType.BaseType.IsSome && not (resultType.BaseTypeChain.Contains hobj.Type) then
            SExpr.New resultType (SExprNode.Constant null)
        else
            expr
    // expression in assumptions is true
    | _ when expr.ResultType = CecilTools.boolType && assumptions.Set.Contains expr -> SExpr.ImmConstant true
    | _ -> expr

let private getExprBaseKey =
    let getLValueKey =
        function
        | SLExprNode.Parameter _ -> "p"
        | SLExprNode.Dereference _ -> "d"
        | SLExprNode.LdElement _ -> "lde"
        | SLExprNode.LdField _ -> "ldf"
    function
    | SExprNode.Constant _ -> "c"
    | SExprNode.Condition _ -> "if"
    | SExprNode.LValue lv -> "lv_" + getLValueKey lv
    | SExprNode.Reference lv -> "rf_" + getLValueKey lv
    | SExprNode.PureCall (method, _) -> "pc_" + (string method.Reference.MetadataToken.RID)
    | SExprNode.InstructionCall (i, _, _) -> "ic_" + string i

type private PatternMap = {
    /// key is a rough shape of the expression (result of getExprBaseKey)
    /// value is an array of pattern-expression and it's equivalents
    PatternMap: Dictionary<string, (SExpr * SimplifierPattern)[]>
}

/// Returns all equivalent expressions according to the pattern map
let private execPatterns patternMap expr =
    let lookupKey = getExprBaseKey expr.Node
    match patternMap.PatternMap.TryGetValue lookupKey with
    | (false, _) -> Seq.empty
    | (true, pts) ->
        pts |> Seq.collect (fun (patternExpression, patternInfo) ->
            let m = patternMatch expr patternExpression patternInfo.Variables patternInfo.TypeVars
            match m with
            | Ok (resolvedVars) ->
                let resolvedVars = Enumerable.ToDictionary(resolvedVars |> Seq.mapi(fun index var -> (patternInfo.Variables.[index], var)), fst, snd)
                patternInfo.EqExpressions |> IArray.choose (fun eqExpr ->
                    if eqExpr = patternExpression then None
                    else
                        let mutable ok = true
                        let assigned =
                            assignParameters (fun p ->
                                match resolvedVars.TryGetValue(p) with
                                | (true, Some assigned) -> Some assigned
                                | (true, None) -> ok <- false; None
                                | (false, _) -> None
                            ) eqExpr
                        let typeParams = patternInfo.TypeVars
                                         |> IArray.map (fun x ->
                                             let (KeyValue (_, Some a)) = resolvedVars |> Seq.find (fun (KeyValue(k, v)) -> k.Type = x && v.IsSome)
                                             (x, a.ResultType)
                                         )
                        let assigned = Seq.fold (fun e (paramType, argType) -> assignTypeParam paramType argType e) assigned typeParams

                        if ok then Some assigned else None
                )
            | _ -> array<_>.Empty
        )

let rec private simplifyHardcodedM (assumptions: AssumptionSet) expr =
    let expr_t = (simplifyHardcoded assumptions expr)
    if System.Object.ReferenceEquals(expr_t, expr) || expr_t = expr then
        expr
    else simplifyHardcodedM assumptions expr_t
let rec private simplifyPatternsOneLevel (map: PatternMap) (assumptions: AssumptionSet) expr =
    let p = execPatterns map expr
            //|> fun a -> printfn "\t\texecuting patterns for %s, got %d" (ExprFormat.exprToString expr_s) (Seq.length a); a
            |> Seq.append [expr]
            |> Seq.reduce (ExprCompare.exprMin)
    if System.Object.ReferenceEquals(p, expr) || p = expr then
        expr
    else simplifyPatternsOneLevel map assumptions p

let private simplifyExpressionCore (map: PatternMap) (assumptions: AssumptionSet) a =
    // printfn "\t simplifying %s" (ExprFormat.exprToString a)
    SExpr.Visitor (fun expr visitChildren ->
        match expr.SimplificationVersion with
        | (AssumptionSetVersion a) when a < assumptions.Version.Num || a = -1L ->
            let expr_s = simplifyHardcodedM assumptions expr |> visitChildren |> simplifyHardcodedM assumptions
            Some (simplifyPatternsOneLevel map assumptions expr_s)
        | _ ->
            Some expr
    ) a

let rec private simplifyExpression map assumptions a =
    let s = simplifyExpressionCore map assumptions a
    // if ExprCompare.exprCompare s a > 0 then
    //     failwithf "WTF, %s was \"simplified\" into %s" (ExprFormat.exprToString a) (ExprFormat.exprToString s)
    if System.Object.ReferenceEquals(s, a) || s = a then
        s
    else
        simplifyExpression map assumptions s

let private emptyPattern = SExpr.ImmConstant 1, {SimplifierPattern.EqExpressions = array<_>.Empty; TypeVars = array<_>.Empty; Variables = array<_>.Empty}

let rec private buildPatternMap (patterns: seq<SimplifierPattern>) =
    // printfn "building pattern map..."
    let items =
        patterns
        |> Seq.collect (fun p -> p.EqExpressions |> Seq.map (fun e -> (e, p)))
        |> Seq.filter (fun (baseExpr, _) ->
            match baseExpr.Node with
            | SExprNode.LValue (SLExprNode.Parameter _) -> false // blacklist "tree leaves"
            | SExprNode.Constant _ -> false
            | _ -> true
        )
        |> Seq.groupBy (fun (a, _) -> getExprBaseKey a.Node)
        |> fun a -> Enumerable.ToDictionary(a, fst, snd >> Array.ofSeq)
    let emptyAssumptions = { AssumptionSet.empty with Version = AssumptionSetVersion.None }
    let patternMap = { PatternMap = items }
    let mutable anythingNew = false
    let newPatterns =
        patterns
        |> IArray.ofSeq
        |> IArray.map (fun p ->
            let exprKeys = p.EqExpressions
                          |> Seq.choose (fun e ->
                                   let key = getExprBaseKey e.Node

                                   if items.ContainsKey key |> not then None
                                   else

                                   let index = items.[key] |> Array.findIndex (fun (t, _) -> System.Object.ReferenceEquals(t, e))
                                   Some (key, index, items.[key].[index])
                              )
                          |> Seq.toArray
            for (k, index, _) in exprKeys do
                items.[k].[index] <- emptyPattern // remove the pattern itself in order to simplify it.

            let expressions = p.EqExpressions |> IArray.map (simplifyExpression patternMap emptyAssumptions)

            for (k, index, item) in exprKeys do
                items.[k].[index] <- item

            let newExpressions = Seq.except p.EqExpressions expressions
            let allExpressions = Seq.append p.EqExpressions newExpressions |> IArray.ofSeq
            if allExpressions.Length = expressions.Length then
                p
            else
            anythingNew <- true
            { p with EqExpressions = allExpressions }
        )
    if not anythingNew then
        patternMap
    else
        buildPatternMap (newPatterns :> seq<_>)

/// Adds more patterns based on the other patterns
let extendPatterns (patterns: #seq<SimplifierPattern>) =
    let pmap = buildPatternMap patterns
    pmap.PatternMap.Values |> Seq.concat |> Seq.map snd |> Seq.distinct
let createSimplifier (patterns: #seq<SimplifierPattern>) =
    let pmap = buildPatternMap patterns
    simplifyExpression pmap

let defaultPatterns = [
    createPatternFromQuot
        [ typeof<bool>; typeof<bool> ]
        [ <@ fun a b -> not (justAnd a b) @>; <@ fun a b -> justOr (not a) (not b) @> ]
    // bool commutativity
    createPatternFromQuot
        [ typeof<bool>; typeof<bool> ]
        [ <@ fun a b -> justAnd a b @>; <@ fun a b -> justAnd b a @> ]
    createPatternFromQuot
        [ typeof<bool>; typeof<bool> ]
        [ <@ fun a b -> justOr a b @>; <@ fun a b -> justOr b a @> ]
    // bool asiciativity
    createPatternFromQuot
        [ typeof<bool>; typeof<bool>; typeof<bool> ]
        [ <@ fun a b c -> justAnd a (justAnd b c) @>; <@ fun a b c -> justAnd (justAnd a b) c @> ]
    createPatternFromQuot
        [ typeof<bool>; typeof<bool>; typeof<bool> ]
        [ <@ fun a b c -> justOr a (justOr b c) @>; <@ fun a b c -> justOr (justOr a b) c @> ]
    // bool distribitivity `a & (b | c)` and `a | (b & c)`
    createPatternFromQuot
        [ typeof<bool>; typeof<bool>; typeof<bool> ]
        [ <@ fun a b c -> justAnd a (justOr b c) @>; <@ fun a b c -> justOr (justAnd a b) (justAnd a c) @> ]
    createPatternFromQuot
        [ typeof<bool>; typeof<bool>; typeof<bool> ]
        [ <@ fun a b c -> justOr a (justAnd b c) @>; <@ fun a b c -> justAnd (justOr a b) (justOr a c) @> ]
    // bool `true & a`, and so on
    createPatternFromQuot
        [ typeof<bool> ]
        [ <@ fun a -> justAnd true a @>; <@ fun a -> a @> ]
    createPatternFromQuot
        [ typeof<bool> ]
        [ <@ fun a -> justAnd false a @>; <@ fun a -> false @> ]
    createPatternFromQuot
        [ typeof<bool> ]
        [ <@ fun a -> justOr false a @>; <@ fun a -> a @> ]
    createPatternFromQuot
        [ typeof<bool> ]
        [ <@ fun a -> justOr true a @>; <@ fun a -> true @> ]
    createPatternFromQuot
        [ typeof<bool> ]
        [ <@ fun a -> not (not a) @>; <@ fun a -> justOr a a @>; <@ fun a -> justAnd a a @>; <@ fun a -> a @> ]

    // generic if-conversions
    createPatternFromQuot
        [ typeof<bool>; typeof<CecilTools.GeneralSentinelType>;typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun c a b -> if c then a else b @>; <@ fun c a b -> if not c then b else a @> ]
    createPatternFromQuot
        [ typeof<bool>; typeof<CecilTools.GeneralSentinelType>; ]
        [ <@ fun c a -> if c then a else a @>; <@ fun _ a -> a @> ]
    createPatternFromQuot
        [ typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun a b -> if true then a else b @>; <@ fun a _ -> a @>; <@ fun a b -> if false then b else a @> ]

    // general comparison conversions
    createPatternFromQuot
        [ typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun a b -> a < b @>; <@ fun a b -> b > a @> ]
    createPatternFromQuot
        [ typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun a b -> a = b @>; <@ fun a b -> b = a @> ]
    createPatternFromQuot
        [ typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun a -> a = a @>; <@ fun _ -> true @> ]

    // basic arithmetics
    // these should work for floats too
    createPatternFromQuot
        [ typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun a b -> a + b @>; <@ fun a b -> b + a @> ]
    createPatternFromQuot
        [ typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun a b -> a - b @>; <@ fun a b -> a + (-b) @> ]
    createPatternFromQuot
        [ typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun a b -> a * b @>; <@ fun a b -> b * a @> ]
    createPatternFromQuot
        [ typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun a b -> -a + -b @>; <@ fun a b -> -(a + b) @> ]
    // TODO: this does not work for floats
    createPatternFromQuot
        [ typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun a b c -> a + (b + c) @>; <@ fun a b c -> (a + b) + c @> ]
    createPatternFromQuot
        [ typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType>; typeof<CecilTools.GeneralSentinelType> ]
        [ <@ fun a b c -> a * (b * c) @>; <@ fun a b c -> (a * b) * c @> ]
]

let simplify = createSimplifier defaultPatterns