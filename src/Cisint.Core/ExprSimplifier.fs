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

type SimplifierPattern = {
    Variables: SParameter array
    TypeVars: TypeRef array
    EqExpressions: (SExpr) array
}

module QP = Quotations.Patterns

let createExprFromQuot (quotation: Quotations.Expr) (parameters: #seq<_>) =
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
                SExpr.InstructionCall i (CecilTools.convertType m.ReturnType) (ImmutableArray.CreateRange args)
            | _ ->
                SExpr.PureCall (CecilTools.convertMethodInfo m) (List.append (Option.toList target) args |> ImmutableArray.CreateRange)
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

    let rec stripLambdas q =
        match q with
        | QP.Lambda (var, body) ->
            let (vars, body) = stripLambdas body
            var::vars, body
        | a -> [], a
    let vars, quotationbody = stripLambdas quotation

    let aliases = Seq.zip vars (parameters |> Seq.map SExpr.Parameter) |> Map.ofSeq

    translate aliases quotationbody

let createPattern (parameters: #seq<TypeRef>) (patterns: #seq<array<SParameter> -> SExpr>) =
    let p = parameters |> IArray.ofSeq |> IArray.mapi (fun index a -> SParameter.New a (sprintf "p%d" index))
    let exprs = patterns |> IArray.ofSeq |> IArray.map (fun f -> f p)
    { SimplifierPattern.Variables = p; TypeVars = array<_>.Empty; EqExpressions = exprs }

let createPatternFromQuot (parameters: #seq<System.Type>) (patterns: #seq<Quotations.Expr>) =
    createPattern (Seq.map (fun x -> CecilTools.convertType x) parameters) (Seq.map createExprFromQuot patterns)

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
    new HashSet<struct (TypeRef * TypeRef)>([
        struct (CecilTools.boolType, CecilTools.intType)
    ])
let private simplifyHardcoded (assumptions: AssumptionSet) (expr: SExpr) =
    match expr.Node with
    | SExprNode.InstructionCall (InstructionFunction.Convert, convertTo, EqArray.AP [ { Node = SExprNode.InstructionCall(InstructionFunction.Convert, convertFrom, EqArray.AP [insideExpr]) } as convExpr ])
        when convertTo = insideExpr.ResultType && lossLessConversions.Contains (struct (convertTo, convertFrom)) ->
        if insideExpr.ResultType = convertTo then
            insideExpr
        else SExpr.InstructionCall InstructionFunction.Convert convertTo [ insideExpr ]
    | SExprNode.InstructionCall (InstructionFunction.Convert, convertTo, EqArray.AP [ insideExpr ])
        when insideExpr.ResultType = convertTo ->
        insideExpr

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
            | Ok (resolvedVars) when patternInfo.TypeVars.Length = 0 ->
                let resolvedVars = Enumerable.ToDictionary(resolvedVars |> Seq.mapi(fun index var -> (patternInfo.Variables.[index], var)), fst, snd)
                patternInfo.EqExpressions |> IArray.choose (fun eqExpr ->
                    if eqExpr = expr then None
                    else
                        let mutable ok = true
                        let assigned =
                            assignParameters (fun p ->
                                match resolvedVars.TryGetValue(p) with
                                | (true, Some assigned) -> Some assigned
                                | (true, None) -> ok <- false; None
                                | (false, _) -> None
                            ) eqExpr
                        if ok then Some assigned else None
                )
            | _ -> array<_>.Empty
        )

let private simplifyExpressionCore (map: PatternMap) (assumptions: AssumptionSet) a =
    // printfn "\t simplifying %s" (ExprFormat.exprToString a)
    SExpr.Visitor (fun expr visitChildren ->
        match expr.SimplificationVersion with
        | (AssumptionSetVersion a) when a < assumptions.Version.Num || a = -1L ->
            let expr_t = (simplifyHardcoded assumptions expr)
            let expr_s = visitChildren expr_t
            let p = execPatterns map expr_s
                    //|> fun a -> printfn "\t\texecuting patterns for %s, got %d" (ExprFormat.exprToString expr_s) (Seq.length a); a
                    |> Seq.append [expr_s; expr_t]
                    |> Seq.reduce (ExprCompare.exprMin)
            Some p
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
    createPatternFromQuot
        [ typeof<bool>; ]
        [ <@ fun a -> not (not a) @>; <@ fun a -> a @> ]
    createPatternFromQuot
        [ typeof<bool>; typeof<bool>; typeof<bool> ]
        [ <@ fun a b c -> if c then a else b @>; <@ fun a b c -> if not c then b else a @> ]
    createPatternFromQuot
        [ typeof<int>; typeof<int> ]
        [ <@ fun a b -> a < b @>; <@ fun a b -> b > a @> ]
]

let simplify = createSimplifier defaultPatterns