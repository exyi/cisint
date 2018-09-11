module ExprCompare
open Expression
open System.Collections.Generic

let private getExprBaseKey =
    let inline getLValueKey x =
        match x with
        | SLExprNode.Parameter _ -> "Ap"
        | SLExprNode.Dereference _ -> "d"
        | SLExprNode.LdElement _ -> "lde"
        | SLExprNode.LdField _ -> "ldf"
    function
    | SExprNode.Constant _ -> "ZZZ"
    | SExprNode.Condition _ -> "Y"
    | SExprNode.LValue lv -> "E_" + getLValueKey lv
    | SExprNode.Reference lv -> "rf_" + getLValueKey lv
    | SExprNode.PureCall (method, _) -> "pc_" + (string method.Reference.MetadataToken.RID)
    | SExprNode.InstructionCall (i, _, _) -> "B_" + i.ToString()

// ((a + b) + (c + d)) > (a + (b + (c + d)))
// c > "constant"
// (if a then c else c) > c

let compareObj (a: 'x) (b: 'x) =
    Comparer<'x>.Default.Compare(a, b)

// let inline tupleCompare2 (a1 : 'a, b1: 'b) (a2 : 'a, b2 : 'b) =
//     let a = Comparer<'a>.Default.Compare(a1, a2)
//     if a = 0 then
//         Comparer<'b>.Default.Compare(b1, b2)
//     else
//         a
// let inline tupleCompare3 (a1, b1, c1) (a2, b2, c2) =

let rec exprCompare (a: SExpr) (b: SExpr) =

    if a.NodeLeavesRank <> b.NodeLeavesRank then
        a.NodeLeavesRank.CompareTo b.NodeLeavesRank
    else if a.NodeRank <> b.NodeRank then
        a.NodeRank.CompareTo b.NodeRank
    else


    let (t_a, t_b) = getExprBaseKey a.Node, getExprBaseKey b.Node
    if t_a <> t_b then
        t_a.CompareTo(t_b)
    elif System.Object.ReferenceEquals(a, b) then
        0
    else


    let recurse items =
        items
        |> Seq.map (fun (i_a, i_b) -> exprCompare i_a i_b)
        |> Seq.tryFind ((<>) 0)
        |> Option.defaultWith (fun _ ->
            if a.Node = b.Node then
                a.ResultType.FullName.CompareTo(b.ResultType.FullName)
            else
                compareObj (string a.Node, a.ResultType) (string b.Node, b.ResultType)
        )

    let procLValue a b =
            match (a, b) with
            | (SLExprNode.Dereference e, SLExprNode.Dereference e_p) ->
                recurse [ e, e_p ]
            | (SLExprNode.LdField (field, Some e), SLExprNode.LdField (field_p, Some e_p))
                when field = field_p ->
                recurse [ e, e_p ]
            | (SLExprNode.LdField (field_a, _), SLExprNode.LdField (field_b, _)) ->
                field_a.ToString().CompareTo(field_b.ToString())
            | (SLExprNode.LdElement (target, index), SLExprNode.LdElement (target_p, index_p)) ->
                recurse [ target, target_p ; index, index_p ]
            | (SLExprNode.Parameter a, SLExprNode.Parameter b) ->
                compareObj (a.Name, a.Type, a.Id) (b.Name, b.Type, b.Id)
            | (a, b) when a = b -> 0
            | (a, b) -> failwithf "can't compare lvalues %A AND %A" a b

    match (a.Node, b.Node) with
    | (SExprNode.Condition (cond_a, ifTrue_a, ifFalse_a), SExprNode.Condition (cond_b, ifTrue_b, ifFalse_b)) ->
        recurse [
            cond_a, cond_b
            ifTrue_a, ifTrue_b
            ifFalse_a, ifFalse_b
        ]
    | (SExprNode.InstructionCall (instruction_a, itype_a, args_a), SExprNode.InstructionCall(instruction_b, itype_b, args_b))
        when instruction_a = instruction_b && itype_a = itype_b && args_a.arr.Length = args_b.arr.Length ->
        recurse (Seq.zip args_a.arr args_b.arr)
    | (SExprNode.InstructionCall (instruction_a, itype_a, args_a), SExprNode.InstructionCall(instruction_b, itype_b, args_b)) ->
        compareObj (string instruction_a, itype_a.FullName, args_a.arr.Length, a.ResultType.FullName) (string instruction_b, itype_b.FullName, args_b.arr.Length, b.ResultType.FullName)
    | (SExprNode.PureCall (method, args), SExprNode.PureCall (method_p, args_p))
        when method = method_p && args.arr.Length = args_p.arr.Length ->
        recurse (Seq.zip args.arr args_p.arr)
    | (SExprNode.PureCall (method_a, args_a), SExprNode.PureCall (method_b, args_b)) ->
        compareObj (method_a.ToString(), args_a.arr.Length) (method_b.ToString(), args_b.arr.Length)
    | (SExprNode.LValue lv, SExprNode.LValue lv_p) -> procLValue lv lv_p
    | (SExprNode.Reference lv, SExprNode.Reference lv_p) -> procLValue lv lv_p
    | (SExprNode.Constant c_a, SExprNode.Constant c_b) ->
        compareObj (a.ResultType.FullName, c_a) (b.ResultType.FullName, c_b)
    | (n_a, n_b) when n_a = n_b -> a.ResultType.FullName.CompareTo(b.ResultType.FullName)
    | (a, b) -> failwithf "can't compare %A AND %A" a b

let exprMin a b =
    let compare = exprCompare a b
    softAssert (compare <> 0 || a = b) "Wrong comparisons"
    if compare <= 0 then
        a
    else
        b

let comparerImpl : IComparer<SExpr> =
    { new IComparer<SExpr>
      with member _x.Compare(a, b) = exprCompare a b
    }