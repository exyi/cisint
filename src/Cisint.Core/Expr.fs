module Expression
open Mono.Cecil
open System
open System.Collections.Immutable
open System.Threading

//type SExprConfig = {
//    CheckedArtithmetic: bool
//}

type InstructionFunction =
    | Add = 0
    | And = 1
    | Box = 2
    | C_Eq = 3
    | C_Gt = 4
    | C_Lt = 5
    | Convert = 6
    | Convert_Checked = 7
    | Div = 8
    | IsInst = 9
    | Mul = 10
    | Negate = 11
    | Not = 12
    | Or = 13
    | Rem = 14
    | Shr = 15
    | Shl = 16
    | Sub = 17
    | Unbox = 18
    | Xor = 19
    | Cast = 20

[<CustomComparisonAttribute>]
[<CustomEquality>]
type AssumptionSetVersion = AssumptionSetVersion of int64
with
    interface IEquatable<AssumptionSetVersion> with
        /// Always return true, the version number should be ingored (almost) everywhere it's used
        member _a.Equals(_b) = true
    override _a.Equals(b) = b :? AssumptionSetVersion
    override _a.GetHashCode() = 76434567
    interface IComparable<AssumptionSetVersion> with
        member a.CompareTo(AssumptionSetVersion b) = let (AssumptionSetVersion a) = a in a.CompareTo(b)
    static member None = AssumptionSetVersion -1L
    member x.Num = let (AssumptionSetVersion a) = x in a

type SParameter = {
    Type: TypeReference
    Name: string
    Id: Guid
}
with static member New resultType name =
        { Type = resultType; Name = name; Id = Guid.NewGuid() }

[<StructuralEqualityAttribute>] [<NoComparisonAttribute>]
type SLExprNode =
    | LdField of FieldReference * target: SExpr option
    | LdElement of target: SExpr * index: SExpr
    | Parameter of SParameter
    | Dereference of SExpr

and SExprNode =
    | Reference of SLExprNode
    | LValue of SLExprNode
    | PureCall of MethodReference * args: SExpr EqArray
    | InstructionCall of InstructionFunction * TypeReference * args: SExpr EqArray
    | Condition of condition: SExpr * ifTrue: SExpr * ifFalse: SExpr
    | Constant of obj
and SExpr = {
    ResultType: TypeReference
    NodeLeavesRank: int
    NodeCountRank: int
    Node: SExprNode
//    Config: SExprConfig
    SimplificationVersion: AssumptionSetVersion
}
with
     static member New resultType node =
        let struct (cRank, lRank) = SExpr.CountExprNodes node
        { SExpr.Node = node; ResultType = resultType; SimplificationVersion = AssumptionSetVersion.None; NodeLeavesRank = lRank; NodeCountRank = cRank }
     static member PureCall method (args: #seq<_>) =
        let node = PureCall (method, ImmutableArray.CreateRange(args) |> EqArray.New)
        SExpr.New method.ReturnType node
     static member InstructionCall func resultType (args: #seq<_>) =
        let node = InstructionCall (func, resultType, ImmutableArray.CreateRange(args) |> EqArray.New)
        SExpr.New resultType node
     static member Parameter p =
        let node = LValue (Parameter p)
        SExpr.New p.Type node
     static member LdField field target =
        let node = LValue (LdField (field, target))
        SExpr.New field.FieldType node
     static member Condition cond ifTrue ifFalse =
        assert (ifTrue.ResultType = ifFalse.ResultType)
        assert (cond.ResultType.MetadataType = MetadataType.Boolean)
        let node = Condition (cond, ifTrue, ifFalse)
        SExpr.New ifTrue.ResultType node
     static member ImmConstant<'a> (value: 'a) =
        SExpr.New (CecilTools.convertType typeof<'a>) (SExprNode.Constant (box value))
     static member Visitor func =
        let rec visitChildren node =
            let visitLValue =
                function
                | LdField (f, t) -> LdField (f, Option.map core t)
                | LdElement (t, i) -> LdElement(core t, core i)
                | Dereference a -> Dereference (core a)
                | a -> a
            let n =
                match node.Node with
                | Condition (a, b, c) -> Condition(core a, core b, core c)
                | InstructionCall (a, b, args) -> InstructionCall(a, b, IArray.map core args.arr |> EqArray.New)
                | PureCall (m, args) -> PureCall(m, IArray.map core args.arr |> EqArray.New)
                | Reference (a) -> Reference(visitLValue a)
                | LValue(a) -> LValue(visitLValue a)
                | a -> a
            if node.Node = n && node.SimplificationVersion = AssumptionSetVersion -1L then
                node
            else SExpr.New node.ResultType n
        and core node =
            func node visitChildren |> Option.defaultWith (fun () -> visitChildren node)
        core
     static member private CountExprNodes node =
        let expr = { SExpr.ResultType = null; SimplificationVersion = AssumptionSetVersion.None; Node = node; NodeLeavesRank = -1; NodeCountRank = -1 }
        let countExprNodes a =
            let mutable nodeCounter = 0
            let mutable leavesCounter = 0
            SExpr.Visitor (fun e _ ->
                if Object.ReferenceEquals(e, expr) then
                    None
                else
                assert (e.NodeCountRank > 0)
                assert (e.NodeLeavesRank >= 0)
                nodeCounter <- nodeCounter + e.NodeCountRank
                leavesCounter <- leavesCounter + (
                    if e.NodeLeavesRank > 0 then e.NodeLeavesRank else 1)
                Some e) a |> ignore
            struct (nodeCounter + 1, leavesCounter)
        countExprNodes expr
    // static member AreSameType a b =
    //     match (a, b) with
    //     | (Condition (_, _, _), Condition (_, _, _)) -> true
    //     | (InstructionCall (_, _, _), InstrucitonCall (_, _, _)) ->


[<CustomEquality>]
[<NoComparisonAttribute>]
type AssumptionSet = {
    Version: AssumptionSetVersion
    /// Set of expressions that are known to return true
    Set: ImmutableHashSet<SExpr>
} with
    interface IEquatable<AssumptionSet> with
        member a.Equals(b) = a.Set.SetEquals(b.Set)
    override a.Equals b =
        match b with
        | :? AssumptionSet as y -> a.Set.SetEquals(y.Set)
        | _ -> false
    override a.GetHashCode() =
        printfn "warn AssumptionSet.GetHashCode";
        failwith ""
        a.Set.Count // TODO

module AssumptionSet =

    let mutable private assumptionSetVersionCounter = 1L
    let private nextASVersion () =
        Interlocked.Increment(&assumptionSetVersionCounter) |> AssumptionSetVersion
    let empty = { Version = AssumptionSetVersion 0L; Set = ImmutableHashSet.Create<SExpr>() }
    // TODO: cache these guys, so ids remain the same for same version
    let add (assumptions: #seq<SExpr>) x =
        { x with Set = x.Set.Union(assumptions); Version = nextASVersion () }
