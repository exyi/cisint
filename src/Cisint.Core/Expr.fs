module Expression
open System
open System.Collections.Immutable
open System.Threading
open TypesystemDefinitions

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
    /// see Table 8: Conversion Operations, page 330
    | Convert = 6
    | Convert_Checked = 7
    | Div = 8
    | IsInst = 9
    | Mul = 10
    /// Twos-complement negation, aka minus
    | Negate = 11
    /// Bool negation
    | Not = 12
    /// Bitwise negation
    | BitNot = 21
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
    Type: TypeRef
    Name: string
    Id: Guid
}
with static member New resultType name =
        { Type = resultType; Name = name; Id = Guid.NewGuid() }

[<StructuralEqualityAttribute>] [<NoComparisonAttribute>]
type SLExprNode =
    | LdField of FieldRef * target: SExpr option
    | LdElement of target: SExpr * index: SExpr
    | Parameter of SParameter
    | Dereference of SExpr

and SExprNode =
    | Reference of SLExprNode
    | LValue of SLExprNode
    | PureCall of MethodRef * args: SExpr EqArray
    | InstructionCall of InstructionFunction * TypeRef * args: SExpr EqArray
    | Condition of condition: SExpr * ifTrue: SExpr * ifFalse: SExpr
    | Constant of obj
and SExpr = {
    ResultType: TypeRef
    NodeLeavesRank: int
    NodeCountRank: int
    Node: SExprNode
//    Config: SExprConfig
    SimplificationVersion: AssumptionSetVersion
}
with
     override x.ToString() =
        sprintf "expression %s : %O" (x.Node.GetType().Name) x.ResultType
     static member New resultType node =
        let struct (cRank, lRank) = SExpr.CountExprNodes node
        { SExpr.Node = node; ResultType = resultType; SimplificationVersion = AssumptionSetVersion.None; NodeLeavesRank = lRank; NodeCountRank = cRank }
     static member PureCall method (args: #seq<_>) =
        let node = PureCall (method, ImmutableArray.CreateRange(args) |> EqArray.New)
        SExpr.New (TypeRef method.Reference.ReturnType) node
     static member InstructionCall func resultType (args: #seq<_>) =
        let node = InstructionCall (func, resultType, ImmutableArray.CreateRange(args) |> EqArray.New)
        SExpr.New resultType node
     static member Cast func rtype node =
        if node.ResultType = rtype then node
        else SExpr.InstructionCall func rtype [ node ]
     static member Parameter p =
        let node = LValue (Parameter p)
        SExpr.New p.Type node

     static member ParamReference p =
        let node = Reference (Parameter p)
        let resType = Mono.Cecil.ByReferenceType(p.Type.Reference) |> TypeRef
        SExpr.New resType node
     static member Dereference expr =
        let t = expr.ResultType.Reference :?> Mono.Cecil.ByReferenceType
        SExpr.New (TypeRef t.ElementType) (SExprNode.LValue (SLExprNode.Dereference expr))
     static member LdField field target =
        let node = LValue (LdField (field, target))
        SExpr.New (TypeRef field.Reference.FieldType) node
     static member LdElement target index =
        let node = LValue (LdElement (target, index))
        SExpr.New (TypeRef (target.ResultType.Reference.GetElementType())) node
     static member Condition cond ifTrue ifFalse =
        assert (ifTrue.ResultType = ifFalse.ResultType)
        assert (cond.ResultType.Reference.MetadataType = Mono.Cecil.MetadataType.Boolean)
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
        let expr = { SExpr.ResultType = CecilTools.generalSentinelType; SimplificationVersion = AssumptionSetVersion.None; Node = node; NodeLeavesRank = -1; NodeCountRank = -1 }
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
     static member BoolNot node =
        let node =
            if node.ResultType.Reference.MetadataType = Mono.Cecil.MetadataType.Boolean then node
            else SExpr.InstructionCall InstructionFunction.Convert CecilTools.boolType [ node ]
        SExpr.InstructionCall InstructionFunction.Not CecilTools.boolType [ node ]
     static member BoolAnd a b = SExpr.InstructionCall InstructionFunction.And CecilTools.boolType [a; b]
     static member BoolOr a b = SExpr.InstructionCall InstructionFunction.Or CecilTools.boolType [a; b]
    // static member AreSameType a b =
    //     match (a, b) with
    //     | (Condition (_, _, _), Condition (_, _, _)) -> true
    //     | (InstructionCall (_, _, _), InstrucitonCall (_, _, _)) ->
