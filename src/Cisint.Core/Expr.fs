module Expression
open System
open System.Collections.Immutable
open System.Threading
open TypesystemDefinitions

type InstructionFunction =
    | Add = 0
    | And = 1
    | C_Eq = 3
    | C_Gt = 4
    | C_Lt = 5
    /// see Table 8: Conversion Operations, page 330
    | Convert = 6
    | Convert_Checked = 7
    | Div = 8
    /// Cast that return null if it's not successful
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
    /// Shift right (unsigned argument -> logical, signed argument -> arithmetic)
    | Shr = 15
    /// Shift left
    | Shl = 16
    | Sub = 17
    | Xor = 19
    /// Cast that throws an exception if it's not successful
    | Cast = 20
    /// Loads length of an array
    | ArrLen = 22
    /// Sentinel value for undecidable values. (State of variables after ommited exception handler, anything computed from other undecidables)
    | Undecidable = 23

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
/// Writable value. For practical purposes, all LValues are basically equivalent to Parameter as the LdField, LdElement and Dereference are only used to introduce a virtual symbolic parameter when something that is not known is referenced.
type SLExprNode =
    /// Load of object field when the value of the field is not known.
    | LdField of FieldRef * target: SExpr option
    /// Load of array element when the value of the element is not known.
    | LdElement of target: SExpr * index: SExpr
    /// Load of parameter
    | Parameter of SParameter
    /// Dereference of a reference expression (when the value is not known)
    | Dereference of SExpr

/// Discriminated union of symbolic tree node types
and SExprNode =
    /// Reference to LValue
    | Reference of SLExprNode
    /// Read of LValue
    | LValue of SLExprNode
    /// Invocation of a pure function
    | PureCall of MethodRef * args: SExpr EqArray
    /// Invocation of a primitive function
    | InstructionCall of InstructionFunction * TypeRef * args: SExpr EqArray
    /// Conditional expression (if condition then ifTrue else ifFalse)
    | Condition of condition: SExpr * ifTrue: SExpr * ifFalse: SExpr
    /// Constant expression. The type is declared in the enclosing SExpr.
    | Constant of obj
/// Symbolic expression
and SExpr = {
    ResultType: TypeRef
    NodeLeavesRank: int
    NodeRank: int64
    Node: SExprNode
    SimplificationVersion: AssumptionSetVersion
}
with
     override x.ToString() =
        sprintf "expression %s : %O" (x.Node.GetType().Name) x.ResultType
     member a.IsUndecidable = match a.Node with SExprNode.InstructionCall (InstructionFunction.Undecidable, _, _) -> true | _ -> false
     static member New resultType node =
        let struct (cRank, lRank) = SExpr.CountExprNodes node
        { SExpr.Node = node; ResultType = resultType; SimplificationVersion = AssumptionSetVersion.None; NodeLeavesRank = lRank; NodeRank = cRank }
     static member PureCall method (args: #seq<_>) =
        let node = PureCall (method, ImmutableArray.CreateRange(args) |> EqArray.New)
        SExpr.New (TypeRef method.Reference.ReturnType) node
     static member InstructionCall func resultType (args: #seq<_>) =
        let node = InstructionCall (func, resultType, ImmutableArray.CreateRange(args) |> EqArray.New)
        SExpr.New resultType node
     /// Creates a cast operation if type of the `node` is different than the expected type
     static member Cast func rtype node =
        if node.ResultType = rtype && (func <> InstructionFunction.IsInst || rtype.IsObjectReference) then node
        else SExpr.InstructionCall func rtype [ node ]
     static member Undecidable t = SExpr.InstructionCall InstructionFunction.Undecidable t []
     static member Parameter p =
        let node = LValue (Parameter p)
        SExpr.New p.Type node

     static member ParamReference p =
        let node = Reference (Parameter p)
        let resType = TypeRef.CreateByref(p.Type)
        SExpr.New resType node
     static member Reference (referencedType: TypeRef) lvalue =
        let t = TypeRef.CreateByref(referencedType)
        SExpr.New t (SExprNode.Reference lvalue)
     static member Dereference expr =
        let t = expr.ResultType.Reference :?> Mono.Cecil.ByReferenceType
        SExpr.New (TypeRef t.ElementType) (SExprNode.LValue (SLExprNode.Dereference expr))
     static member LdField field target =
        let node = LValue (LdField (field, target))
        SExpr.New field.FieldType node
     static member LdElement target index =
        let node = LValue (LdElement (target, index))
        SExpr.New (TypeRef ((target.ResultType.Reference :?> Mono.Cecil.ArrayType).ElementType)) node
     static member Condition cond ifTrue ifFalse =
        softAssert (ifTrue.ResultType = ifFalse.ResultType) <| sprintf "condition branches must have the same type, %O vs %O" ifTrue.ResultType ifFalse.ResultType
        softAssert (cond.ResultType.Reference.MetadataType = Mono.Cecil.MetadataType.Boolean) "condition must be boolean"
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
     static member private GetNodeRank node =
        match node with
        | SExprNode.Condition _ -> 15L
        | SExprNode.PureCall _ -> 100L
        | SExprNode.Reference _ -> 5L
        | SExprNode.InstructionCall (InstructionFunction.Sub, _, _) -> 5L
        | SExprNode.InstructionCall _ -> 2L
        | SExprNode.Constant _ | SExprNode.LValue _ -> 1L
     static member private CountExprNodes node =
        let expr = { SExpr.ResultType = CecilTools.generalSentinelType; SimplificationVersion = AssumptionSetVersion.None; Node = node; NodeLeavesRank = -1; NodeRank = -1L }
        let countExprNodes a =
            let mutable nodeCounter = 0L
            let mutable leavesCounter = 0
            SExpr.Visitor (fun e _ ->
                if Object.ReferenceEquals(e, expr) then
                    None
                else
                softAssert (e.NodeRank > 0L) "NodeCountRank > 0"
                softAssert (e.NodeLeavesRank >= 0) "NodeLeavesRank >= 0"
                nodeCounter <- nodeCounter + e.NodeRank
                leavesCounter <- leavesCounter + (
                    if e.NodeLeavesRank > 0 then e.NodeLeavesRank else 1)
                Some e) a |> ignore
            struct (nodeCounter + SExpr.GetNodeRank node, leavesCounter)
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
