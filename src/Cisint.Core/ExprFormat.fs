module ExprFormat
open Expression
open System

let tabRight (str: string) =
    "\t" + str.Replace("\n", "\t\n")

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
        sprintf "%s(%s)" method.FullName (String.Join(", ", args.arr |> Seq.map exprToString))
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
        sprintf "(%s %s %s)" (exprToString a) op (exprToString b)
    | SExprNode.InstructionCall (InstructionFunction.Not, _, args) -> sprintf "!%s" (args.arr |> Seq.exactlyOne |> exprToString)
    | SExprNode.InstructionCall (InstructionFunction.Negate, _, args) -> sprintf "-%s" (args.arr |> Seq.exactlyOne |> exprToString)
    | SExprNode.InstructionCall (instr, t, args) ->
        sprintf "%O<%O>(%s)" instr t (String.Join(", ", args.arr |> Seq.map exprToString))
    | SExprNode.Condition (cond, ifTrue, ifFalse) ->
        sprintf "if (%s) {\n%s\n} else {\n%s\n}" (exprToString cond) (exprToString ifTrue |> tabRight) (exprToString ifFalse |> tabRight)