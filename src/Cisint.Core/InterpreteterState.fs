module InterpreterState
open System.Collections.Immutable
open Expression
open TypesystemDefinitions

let indexParameter = SParameter.New CecilTools.intType "_index"

let mutable private arrayDefaultCounter = 0L
type ArrayInfo = {
    GeneralExpression: SExpr
    Constants: ImmutableDictionary<int, (SExpr)>
    Length: SExpr option
    CurrentVersion: int
}
with
    static member Initialize elementType defaultValue =
        let p = SParameter.New elementType (sprintf "array_default%d" (System.Threading.Interlocked.Increment(&arrayDefaultCounter)))
        {
          GeneralExpression = defaultValue
          Constants = dict<_, _>.Empty
          CurrentVersion = 0
          Length = None
          }

type HeapObject = {
    Type: TypeRef
    TypeIsDefinite: bool
    Fields: dict<FieldRef, SExpr>
    Array: ArrayInfo option
    IsShared: SExpr
}

[<CustomEquality>]
[<NoComparisonAttribute>]
type AssumptionSet = {
    Version: AssumptionSetVersion
    /// Set of expressions that are known to return true
    Set: ImmutableHashSet<SExpr>

    /// Set of all objects on the heap
    Heap: dict<SParameter, HeapObject>
} with
    interface System.IEquatable<AssumptionSet> with
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
        System.Threading.Interlocked.Increment(&assumptionSetVersionCounter) |> AssumptionSetVersion
    let empty = { Version = AssumptionSetVersion 0L; Set = ImmutableHashSet.Create<SExpr>(); Heap = dict<_, _>.Empty }
    // TODO: cache these guys, so ids remain the same for same version
    let add (assumptions: #seq<SExpr>) x =
        { x with Set = x.Set.Union(assumptions); Version = nextASVersion () }
    let changeObj (objs: #seq<SParameter * HeapObject>) x =
        { x with Heap = x.Heap.SetItems(objs |> Seq.map (fun (a, b) -> System.Collections.Generic.KeyValuePair(a, b))) }

    let modObj key fn x =
        { x with Heap = x.Heap.SetItem(key, fn x.Heap.[key]); Version = nextASVersion () }


[<RequireQualifiedAccess>]
type FieldOrElement =
    | FieldRef of FieldRef
    | ElementRef of index: SExpr * resultType: TypeRef
with
    member x.ResultType =
        match x with
        | FieldRef f -> f.FieldType
        | ElementRef (_index, resultType) -> resultType

type ConditionalEffect = (SExpr * SideEffect)

and SideEffect =
    | MethodCall of MethodRef * resultValue: SParameter * args: SExpr array * virt: bool * globalEffect: bool * atState: AssumptionSet
    | FieldWrite of target: SParameter option * FieldOrElement * value: SExpr * atState: AssumptionSet
    | FieldRead of target: SParameter option * FieldOrElement * resultValue: SParameter * atState: AssumptionSet
    | Throw of value: SParameter * atState: AssumptionSet
    | Effects of ConditionalEffect array

type ExecutionState = {
    Parent: ExecutionState option
    SideEffects: ConditionalEffect list
    Conditions: SExpr array
    Assumptions: AssumptionSet
    // AssumptionsVersion: AssumptionSetVersion
    ChangedHeapObjects: SParameter clist
    Locals: dict<SParameter, SExpr>
    Stack: SExpr clist
} with
    override x.ToString () =
        sprintf "State, %d side effects, %d objects, parent = { %O }" x.SideEffects.Count x.Assumptions.Heap.Count x.Parent
    /// Get side effects incuding those from parent states
    member x.AllSideEffects =
        seq {
            match x.Parent with
            | Some (p) -> yield! p.AllSideEffects
            | _ -> ()
            yield! x.SideEffects
        }
    member x.WithCondition (conditions: #seq<SExpr>) =
        { ExecutionState.Parent = Some x; SideEffects = list<_>.Empty; Conditions = IArray.ofSeq conditions; Assumptions = AssumptionSet.add conditions x.Assumptions; Stack = x.Stack; ChangedHeapObjects = []; Locals = x.Locals }
    member x.ChangeObject (objs: #seq<SParameter * HeapObject>) =
        { x with Assumptions = AssumptionSet.changeObj objs x.Assumptions; ChangedHeapObjects = List.append (List.ofSeq <| Seq.map fst objs) x.ChangedHeapObjects }
    /// Takes `count` elements from the stack and returns them in natural order (reversed stack order)
    member x.PopStack (count: int) =
        let head = List.take count x.Stack
        List.rev head, { x with Stack = List.skip count x.Stack }
    static member Empty = { ExecutionState.Parent = None; SideEffects = list<_>.Empty; Conditions = array<_>.Empty; Assumptions = AssumptionSet.empty; Stack = []; ChangedHeapObjects = []; Locals = dict<_, _>.Empty }

type InterpreterTodoTarget =
    | CurrentMethod of Mono.Cecil.Cil.Instruction * isLeave: bool
    | CallMethod of MethodRef * args: SExpr clist * returnInstruction: option<Mono.Cecil.Cil.Instruction> * isVirtual: bool

type InterpreterTodoItem = {
    State: ExecutionState
    Target: InterpreterTodoTarget
}

type InterpretationResult =
    | NewState of ExecutionState
    | Branching of InterpreterTodoItem clist
    | Return of ExecutionState

type MethodArgumentEffect =
    /// The method only reads from the passed object
    | ReadOnly
    /// The method may read and write to the object, but CAN'T LINK OBJECTS TOGETHER. Implies that the values of all field will become unknown after the effect is executed.
    | Mutable
    /// The object will also become shared
    | Shared
type MethodSideEffectInfo = {
    /// The side-effect is global, i.e. can't be neglected even though it's modified arguments are unused, can't be reordered and so on
    IsGlobal: bool
    /// Whether the function may be used in expressions instead of side-effects
    IsPure: bool
    ArgumentBehavior: MethodArgumentEffect array
    ResultIsShared: bool
    ActualResultType: TypeRef option
}

exception FunctionTooComplicatedException of string
let tooComplicated msg = raise (FunctionTooComplicatedException msg)
let assertOrComplicated cond msg = if not cond then raise (FunctionTooComplicatedException msg)