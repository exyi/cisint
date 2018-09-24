module InterpreterState
open System.Collections.Immutable
open Expression
open TypesystemDefinitions
open System.Threading.Tasks

let indexParameter = SParameter.New CecilTools.intType "_index"

let mutable private arrayDefaultCounter = 0L
type ArrayInfo = {
    /// Expression that returns the element of the array if it's not found in the `Constants`
    GeneralExpression: SExpr
    /// When some elements of the array are known to be at constant index, they are stored here for easier access
    Constants: ImmutableDictionary<int, (SExpr)>
    /// Length of the array, if it's known
    Length: SExpr option
}
with
    /// Creates an array with the default value everywhere and unknown length
    static member Initialize defaultValue =
        {
          GeneralExpression = defaultValue
          Constants = dict<_, _>.Empty
          Length = None
        }

/// Represents a state of the heap object
type HeapObject = {
    Type: TypeRef
    /// If the the is known exactly or if the object can also be derived from the `Type`
    TypeIsDefinite: bool
    /// Known fields of the object. Unknown fields should not be in the dictionary and will be referenced as a expression of form `obj.field`.
    Fields: dict<FieldRef, SExpr>
    /// If the object is an array, the additional data are stored here
    Array: ArrayInfo option
    /// If the object may be shared with something else and all read/writes should be considered volatile
    IsShared: SExpr
}

[<CustomEquality>]
[<NoComparisonAttribute>]
type AssumptionSet = {
    Version: AssumptionSetVersion
    /// Set of expressions that are known to be true
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

/// Side effects with a condition
type ConditionalEffect = (SExpr * SideEffect)

and SideEffect =
    /// Method is invoked. The result of the invocation is stored in `resultValue`. If the method does not have `globalEffect` it means that it should only have effect on it's arguments and result value.
    | MethodCall of MethodRef * resultValue: SParameter * args: SExpr array * virt: bool * globalEffect: bool * atState: AssumptionSet
    /// A write operation to a shared field
    | FieldWrite of target: SParameter option * FieldOrElement * value: SExpr * atState: AssumptionSet
    /// A read from a shared field
    | FieldRead of target: SParameter option * FieldOrElement * resultValue: SParameter * atState: AssumptionSet
    /// Throw of an exception.
    | Throw of value: SParameter * atState: AssumptionSet
    /// Represents an exception handled block of side effects. When the catchHandler is invoked, the exception is stored in `exceptionValue`
    | ExceptionHandledEffects of body: ConditionalEffect array * exceptionValue: SParameter * finallyHandler: SideEffect * catchHandler: SideEffect
    /// Recursive list of conditional effects.
    | Effects of ConditionalEffect array

/// Complete state of the program (including a log of side-effects, excluding instruction pointers)
type ExecutionState = {
    /// The state where this one was forked. This is mainly used for branching/marging the program state.
    Parent: ExecutionState option
    /// List of program's side effects. (items from Parent state are not duplicated here)
    SideEffects: ConditionalEffect list
    /// Conditions of this branch of the program state
    Conditions: SExpr array
    /// All assumptions that hold about the program parameters (all conditions and objects)
    Assumptions: AssumptionSet
    /// Objects that were changed in this branch of state
    ChangedHeapObjects: SParameter clist
    /// All local variables used by the program
    Locals: dict<SParameter, SExpr>
    /// The contents of the current IL evaluation state
    Stack: SExpr clist
} with
    override x.ToString () =
        sprintf "State, %d side effects, %d objects, parent = { %O }" x.SideEffects.Count x.Assumptions.Heap.Count x.Parent
    /// Get side effects including those from parent states
    member x.AllSideEffects =
        seq {
            match x.Parent with
            | Some (p) -> yield! p.AllSideEffects
            | _ -> ()
            yield! x.SideEffects
        }
    member x.WithCondition (conditions: #seq<SExpr>) =
        { ExecutionState.Parent = Some x; SideEffects = list<_>.Empty; Conditions = IArray.ofSeq conditions; Assumptions = AssumptionSet.add conditions x.Assumptions; Stack = x.Stack; ChangedHeapObjects = []; Locals = x.Locals }.AssertSomeInvariants()
    member x.ChangeObject (objs: #seq<SParameter * HeapObject>) =
        let objs = IArray.ofSeq objs
        { x with Assumptions = AssumptionSet.changeObj objs x.Assumptions; ChangedHeapObjects = List.append (List.ofSeq <| Seq.map fst objs) x.ChangedHeapObjects }.AssertSomeInvariants()
    /// Takes `count` elements from the stack and returns them in natural order (reversed stack order)
    member x.PopStack (count: int) =
        let head = List.take count x.Stack
        List.rev head, { x with Stack = List.skip count x.Stack }
    static member Empty = { ExecutionState.Parent = None; SideEffects = list<_>.Empty; Conditions = array<_>.Empty; Assumptions = AssumptionSet.empty; Stack = []; ChangedHeapObjects = []; Locals = dict<_, _>.Empty }

    member x.AssertSomeInvariants () =
#if DEBUG
        softAssert (x.ChangedHeapObjects |> Seq.forall (x.Assumptions.Heap.ContainsKey)) "EState has inconsistent heap"
#endif
        x

type InterpreterTodoTarget =
    | CurrentMethod of Mono.Cecil.Cil.Instruction
    | CallMethod of MethodRef * args: SExpr clist * returnInstruction: option<Mono.Cecil.Cil.Instruction> * isVirtual: bool
    | AccessStaticField of FieldRef * returnInstruction: Mono.Cecil.Cil.Instruction
    | ExceptionHandlerEntry of Mono.Cecil.Cil.Instruction

type InterpreterTodoItem = {
    State: ExecutionState
    Target: InterpreterTodoTarget
}

type InterpretationResult =
    | NewState of ExecutionState
    | Branching of InterpreterTodoItem clist
    | Return of ExecutionState
    | ExitExceptionHandler of ExecutionState * target: Mono.Cecil.Cil.Instruction option

type InterpreterReturnType =
    | NextMethod
    | LeaveExceptionHandler of target: Mono.Cecil.Cil.Instruction option

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


type InterpreterFrameInfo = {
    FrameToken: obj
    Method: MethodRef
    Args: SExpr array
    BranchingFactor: int
    CurrentInstruction: Mono.Cecil.Cil.Instruction
}

type InterpreterFrameDispatcher = InterpreterFrameInfo clist -> (unit -> Task<ExecutionState * InterpreterReturnType>) -> Task<ExecutionState * InterpreterReturnType>

type ExecutionServices = {
    /// asynchronously dispatches a frame (i.e. a piece of computation)
    Dispatch: InterpreterFrameDispatcher
    /// Return the state after the method invoked.
    InterpretMethod: MethodRef -> ExecutionState -> array<SExpr> -> ExecutionServices -> Task<ExecutionState>
    /// When the MethodCall side effect is added, this info affects the `shared` and `global` flags, types of result and so on.
    GetMethodSideEffectInfo: MethodRef -> ExecutionServices -> MethodSideEffectInfo
    /// Returns the state after the static field is accessed
    AccessStaticField: FieldRef -> ExecutionState -> ExecutionServices -> Task<SExpr * ExecutionState>
}

exception FunctionTooComplicatedException of string
let tooComplicated msg = raise (FunctionTooComplicatedException msg)
let assertOrComplicated cond msg = if not cond then raise (FunctionTooComplicatedException msg)