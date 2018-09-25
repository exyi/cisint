# API of Cisint

The main function of is `Interpreter.interpretMethod` -- it takes a method, it's arguments as symbolic expressions, initial state of the program and `ExecutionServices`. It return a state after the method is executed (the result value is the only element of IL stack).

### `ExecutionState`

It represents a state of the program (including a log of side-effects, excluding instruction pointers) at any point during the execution. It's also the result of any interpretation. There is some general info about in the [README](../README.md) and you can find more details on the record type.

### `SExpr`

This is the main class that represents the symbolic expressions. It contains some general metadata about the node (like the `ResultType`) and the `Node` itself. The node is a discriminated union with a few options, in a nutshell it can represent

* Symbolic parameters
* Constants
* Invocations of primitive "instruction functions" (basic instructions that don't have side-effects. e.g. add, xor, cast, ...)
* Invocations of custom pure functions
* Conditions
* References and dereferences

For more details, have a look at the record type.

### MethodRef, FieldRef and TypeRef

This is a wrapper around Mono.Cecil references. It tracks generic parameter for us and you can easily get the underlying Mono.Cecil reference in the `Reference` field. To create it, just use the default constructor or `CecilTools.convertType : System.Type -> TypeRef` if you have a reflection type.

### ExecutionServices

This is the main extensibility point of the interpreter, there are some functions that you can "override":

* `InterpretMethod`: This is supposed to invoke the interpreter, but you can wrap in custom logic, suppress certain methods exchange the method reference to another implementation and so on.
* `AccessStaticField`: Similar to the above. By default, accessing a static field is always a side effect, but if you know what will be in the field, you can provide custom implementation.
* `GetMethodSideEffectInfo`: When method is considered a side-effect, the interpreter does not know anything about it's implementation and has to assume that the method can do anything ungly to it's parameters (send them to other threads and change it periodically). You can override that for your methods here.
* `Dispatch`: Rather internal function that is invoked when the code is branching. It's used to parellelize things by default, and suppress the parallelization for tests. It can be also used to trace all processed invocations, supress execution of certain branches and so on.

To configure the interpreter, you should start with the default options `Interpreter.defaultServices` and rewrite only the functions that you want. For example, if you want synchronous dispatcher with custom callback for every frame:

```F#

let dispatcher = Interpreter.createSynchronousDispatcher (fun frames ->
        do whatever you want with the frames
    )

let execService =
    { Interpreter.defaultServices with
        Dispatch = dispatcher
    }
```

As another example, we can replace the default `AccessStaticField`. There is a prebuilt `Interpreter.aBitSmartReadStaticField` that tries to execute static constructor to figure what ends up in readonly static fields.

```F#
let execService =
    { Interpreter.defaultServices with
        AccessStaticField = Interpreter.aBitSmartReadStaticField
    }
```

As promised above, you can easily replace implementation of certain methods:

```F#
let execService =
    { Interpreter.defaultServices with
        InterpretMethod = fun method state args services ->
            if method = myMethod1 then
                services.InterpretMethod myMethod2 state args services
            else
                Interpreter.defaultServices.InterpretMethod method state args services
    }
```

Architecture note: If you'd expect this to be a interface or a abstract class, I just need to show you what can you do with this simple record of functions:

```F#
// define a function for each transformation you want to do

let replaceMethod1 s =
    { s with
        InterpretMethod = fun method state args services ->
            if method = myMethod1 then
                services.InterpretMethod myMethod2 state args services
            else
                s.InterpretMethod method state args services
    }

let supressMethod4 s =
    { s with
        InterpretMethod = fun method state args services ->
            if method = myMethod1 then
                // add a side effect instead of interpreting the method
                StateProcessing.addCallSideEffect method (services.GetMethodSideEffectInfo method services) args (*virt*)false state |> System.Threading.Tasks.Task.FromResult
            else
                Interpreter.defaultServices.InterpretMethod method state args services    
    }

... more functions like this

// fold these functions together. See? No more multiple inheritance issues, no more decorator boilerplate, just simple function composition ;)
let customizeServices =
    [
        replaceMethod1
        supressMethod4
        addFrameLogger
        ... more functions
    ] |> List.reduce (>>)

// you have also probably heard that the funcition composition is asociative, which means that you can put these modifications into separate function and form a tree where you can disable/enable certain branches based on confiuration. You can even generate some of these branches from the configuration :)

```

End of "FP > OOP" note


### Example usage

When we have the configuration prepared, we can invoke the interpreter. This time, with two arguments - a constant and a symbolic parameter.

```F#

let method1 = some method
let execServices = ... see above
let initialState = ExecutionState.Empty

let argument1 = SExpr.ImmConstant 42
let parameterA = SParameter.New CecilTools.intType "a"
let argument2 = SExpr.Parameter parameterA

task {
    // it returns Task<ExecutionState>, as it can be parallel
    let! resultState = Interpreter.interpretMethod method1 state (IArray.ofSeq [argument1; argument2]) execService
    if resultState.SideEffects.IsEmpty then
        printfn "Wow, the function does not have any side-effects"
    else printfn "Hmm, the functions seems to have some effects"
}

```

You also run one function and then a second function.

```F#
task {
    let! state1 = Interpreter.interpretMethod method1 state (IArray.ofSeq [argument1; argument2]) execService
    let result1 = List.exactlyOne state1.Stack
    let! state2 = Interpreter.interpretMethod method2 state1 (IArray.ofSeq [result1]) execService
    
    // ... process state2
}
```

You can also create an object and then invoke the function with that object.

```F#
let objParameter = SParameter.New objectType "inputObj"
let object = { HeapObject.Type = objectType
               TypeIsDefinite = true
               IsShared = SExpr.ImmConstant false
               Array = None
               // fields that are not assigned are "implicit" symbolic parameters
               Fields = ImmutableDictionary<_, _>.Empty
             }
let initialState = ExecutionState.Empty.ChangeObject [ objParameter, object ]


Interpreter.interpretMethod method1 state (IArray.ofSeq [SExpr.Parameter object]) execService

```
