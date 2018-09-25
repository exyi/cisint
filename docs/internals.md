# Internals of Cisint

In principle, the symbolic execution engine is pretty simple (it only uses complicated component to make it work). When the `interpretMethod` function is invoked, it invokes `interpretInstruction` function for the first instruction. The instruction may might affect what should happen next (next instruction, jump somewhere, return from function, invoke a method, ...) and might affect the state somehow (change object, local variable, ...) - this is represented by `InterpreterState.InterpretationResult`.

### State processing

Most non-trivial modifications of the state is handled by the StateProcessing module. Most of the code is concerned about the task "I want to modify an object but I have an expression", the core of this logic is in the `accessObjectProperty` function which walks through the expression, finds all object or parameter references and does some operation on it.

For example, suppose we have a expression `if (x) { obj1 } else { obj2 }` and try to set the `field1` to `1`. The `setField` function will set the `obj1.field1` to `if (x) { 1 } else { old value of obj1.field1 }` and `obj2.field1` to `if (!x) { 1 } else { old value of obj2.field1 }`. If we'd try to read the value after the write, the `accessField` function will return `if (x) { value from obj1.field1 } else { value from obj2.field1 }`, which will be `if (x) { if (x) { 1 } else { old value of obj1.field1 } } else { if (!x) { 1 } else { old value of obj2.field1 } }`. After that, this expression is simplified into `1` by the expression simplifier. If the object would be shared, all writes and reads are a side-effect, so the `setField` or `accessField` might add some side-effects.

### State branching

When a branching instruction is encountered, the interpreter tries to figure out which way to go. In some cases, after simplification the expression is a constant (then it simply follows the path of the jump), but it's certainly not a general case. When an unresolvable branch is encountered, the state is forked and both branches are taken. When these branches make it to a common point (usually at end of the function) the states are merged together (using the `mergeStates` function). When the state is merged, the original state is referenced from it as a parent and most of the information is inherited, there is just the branching condition added as an assumption. When the states are merged, everything that was added or changed in the new states (compared to their parent) needs get a condition.

For example, suppose we are interpreting a function like this:

```F#
let x obj1 =
    obj1.field <- 3
    if obj1.field2 then
        obj1.field <- 4
```

It will contain a branch instruction that depends on the value of `obj1.field2` and suppose we don't know what's inside. First, we will set the `field` to a constant `3`. Then we will fork the state and in the first branch change it's value to `4`. When we come to the end of the function, we will merge the changes of the objects and assign conditional expression into the changed fields (it will be `field = if obj1.field then 4 else 3`).

### Method calls

Some instructions may need to invoke a method - in that case the interpreter calls itself recursively (via `ExecutionServices`). It simply gets a new ExecutionState from the recursion and continues in the execution.

In some cases, the method will not be interpretable (`FunctionTooComplicatedException` is thrown during the execution), which will force the interpreter to make a side effect from the invocation. It will be simply added to the list in `ExecutionState`.

When a virtual call is performed, we will try to devirtualize it in order to find what's inside that target method. Devirtualization is performed by analyzing the real type of the expression (basically looking for used objects in it) and if it fails, the call is also considered to be a side-effect

### Expression simplification

The expression simplifier is the core part of the entire system. It works by transforming the expression into different variants using a list of patterns and then choosing the "nicest one". This process is iterated until it can't find any nicest expression. The expressions are compared using the `ExprCompare` module, primarily by some ranking of nodes. The primary rank is a number of leaves in the tree, secondary one is a sum of individual rank of each node in the tree (this allows us to discourage the simplifier from some nodes).


