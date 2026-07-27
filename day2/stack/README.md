# Linked-list stack workshop exercise

This is the second separation-logic exercise. It deliberately imports the
problem-set memory API from `../mem/`, so complete the memory exercise first.
The stack implementation never opens the concrete memory state; its proof
uses only the `MemA` specifications and `l ↦ v` resources from Exercise 1.

The public API is:

```text
new_stack : unit -> loc
push      : (loc * nat) -> unit
pop       : loc -> option nat
```

For a compact workshop exercise, stack elements specialize the slide's
generic values to `nat`.

The mathematical list is top-first: `value :: values` means `value` is
popped next. This is a LIFO stack. `pop` uses `option nat`, with `None` for an
empty stack and `Some value` otherwise. This uniform return type replaces the
slide draft's heterogeneous pseudocode result (`()` or a value).

## Representation

A stable header cell contains `Vloc head`. Each nonempty linked-list node
contains:

```text
Vpair (Vnat value) (Vloc next)
```

Thus `new_stack` allocates one header cell. Each `push` allocates one node.
`pop` advances the header; it need not reclaim the old node because this
memory API has no `free`. The popped node is intentionally left allocated;
discarding its affine points-to resource is sound.

## Files and exercise order

1. Read the supplied `StackHeader.v` and `StackI.v`.
2. In `StackA.v`, define `linked_list` and `is_stack`, then read the supplied
   operation specifications.
3. In `StackIAproof.v`, define `Ist`, prove `new_stack`, then `push`, then
   both branches of `pop`, and finally prove module simulation and contextual
   refinement.

Every intended edit location starts with `TODO` and is followed by
`Admitted`. Use high-level CRIS tactics (`cStartFunSim`, `cStepsS`,
`cStepsT`, `cInlineT`, `cForceS`, `cForceT`) and Iris proof-mode tactics.
Do not unfold memory resources or reason directly about `own`.
Keep the imports under `From mem` and `From stack`; importing an `_answer`
namespace would silently mix the solution into the exercise.

The final theorem in `StackIAproof.v` is intentionally layered:
`StackI ★ MemA` refines `StackA`. In other words, the stack implementation is
proved against the Task 1 memory specification; the separate `MemIA` theorem
can later be used to replace that specification with the concrete memory
implementation.

From the repository root, build all starter and answer files with:

```sh
make day2
```

The completed version is in `../stack_answer/`; it imports `../mem_answer/`
so the two answer trees are independent of the starter files.
