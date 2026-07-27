# Linked-list stack exercise — answer

This directory contains the completed second separation-logic exercise.
It imports the verified memory API from `mem_answer` and never opens the
memory implementation.

- `StackHeader.v` defines `new_stack`, `push`, and `pop`.
- `StackI.v` implements a linked-list stack using `Mem.alloc`, `Mem.load`,
  and `Mem.store`.
- `StackA.v` defines `linked_list` and the abstract predicate
  `is_stack l values`, then gives operation specifications.
- `StackIAproof.v` proves the implementation refines those specifications
  using high-level CRIS and Iris tactics.

The mathematical list is top-first (LIFO). `pop` returns `option nat`; this
resolves the slide draft's heterogeneous pseudocode result (`()` when empty,
a value when nonempty) while preserving its intended behavior. The slide's
generic element type is specialized to `nat`.

Because the memory API has no `free`, `pop` advances the header and
intentionally leaves the old node allocated; its affine points-to resource
may be discarded. The proved theorem is layered over `MemA`:
`StackI ★ MemA` refines `StackA`, ready for later composition with the
separate `MemIA` refinement.
