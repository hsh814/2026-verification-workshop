# Memory module workshop exercise

This is the first separation-logic exercise. It builds a small memory module
with four operations:

```text
alloc   : unit -> loc
load    : loc -> memval
store   : (loc * memval) -> unit
get_cnt : unit -> nat
```

`load` and `store` increment the access counter. `alloc` and `get_cnt` do not.
The specification exposes individual cells as linear `l ↦ v` resources and
counter observations as persistent lower-bound snapshots.
`mem_alloc` supplies the bootstrap `count_snapshot 0`; retain that persistent
snapshot to satisfy the first `get_cnt` precondition.

The point of the exercise is to use CRIS's high-level libraries:

- `ghost_map` for the authoritative heap and exclusive per-cell fragments;
- `mono_nat` for an authoritative counter and persistent lower bounds.

Do not unfold either library to low-level `own` expressions.

## Files and exercise order

1. Read `MemHeader.v` and `MemI.v`; both are supplied.
2. In `MemA.v`, complete `pointsto` and `mem_alloc`.
3. In `MemIAproof.v`, complete `Ist`, the four function simulations, the
   module simulation, and contextual refinement.

Every intended edit location starts with `TODO` and is followed by
`Admitted`. The starter therefore compiles before any exercises are solved.
Keep the imports under `From mem`; importing `mem_answer` would silently mix
the solution into the exercise.

Useful high-level lemmas include:

```coq
ghost_map_alloc_empty
ghost_map_insert
ghost_map_lookup
ghost_map_update
mono_nat_own_alloc
mono_nat_own_update
mono_nat_lb_own_valid
mono_nat_lb_own_get
```

After compiling dependencies once, use Coqtail's `rocq_start`,
`rocq_step_to`, and `rocq_goals` loop on the file you are editing, stepping to
the next `Admitted`. Use `cStartFunSim`, `cStepsS`, `cStepsT`, `cForceS`,
`cForceT`, and Iris tactics such as `iIntros`, `iDestruct`, and `iMod`.

From the repository root, the full exercise collection builds with:

```sh
make day2
```

The completed version is in `../mem_answer/`.
