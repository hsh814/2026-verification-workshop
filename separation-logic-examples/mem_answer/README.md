# Memory exercise — answer

This directory contains the completed memory module used in the separation
logic workshop.

- `MemHeader.v` defines locations, memory values, and the four public
  operations.
- `MemI.v` implements a finite heap and an access counter.
- `MemA.v` specifies cells with CRIS's high-level `ghost_map` resource and
  counter observations with the persistent `mono_nat` snapshot.
- `MemIAproof.v` proves the implementation contextually refines the
  separation-logic specification.

`load` and `store` increment the counter. `alloc` and `get_cnt` do not.
Consequently, two calls to `get_cnt` around arbitrary verified code can use
their persistent snapshots to prove that the second result is no smaller.
`mem_alloc` supplies the initial `count_snapshot 0`, which bootstraps the
first call.
