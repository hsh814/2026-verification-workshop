# Verified linked-list map

This directory contains the completed linked-list implementation of the
workshop's finite map from natural-number keys to natural-number values:

```text
new_map : unit -> loc
insert  : (loc * (nat * nat)) -> unit
delete  : (loc * nat) -> unit
get     : (loc * nat) -> option nat
```

The public model is `gmap nat nat`. A full `is_map handle model` resource
gives a client exclusive access to one map, while the authoritative outer
`ghost_map` records every live handle. The simulation invariant owns a
`big_sepM` of concrete representations, so several maps may coexist.

Each map has a stable header cell containing its list head. A node contains
`(key, (payload, next))`; `Vnat value` is live and `Vundef` is a tombstone.
Historical keys are unique. Insertion scans until it finds the key, updates
or revives that node, and allocates a new head only after reaching the end
without a match. Deletion writes a tombstone, and lookup interprets either
payload form.

`MapIAproof.v` relates the physical list to the abstract map. Its iterator
proofs induct over the unvisited suffix and carry a linear reconstruction
frame for the traversed prefix. The proof uses only the public memory and
`ghost_map` interfaces.

Files:

- `MapHeader.v` defines the four public function signatures.
- `MapA.v` defines the abstract resources and operation specifications.
- `MapI.v` implements the linked-list map.
- `MapIAproof.v` proves all function simulations, the module simulation, and
  contextual refinement.
