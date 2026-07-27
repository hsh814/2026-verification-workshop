# Verified finite map: unbalanced BST answer

This directory contains a complete refinement proof for a finite map with the
public operations

```text
new_map : unit -> loc
insert  : loc * (nat * nat) -> unit
delete  : loc * nat -> unit
get     : loc * nat -> option nat
```

The abstract contents of each handle are a `gmap nat nat`.  `is_map h m` is
an exclusive `ghost_map_elem` fragment, so clients can own and use several
independent map handles at once.  The module invariant owns the corresponding
authoritative handle-to-model map and a `big_sepM` of concrete
representations.  The specification and proof use only the high-level
`ghost_map` interface.

The implementation uses `mem_answer`.  A stable header cell stores the
optional root pointer.  Each unbalanced BST node occupies one cell encoded as

```text
(key, (payload, (left, right)))
```

where a live payload is `Vnat value` and `Vundef` is a deletion tombstone.
Insertion revives a tombstoned node in place; deletion does not restructure
the tree.  Lookup and deletion iterate over optional child pointers, and
insertion allocates and links a leaf when it reaches a missing child.

Files:

- `MapHeader.v` — typed public function signatures.
- `MapA.v` — representation-independent resource specification and ghost
  allocation.
- `MapI.v` — concrete BST implementation over `mem_answer`.
- `MapIAproof.v` — BST ordering/model lemmas, concrete representation,
  multi-map invariant, all four function simulations, and contextual
  refinement.

There are no admitted proofs.  `Print Assumptions MapIA.ctxr` reports only the
standard axioms already used by CRIS/Iris (proof irrelevance, extensionality,
classical/description principles, and itree bisimulation equality).

From the workshop root, a focused final check is:

```sh
make COQC=_opam/bin/coqc \
  separation-logic-examples/map/bst_answer/MapIAproof.vo
```
