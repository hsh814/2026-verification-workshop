# Map data-structure exercises

Both exercises implement the same finite map from natural-number keys to
natural-number values:

```text
new_map : unit -> loc
insert  : (loc * (nat * nat)) -> unit
delete  : (loc * nat) -> unit
get     : (loc * nat) -> option nat
```

The common mathematical model is `gmap nat nat`. The public `is_map r m`
resource says that handle `r` currently represents `m`; operation
specifications use `∅`, `<[k := v]> m`, `delete k m`, and `m !! k`.

- `linked_list/` uses a heap-allocated linked list.
- `bst/` uses an unbalanced binary search tree.
- `try/` is a scaffold for a different representation of your choice.

The completed directories have the `_answer` suffix. The `linked_list/` and
`bst/` starters supply `MapHeader.v` and the complete `MapI.v` algorithm;
their common specification, logical resources, representation invariant, and
simulations are exercises. The `try/` directory instead supplies an empty
implementation skeleton for a representation of your choice. All three use
the same abstract API so clients do not depend on physical representation.
