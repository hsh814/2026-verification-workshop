# Linked-list map exercise

This exercise implements a finite `nat`-to-`nat` map with a linked list. The
implementation (`MapI.v`) and public signatures (`MapHeader.v`) are supplied.

Every map has a stable header cell containing the head pointer. Each node
stores:

```text
(key, (payload, next))
```

`Vnat value` is a live payload and `Vundef` is a tombstone. Deletion marks a
node instead of unlinking it. A later insertion of the same key revives that
node, so historical node keys remain unique.

Exercise order:

1. In `MapA.v`, define the common `is_map handle model` resource and write
   specifications for `new_map`, `insert`, `delete`, and `get`.
2. In `MapIAproof.v`, define the linked-node representation and `Ist`.
3. Prove the four simulations. The `find` iterator is proved by induction on
   the remaining logical node list, using a reconstruction wand for the
   prefix already traversed.
4. Finish `sim` and contextual refinement.

The invariant should combine one authoritative high-level `ghost_map` with a
`big_sepM` of concrete representations. This supports several live maps.
Never unfold `ghost_map` or memory resources into direct `own` assertions.

The completed solution is in `../linked_list_answer/`.
