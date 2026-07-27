# Unbalanced BST map exercise

This directory implements the same abstract finite-map interface as the
linked-list exercise, but stores historical keys in an unbalanced binary
search tree.

Each map handle owns a root-pointer cell. Each node stores a key, an optional
payload, and two child pointers. Deletion is deliberately *lazy*: it replaces
the payload with `Vundef`, leaving a tombstone that a later insertion may
revive. This keeps deletion focused on separation-logic reasoning instead of
tree surgery.

Suggested order:

1. Complete `MapA.v`, reusing exactly the abstract `gmap nat nat`
   specification from the linked-list exercise.
2. In `MapIAproof.v`, define a recursive tree resource and connect its lookup
   function to the abstract `gmap`.
3. State the module invariant `Ist`.
4. Prove the four operation simulations with CRIS and Iris tactics.
5. Finish the module simulation and contextual-refinement theorem.

The completed version is in `../bst_answer/`.
