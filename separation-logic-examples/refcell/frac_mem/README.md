# Fractional memory exercise

This first refcell exercise extends the earlier `mem` module with fractional
points-to ownership. The executable heap is unchanged; only the logical
permissions become more expressive.

The supplied specification uses:

```text
l ↦{q} v    fraction q : Qp of cell l containing v
l ↦ v       full ownership (q = 1)
```

`load` accepts any positive fraction and returns the same share. `store`
still requires full ownership. Thus a fraction smaller than one behaves like
a read-only permission: it is enough to read, but not enough to update.

Complete `FracMemA.v` first:

1. Define fractional `pointsto` with `ghost_map_elem`.
2. Register its `Fractional` and `AsFractional` instances.
3. Prove the split/merge and same-location validity rules.
4. Complete `frac_mem_alloc`.

Then complete the invariant and simulations in `FracMemIAproof.v`. Most of
that file is deliberately a copy of the earlier memory proof; the important
difference is that the `load` fragment now carries an arbitrary `q`.

Use the high-level lemmas `ghost_map_elem_valid_2`,
`ghost_map_insert`, `ghost_map_lookup`, and `ghost_map_update`. Do not unfold
the resource into a direct `own` assertion.

After compiling dependencies once, iterate with Coqtail:
`rocq_start`, `rocq_step_to`, and `rocq_goals`. The complete solution is in
`../frac_mem_answer/`.

From the repository root, all separation-logic examples build with:

```sh
opam exec --switch=. -- make sl
```
