# Dynamically checked reference-cell exercise

This exercise does not assume Rust knowledge. Think of a reference cell as a
memory location protected by a small runtime borrow counter:

- `try_borrow r` returns `Some l` when read-only access to `l` is safe, and
  `None` while mutable access is active.
- `try_borrow_mut r` returns `Some l` when exclusive read-write access is
  safe, and `None` while any borrow is active.
- `drop r` finishes one successful borrow and updates the counter.

The counter describes *active borrows*; it is not an object-lifetime reference
count.

The specifications in `RefCellA.v` are already supplied. Your work is to:

1. Define the persistent `RefCell r l` fact and the linear `Borrowed r q`
   ticket with `ghost_map`.
2. Design the shared and mutable representations in `RefCellIAproof.v`.
3. State `Ist`, keeping every mutable points-to assertion inside it.
4. Prove all four operation simulations and contextual refinement.

The key accounting equation is:

```text
sum(active shared-borrow fractions) + residual fraction = 1
```

In mutable mode the unique borrower owns fraction `1`, so the invariant owns
no fraction of the protected location.

The completed version is in `../refcell_answer/`.
