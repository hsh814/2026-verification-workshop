# RefCell answer

This directory verifies a small dynamically checked reference cell on top of
the fractional-memory interface in `../frac_mem_answer`.

The concrete header is stored at `r` and protects a separate value cell `l`.
It contains either a natural number (the number of active shared borrows) or
`Vundef` (one active mutable borrow). The public assertion `RefCell r l` is
persistent, so clients may retain and duplicate the handle description.

Each successful borrow also returns `Borrowed r q`. Internally, this is a
full, indivisible entry in a per-cell ghost map. Its hidden identifier makes
one ticket authorize exactly one `drop`; duplicating or dropping the same
borrow twice is impossible.

## Invariant

`RefCellIAproof.v` keeps a persistent outer registry

```text
r ↦ (l, γb)
```

and a separating conjunction of representations for all registered cells.
Every representation owns the full concrete header and the authoritative
per-cell ticket map `bs`.

In shared mode it additionally owns a residual fraction `q0` of the protected
cell and records:

```text
header count = size bs
sum (fractions in bs) + q0 = 1
every fraction in bs is strictly below 1
```

The sum uses canonical rationals (`Qc`) because the empty sum is zero while
`Qp` contains only positive rationals. A successful `try_borrow` halves the
residual fraction, inserts one fresh ticket for one half, and gives the other
half to the caller. This can be repeated for arbitrarily many simultaneous
shared borrows.

In mutable mode the ticket map is exactly `{ id ↦ 1 }` and the invariant owns
no protected-cell fraction; the unique caller owns the full points-to
assertion. Consequently, `try_borrow_mut` succeeds exactly when the shared
ticket map is empty.

`drop` looks up and deletes the supplied full ticket. In shared mode it merges
exactly that ticket's caller-owned fraction into the residual fraction and
decrements the concrete count. In mutable mode it deletes the singleton
ticket, returns the caller's full points-to assertion to the invariant, and
restores shared mode with count zero.

## Files

- `RefCellHeader.v` defines the four function signatures.
- `RefCellI.v` implements `new_refcell`, `try_borrow`,
  `try_borrow_mut`, and `drop`.
- `RefCellA.v` defines the ghost state, persistent `RefCell`, linear
  `Borrowed`, and the abstract specifications.
- `RefCellIAproof.v` defines the invariant and proves contextual refinement
  against `RefCellI.t ★ FracMemA.t`.

The proof uses only the high-level `ghost_map` and fractional points-to APIs;
it contains no direct low-level ghost ownership and no admitted obligations.
