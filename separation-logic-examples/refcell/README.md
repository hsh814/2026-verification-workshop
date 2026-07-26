# Fractional ownership and reference cells

This exercise has two stages:

1. `frac_mem/` extends the workshop memory specification with fractional
   points-to ownership. Its completed version is `frac_mem_answer/`.
2. `refcell/` uses that memory API to verify a dynamically checked reference
   cell. Its completed version is `refcell_answer/`.

Rust's
[`RefCell`](https://doc.rust-lang.org/std/cell/struct.RefCell.html) is a
mutable location whose borrowing rules are checked at run time. You do not
need to know Rust for this exercise. Think of a refcell at `r` as protecting
an internal memory location `l`:

- `try_borrow r` returns `Some l` when read-only access can be granted and
  `None` while a mutable borrow is active.
- Several read-only borrows may coexist. Each successful call returns a
  positive fractional points-to share.
- `try_borrow_mut r` returns `Some l` only when no borrow is active. Its
  caller receives full ownership and may both read and write.
- `drop r` ends one successful borrow and returns its permission to the
  refcell.

The term “reference count” in this exercise refers to the run-time count of
active shared borrows. It is not a garbage-collection or object-lifetime
reference count.

The intended proof uses high-level `ghost_map` resources. A persistent
`RefCell r l` records which location is protected. A linear
`Borrowed r q` ticket makes one successful borrow authorize exactly one
`drop`. The module-local simulation invariant owns the remaining fraction and
relates the physical counter to all outstanding tickets.
