# Fractional memory — answer

This directory contains the complete fractional-permission variant of the
workshop memory module.

The public interface is:

```text
alloc   : unit -> loc
load    : loc -> memval
store   : (loc * memval) -> unit
get_cnt : unit -> nat
```

`l ↦{q} v` owns fraction `q : Qp` of cell `l` and records that its value is
`v`. The shorthand `l ↦ v` means full ownership (`q = 1`). Full ownership can
be split into positive shares, and shares can be merged by
`pointsto_split_merge`. Any two compatible shares for the same location agree
on the value; `pointsto_agree_valid` also states that their fractions sum to at
most one.

`load` accepts and returns any fraction. `alloc` returns full ownership and
`store` requires and returns full ownership. Consequently, clients may share
read access, but they must reassemble all outstanding shares before writing.
The concrete implementation does not store fractions: `ghost_map` enforces
the permissions in the abstract proof.

`load` and `store` increment the access counter. Persistent
`count_snapshot n` resources record lower bounds on that counter.

The proof uses CRIS's high-level `ghost_map` and the local `mono_nat` wrapper;
it never unfolds either resource into raw `own` expressions.

From the repository root, the full separation-logic collection builds with:

```sh
make day2
```
