# Prime with safe memory — problem set

This exercise proves memory safety while preserving the program bodies all
the way through cancellation.

The three concrete target modules are:

```text
PrimeI ★ LListI ★ MemI
```

`PrimeA` and `LListA` contain exactly the same bodies as `PrimeI` and
`LListI`, respectively, but attach Iris specifications to them. `MemNB` is
the supplied body-preserving safe-memory layer: it has the memory bodies and
the `MemA` specifications, and replaces undefined memory behavior with
`triggerNB`.

`PrimeI` and `PrimeA` both contain a distinguished program entry. It calls
`Prime.get_prime` and emits an `IO "print"` event with the returned natural
number. `PrimeA.main_spec` is attached to that entry, so cancellation cannot
succeed by silently treating a missing entry as `fsp_none`.

The intended refinement chain is:

```text
PrimeI ★ LListI ★ MemI
  <= PrimeI ★ LListI ★ MemNB
  <= PrimeI ★ LListA ★ MemNB
  <= PrimeA ★ LListA ★ MemNB
  <= cancel (PrimeA ☆ LListA ☆ MemNB)
```

All body-preserving modules use the single specification map
`SMod.sp_from (PrimeA.smod ☆ LListA.smod ☆ MemNB.smod [])`. This exact map
is then passed to the cancellation theorem.

## Exercises

1. In `LListIAproof.v`, prove the three list operations from the supplied
   `LListA` specifications. The list predicate directly owns `MemA`
   points-to assertions; no custom resource algebra is needed. Use ordinary
   simulation steps and matched calls rather than `MemTactics`.
2. In `PrimeIAproof.v`, prove the prime client's safety specification. The
   key invariant is `length values = found`, which rules out the unsafe
   `None` branch in `has_divisor`. Then prove the entry by matching its
   `get_prime` call with `cCall` and matching the print event.
3. In `PrimeAll.v`, prove the three specification-map inclusions, compose
   `MemINB`, `LListIA`, and `PrimeIA`, and cancel the complete source module.
   The cancellation proof must find `fsp_some PrimeA.main_spec` at `entry`.

`PrimeMath.v` remains in the directory to preserve the layout of the
original prime example, but this safety-only exercise should not require its
number-theoretic lemmas.

All intended student proof holes are marked with `TODO` and `Admitted`.
