# Prime with safe memory — answer set

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

## Proof structure

1. `LListIAproof.v` proves the three list operations from the supplied
   `LListA` specifications. The list predicate directly owns `MemA`
   points-to assertions, so no custom resource algebra is needed.
2. `PrimeIAproof.v` proves the prime client's safety specification. Its key
   invariant is `length values = found`, which rules out the unsafe `None`
   branch in `has_divisor`. It then proves the entry by matching the
   `get_prime` call with `cCall` and matching the print event.
3. `PrimeAll.v` proves the specification-map inclusions, composes `MemINB`,
   `LListIA`, and `PrimeIA`, and cancels the complete source module. The
   cancellation proof looks up `fsp_some PrimeA.main_spec` at `entry`.

The simulations use `IstProd` to separate each changing module from its
shared suffix. Calls into that suffix are matched in lock step with `cCall`;
the shared functions themselves are handled by `cStartModSim`.

`PrimeMath.v` remains in the directory to preserve the layout of the
original prime example, but this safety-only proof does not use its
number-theoretic lemmas.
