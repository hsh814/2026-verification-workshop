# nth-prime workshop solution

This exercise verifies a small client and a linked-list library in two layers:

1. Give the linked-list API an Iris resource model and prove that the supplied
   Imp-memory implementation refines it.
2. Verify the IO-facing `get_prime` against supplied pure specification code
   while calling the resource-level linked-list API.
3. Compose the implementation refinements, cancel the final abstract module,
   and derive behavioral refinement for the linked program.

The index is zero based: `nth_prime 0 = 2`, `nth_prime 1 = 3`, and so on.  The
calculator therefore searches candidates from `2` until it has found `n + 1`
primes.  Iterating only from `2` through `n` would solve the different problem
of enumerating primes bounded by `n`.

The concrete linked-list module can allocate multiple list instances.  Each
call to `new` allocates and returns a stable location for a fresh list.  The
exercise resource model intentionally tracks only the most recently selected
instance: calling `new` consumes the current singleton state and replaces it
with `is_list l []`.  The head pointer stored at `l` changes when a value is
inserted, but `l` itself remains fixed.  The API is:

```text
new        : unit -> val
push_front : (val * nat) -> unit
get        : (val * nat) -> option nat
```

The shared `ImpPrelude.val` type is used for all pointers; the workshop does
not define a second value type.  The stable list location is one Imp-memory
cell containing the head pointer.  Each node is a two-cell allocation holding
the integer value and next pointer.  The implementation uses
`MemHdr.alloc`, `MemHdr.load`, and `MemHdr.store` throughout.

The linked list inserts at its head.  Since candidates are considered in
increasing order, its contents are sorted in descending order (largest/newest
prime first).  `first_primes_desc` is the supplied mathematical model of that
list.  `get (l, i)` traverses from the head and returns `None` when `i` is out
of bounds.  This is less efficient than exposing an iterator, but it gives
beginners a small, familiar interface and keeps cursor resources out of the
exercise.

Initially, the client owns the `None` fragment.  A call to `new` consumes the
current fragment—whether `None` or a previously tracked list—and produces
`is_list l []` for the new list.  Subsequent operations preserve `l` while
changing or observing its logical contents.  A generalized design could use
an authoritative finite map to retain resources for all allocated lists, but
that extension is not required here.

The two proof layers deliberately start with different resource halves.
`LListIA` consumes `auth_init`, while `PrimeIA` consumes `frag_init`.  Neither
source module includes its auxiliary module: `LListIA` inlines target calls to
`MemA`, and `PrimeIA` inlines target calls to `LListA`.  The final theorem
frames the authoritative half around the client refinement and uses
`init_cond = frag_init ∗ auth_init`.

The mathematical Rocq function `nth_prime n` remains parameterized by an
index.  The executable calculator instead has type `get_prime : unit -> nat`:
it obtains `n` from the observable `IO "input"` event.  Because the input is
inside the function behavior, its expected behavior is given as an abstract
ITree rather than an `fspec_simple`.

## Files

- `PrimeMath.v`: supplied executable prime definition, Euclid termination
  argument, `next_prime`, `nth_prime`, and helper lemmas.
- `LListHeader.v`: supplied linked-list function names and typed signatures.
- `PrimeHeader.v`: supplied prime-function name and typed signature.
- `LListI.v`: supplied concrete ITree implementation over Imp memory.
- `LListA.v`: the solved resource algebra, resources, update lemmas, and
  resource-level function specifications.
- `LListIAproof.v`: solved function simulations, module simulation, and
  linked-list contextual refinement.
- `PrimeI.v`: supplied IO-facing prime-calculator ITree.
- `PrimeA.v`: supplied pure specification ITree:

  ```coq
  fun _ =>
    n <- trigger (IO "input" ());;
    Ret (nth_prime n)
  ```

- `PrimeIAproof.v`: the solved client proof against `LListA`.
- `PrimeAll.v`: memory abstraction, proof-layer composition,
  cancellation, and the final behavioral-refinement theorem.

## Build

From the CRIS-examples repository root, with the workshop opam switch active:

```sh
make workshop/prime_answer/PrimeAll.vo
```

For a faster dependency check while working, build the file currently being
edited, for example:

```sh
make workshop/prime_answer/LListA.vo
make workshop/prime_answer/LListIAproof.vo
make workshop/prime_answer/PrimeIAproof.vo
```

## Suggested order and hints

1. In `LListA.v`, choose a singleton resource state that distinguishes the
   uninitialized module from an initialized list at location `l` with logical
   contents `values`.  The library owns the authoritative half and the client
   owns the matching fragment.  Prove agreement and a joint update lemma
   before simulation.  Keep the supplied `auth_init` and `frag_init` split:
   it is needed for final composition.
2. In `LListIAproof.v`, prove `new` and `push_front` first using the memory
   tactics.  Then prove `get` by following the supplied `nodes` predicate and
   inducting over the index.  Preserve the stable list location through both
   operations.  An index past the null pointer returns `None`.
3. In `PrimeIAproof.v`, keep the ITree proof separate from the number theory.
   State an outer invariant involving `first_primes_desc`, then an inner
   invariant for the indexes already checked.  Each `get` preserves the same
   list resource.  The divisibility loop belongs entirely to `PrimeI`.
4. Finish the `get_prime` simulation by relating the concrete result to the
   abstract `nth_prime` return.  In `PrimeAll.v`, compose
   `MemIA`, `LListIA`, and `PrimeIA`, then apply `Cancel.prepare` and
   `Cancel.cancel` to the remaining `PrimeA` source module.  Use separate
   specification maps derived from `PrimeA.smod`, `LListA.smod`, and
   `MemA.smod`; the prime map must exactly match the source module when
   applying cancellation.

Good nearby references in `../CRIS-examples` are:

- `sequential/celliocb/CellioA.v` and `CellioIAproof.v` for a small
  authoritative-resource simulation;
- `sequential/map/MapA.v` and `MapIAproof.v` for a larger resource API and a
  transitive contextual-refinement proof;
- `sequential/repeat/RepeatIAproof.v` for an iterator/client simulation.
