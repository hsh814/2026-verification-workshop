# Try your own map representation

This directory is an intentionally empty scaffold for a third implementation
of the workshop map interface.

Suggested order:

1. Complete the common `gmap nat nat` specification in `MapA.v`.
2. Choose a representation: a sorted list, hash buckets, a trie, an array for
   bounded keys, or something else supported by the workshop memory values.
3. Implement the four operations in `MapI.v`.
4. Define `map_rep` and `Ist` in `MapIAproof.v`.
5. Prove the four function simulations, module simulation, and `ctxr`.

Keep the public `is_map r m` specification independent of the physical
representation. The suggested authoritative `ghost_map` allows several maps
to be live at once; the invariant should own a separating representation for
every handle in that registry.

Use only the high-level memory and ghost-resource APIs. During proof
development, step through the files with Coqtail instead of repeatedly
compiling the whole collection.
