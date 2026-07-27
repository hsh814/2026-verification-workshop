(** * A Fractional-Permission Memory Interface

    Locations are natural numbers and memory cells contain dynamically typed
    values.  The abstract specification in [FracMemA] exposes fractional
    points-to resources for shared reads and requires full ownership for
    writes. *)

From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Export ImpPrelude.

Definition loc : Type := nat.

Global Instance loc_eq_dec : EqDecision loc := Nat.eq_dec.
Global Instance loc_countable : Countable loc := nat_countable.

Inductive memval : Type :=
| Vundef
| Vnat (n : nat)
| Vloc (l : option loc)
| Vpair (left right : memval).

Global Instance memval_eq_dec : EqDecision memval.
Proof. solve_decision. Defined.

Module FracMemHdr.
  Definition alloc :=
    fnsig "FracMem.alloc" (fntyp unit loc).
  Definition load :=
    fnsig "FracMem.load" (fntyp loc memval).
  Definition store :=
    fnsig "FracMem.store" (fntyp (loc * memval) unit).
  Definition get_cnt :=
    fnsig "FracMem.get_cnt" (fntyp unit nat).
End FracMemHdr.
