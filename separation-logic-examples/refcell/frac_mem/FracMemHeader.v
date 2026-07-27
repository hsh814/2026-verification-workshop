(** * Exercise 1: A Fractional-Permission Memory Interface

    Locations are natural numbers and cells contain dynamically typed values.
    This interface is intentionally the same concrete memory as the earlier
    [mem] exercise; only its separation-logic ownership rules change. *)

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
