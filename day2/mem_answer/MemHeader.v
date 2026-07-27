(** * A Small Memory Interface

    The workshop memory stores dynamically typed values.  Locations are
    natural numbers; [Vundef] is the value of a freshly allocated cell.
    [Vnat], [Vloc], and [Vpair] are enough to encode the linked-list stack in
    the next exercise. *)

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

Module MemHdr.
  Definition alloc :=
    fnsig "Mem.alloc" (fntyp unit loc).
  Definition load :=
    fnsig "Mem.load" (fntyp loc memval).
  Definition store :=
    fnsig "Mem.store" (fntyp (loc * memval) unit).
  Definition get_cnt :=
    fnsig "Mem.get_cnt" (fntyp unit nat).
End MemHdr.
