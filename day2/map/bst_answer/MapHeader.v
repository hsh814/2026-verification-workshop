(** * Finite-Map Interface *)

From CRIS.common Require Import CRIS.
From mem_answer Require Export MemHeader.

(** The same abstract interface is used by the linked-list and BST
    implementations.  Handles and keys are natural numbers because workshop
    memory locations are natural numbers. *)
Module MapHdr.
  Definition new_map :=
    fnsig "Map.new_map" (fntyp unit loc).
  Definition insert :=
    fnsig "Map.insert" (fntyp (loc * (nat * nat)) unit).
  Definition delete :=
    fnsig "Map.delete" (fntyp (loc * nat) unit).
  Definition get :=
    fnsig "Map.get" (fntyp (loc * nat) (option nat)).
End MapHdr.
