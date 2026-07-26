(** * Common Finite-Map Interface *)

From CRIS.common Require Import CRIS.
From mem Require Export MemHeader.

(** Both map exercises expose exactly this interface.  Keys and values are
    natural numbers; [get] returns [None] when the key is absent. *)
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
