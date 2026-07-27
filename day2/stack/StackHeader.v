(** * Linked-List Stack Interface

    This file is supplied.  Stack locations and node values come from the
    memory exercise, so finish that exercise first. *)

From CRIS.common Require Import CRIS.
From mem Require Export MemHeader.

Module StackHdr.
  Definition new_stack :=
    fnsig "Stack.new_stack" (fntyp unit loc).
  Definition push :=
    fnsig "Stack.push" (fntyp (loc * nat) unit).
  Definition pop :=
    fnsig "Stack.pop" (fntyp loc (option nat)).
End StackHdr.
