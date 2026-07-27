(** * Linked-List Module Header *)

From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Export ImpPrelude.

(** The interface uses the Imp system's shared [val] type.  In particular,
    list locations are [Vptr] values returned by the memory module. *)

(** The linked-list module can create multiple independent lists.  Clients
    call [new] to create each list before using the other operations on it.
    The returned value denotes a stable location containing that list's
    current head pointer. *)
Module LListHdr.
  (** [new] allocates a new list and returns its stable location. *)
  Definition new := fnsig "LList.new" (fntyp unit val).

  (** [push_front] takes the list location and a value, then inserts the value
      at the front.  The list location itself does not change. *)
  Definition push_front :=
    fnsig "LList.push_front" (fntyp (val * nat) unit).

  (** [get] takes the list location and a zero-based index.  It returns
      [None] when the index is out of bounds. *)
  Definition get :=
    fnsig "LList.get" (fntyp (val * nat) (option nat)).

  (** A conventional linked-list interface might also provide operations such
      as [pop_front], [push_back], and [pop_back].  They are omitted because
      the prime-number example does not use them.  Interested participants
      may implement them and give them specifications as an extension. *)
End LListHdr.

(** * Notes **)

(** CRIS call events carry function arguments and return values in [Any.t].
    Declaring a function with a typed [fnsig] lets Rocq infer those argument
    and return types when the function is called from another function body. *)

(** As a separate organizational convention, collecting these function names
    and signatures in a header module is similar to using a header file in C. *)
