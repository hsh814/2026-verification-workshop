(** * Prime-Number Module Header *)

From CRIS.common Require Import CRIS.

Module PrimeHdr.
  (** Return the prime number at the zero-based index supplied by the
      observable input event. *)
  Definition get_prime := fnsig "Prime.get_prime" (fntyp unit nat).
End PrimeHdr.
