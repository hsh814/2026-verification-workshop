From CRIS.common Require Import CRIS.
From prime_answer Require Export LListA PrimeHeader PrimeMath.

(** Supplied abstract behavior for the IO-facing prime calculator.

    [get_prime] is specification code: it observes the same input event as the
    implementation and returns the corresponding mathematical prime.  Its
    function specification transfers the linked-list fragment through the
    call boundary.  The program [main] receives the initial fragment, calls
    [get_prime], and prints its result. *)
Module PrimeA. Section PrimeA.
  Context `{!crisG Γ Σ α β τ _S _I, !llistGS}.

  Definition scopes := ["Prime"].

  (*** Specification-code behavior

  nat get_prime(void) {
    nat n = input();
    return (nth_prime n);
  }
  ***)
  Definition get_prime : unit -> itree crisE nat :=
    fun _ =>
      n <- trigger (IO "input" ());;
      Ret (nth_prime n).

  (** A call may replace the singleton logical list selected by its caller.
      The postcondition returns ownership of whichever list is selected when
      the call finishes. *)
  Definition get_prime_spec : fspec :=
    fspec_simple
      (fun old_state : llist_state =>
        ((fun arg =>
            ⌜arg = tt↑⌝ ∗ LListA.list_user old_state),
         (fun _ =>
            ∃ new_state,
              LListA.list_user new_state)))%I.

  Definition main : Any.t -> itree crisE Any.t :=
    fun _ =>
      prime <- ccallU PrimeHdr.get_prime tt;;
      '_ : unit <- trigger (@IO nat unit "print" prime);;
      Ret tt↑.

  (** Cancellation supplies [list_uninit] to the program entry.  The entry
      passes it to [get_prime] and returns the resulting fragment. *)
  Definition main_spec : fspec :=
    fspec_simple
      (fun _ : unit =>
        ((fun arg =>
            ⌜arg = tt↑⌝ ∗ LListA.list_uninit),
         (fun ret =>
            ⌜ret = tt↑⌝ ∗
            ∃ state,
              LListA.list_user state)))%I.

  Definition fnsems : fnsemmap :=
    {[entry #
        (msk_scp scopes msk_true,
          (fsp_some main_spec, main));
      fid PrimeHdr.get_prime #
        (msk_scp scopes msk_true,
          (fsp_some get_prime_spec,
            cfunU PrimeHdr.get_prime get_prime))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := LListA.frag_init.

  (** [PrimeA] is the source module cancelled in [PrimeAll].  Before
      cancellation, its map interprets both the entry and [get_prime]
      specifications. *)
  Definition t : Mod.t := SMod.to_mod (SMod.sp_from smod) smod.
End PrimeA. End PrimeA.
