From CRIS.common Require Import CRIS.
From prime Require Export PrimeHeader PrimeMath.

(** Supplied abstract behavior for the IO-facing prime calculator.

    This is specification code rather than an [fspec].  It observes the same
    input event as the implementation, chooses an abstract return value, and
    uses the pure [guarantee] event to constrain that value.  No Iris resource
    is involved in this postcondition. *)
Module PrimeA. Section PrimeA.
  Context `{!crisG Γ Σ α β τ _S _I}.

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

  Definition fnsems : fnsemmap :=
    {[fid PrimeHdr.get_prime #
        (msk_scp scopes msk_true,
          (None, cfunU PrimeHdr.get_prime get_prime))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := emp%I.

  (** [PrimeA] is the source module that is cancelled in [PrimeAll].  Using
      the specification map derived from the source module is the standard
      pre-cancellation form, even though [PrimeA] itself declares no
      function specifications. *)
  Definition t : Mod.t := SMod.to_mod (SMod.sp_from smod) smod.
End PrimeA. End PrimeA.
