From CRIS Require Import CRIS.

Set Implicit Arguments.

Local Open Scope Z_scope.

(** The smallest examples in the workshop are still modules.  Keeping the
    module wrapper visible makes the direction of [ISim.sim_fun] explicit:
    its source argument is the specification and its target argument is the
    implementation. *)
Module CasesHdr.
  Definition mn := "WorkshopCases".

  Definition fn (method : string) := mn +:+ "." +:+ method.

  Definition ret_tau := fnsig (fn "ret_tau") (fntyp () Z).
  Definition choose_zero := fnsig (fn "choose_zero") (fntyp () Z).
End CasesHdr.

Module CasesSource. Section CasesSource.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition ret_tau : () -> itree crisE Z :=
    fun _ => Ret 42.

  Definition choose_zero : () -> itree crisE Z :=
    fun _ =>
      'b : bool <- trigger (Choose bool);;
      Ret (if b then (0 : Z) else (1 : Z)).

  Definition fnsems : fnsemmap :=
    {[ fid CasesHdr.ret_tau #
         (msk_scp [] msk_true, (fsp_none, cfunU CasesHdr.ret_tau ret_tau));
       fid CasesHdr.choose_zero #
         (msk_scp [] msk_true,
          (fsp_none, cfunU CasesHdr.choose_zero choose_zero)) ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CasesSource. End CasesSource.

Module CasesTarget. Section CasesTarget.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition ret_tau : () -> itree crisE Z :=
    fun _ => Tau (Tau (Ret 42)).

  Definition choose_zero : () -> itree crisE Z :=
    fun _ => Ret 0.

  Definition fnsems : fnsemmap :=
    {[ fid CasesHdr.ret_tau #
         (msk_scp [] msk_true, (fsp_none, cfunU CasesHdr.ret_tau ret_tau));
       fid CasesHdr.choose_zero #
         (msk_scp [] msk_true,
          (fsp_none, cfunU CasesHdr.choose_zero choose_zero)) ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CasesTarget. End CasesTarget.

Module CasesProof. Section CasesProof.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition Ist : ist_type Σ :=
    fun st_src st_tgt => ⌜st_src = ∅ /\ st_tgt = ∅⌝%I.

  Local Definition Source := CasesSource.t.
  Local Definition Target := CasesTarget.t.

  (** Pair 0: target-only [Tau] steps are silent. *)
  Lemma simF_ret_tau :
    ISim.sim_fun open Source Target Ist (fid CasesHdr.ret_tau).
  Proof using.
    cStartFunSim. unfold CasesSource.ret_tau, CasesTarget.ret_tau.
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    cStepsT. cStep. iSplit; eauto.
  Qed.

  (** Pair 3: source-side [Choose] is existential.  The deterministic
      implementation is justified by selecting [true] in the source. *)
  Lemma simF_choose_zero :
    ISim.sim_fun open Source Target Ist (fid CasesHdr.choose_zero).
  Proof using.
    cStartFunSim. unfold CasesSource.choose_zero, CasesTarget.choose_zero.
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    cForceS true. cStep. iSplit; eauto.
  Qed.

  Lemma sim : ISim.t open Source Target emp%I Ist.
  Proof using.
    cStartModSim.
    - iIntros "_". iPureIntro. split; reflexivity.
    - apply simF_ret_tau.
    - apply simF_choose_zero.
  Qed.

  (** Adequacy reverses the presentation order: target first, source second. *)
  Lemma ctxr :
    ctx_refines (Target, emp%I) (Source, emp%I).
  Proof using. eapply main_adequacy, sim. Qed.
End CasesProof. End CasesProof.
