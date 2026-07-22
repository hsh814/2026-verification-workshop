From CRIS Require Import CRIS.

(** Two small compiler optimizations.  The first example has no module-local
    state, while the second introduces a simple state relation. *)

(** CRIS stores function bodies behind an [Any.t] interface.  This workshop
    tactic starts the simulation at the typed body and discharges the common
    ill-typed call case. *)
Ltac cStartTypedFunSim x :=
  cStartFunSim;
  cStepsS; cStepsT;
  lazymatch goal with
  | arg : Any.t |- _ =>
      destruct (Any.downcast arg) as [x|];
        cStepsS; [cStepsT|]; ss
  end.

(** Example 1: constant folding without module-local state. *)
Module PureOptHdr.
  Definition mn := "WorkshopPureOptimization".

  Definition fn (method : string) := mn +:+ "." +:+ method.

  Definition fold_constants := fnsig (fn "fold_constants") (fntyp () Z).
End PureOptHdr.

Module PureOptSource. Section PureOptSource.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [PureOptHdr.mn].

  Definition fold_constants : () -> itree crisE Z :=
    fun _ => Ret ((1 + 2)%Z).

  Definition fnsems : fnsemmap :=
    {[fid PureOptHdr.fold_constants #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU PureOptHdr.fold_constants fold_constants))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End PureOptSource. End PureOptSource.

Module PureOptTarget. Section PureOptTarget.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [PureOptHdr.mn].

  Definition fold_constants : () -> itree crisE Z :=
    fun _ => Ret 3%Z.

  Definition fnsems : fnsemmap :=
    {[fid PureOptHdr.fold_constants #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU PureOptHdr.fold_constants fold_constants))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End PureOptTarget. End PureOptTarget.

Module PureOptProof. Section PureOptProof.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Local Definition Source := PureOptSource.t.
  Local Definition Target := PureOptTarget.t.

  (** With no local state to track, the simulation invariant is trivial. *)
  Definition Ist : ist_type Σ := fun _ _ => True%I.

  Lemma simF_fold_constants :
    ISim.sim_fun open Source Target Ist (fid PureOptHdr.fold_constants).
  Proof using.
    cStartTypedFunSim u.
    unfold PureOptSource.fold_constants, PureOptTarget.fold_constants.
    cStep. iSplit; eauto.
  Qed.

  Lemma sim : ISim.t open Source Target emp%I Ist.
  Proof using.
    cStartModSim.
    - iIntros "_". done.
    - apply simF_fold_constants.
  Qed.

  Lemma ctxr : ⊢ ctx_refines Target Source.
  Proof using. eapply main_adequacy, sim. Qed.
End PureOptProof. End PureOptProof.

(** Example 2: store-to-load forwarding with matching local cells. *)
Module StateOptHdr.
  Definition mn := "WorkshopStateOptimization".

  Definition fn (method : string) := mn +:+ "." +:+ method.

  Definition store_load := fnsig (fn "store_load") (fntyp Z Z).
End StateOptHdr.

Module StateOptSource. Section StateOptSource.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [StateOptHdr.mn].
  Definition cell := StateOptHdr.mn ↯ "cell".

  Definition store_load : Z -> itree crisE Z :=
    fun x =>
      cput cell x;;;
      y <- cgetU cell;;
      Ret y.

  Definition fnsems : fnsemmap :=
    {[fid StateOptHdr.store_load #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU StateOptHdr.store_load store_load))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[cell # (0 : Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End StateOptSource. End StateOptSource.

Module StateOptTarget. Section StateOptTarget.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [StateOptHdr.mn].
  Definition cell := StateOptHdr.mn ↯ "cell".

  Definition store_load : Z -> itree crisE Z :=
    fun x =>
      cput cell x;;;
      Ret x.

  Definition fnsems : fnsemmap :=
    {[fid StateOptHdr.store_load #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU StateOptHdr.store_load store_load))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[cell # (0 : Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End StateOptTarget. End StateOptTarget.

Module StateOptProof. Section StateOptProof.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Local Definition Source := StateOptSource.t.
  Local Definition Target := StateOptTarget.t.

  (** The source and target cells always contain the same integer. *)
  Definition Ist : ist_type Σ :=
    fun st_src st_tgt =>
      (∃ x : Z,
        ⌜st_src = {[StateOptSource.cell # x↑]} /\
         st_tgt = {[StateOptTarget.cell # x↑]}⌝)%I.

  Lemma simF_store_load :
    ISim.sim_fun open Source Target Ist (fid StateOptHdr.store_load).
  Proof using.
    cStartTypedFunSim x.
    unfold StateOptSource.store_load, StateOptTarget.store_load.
    iDestruct "IST" as (old) "%". destruct H as [-> ->].
    cStepsS. cStepsT. cStep. iSplit; eauto.
  Qed.

  Lemma sim : ISim.t open Source Target emp%I Ist.
  Proof using.
    cStartModSim.
    - iIntros "_". iExists 0. done.
    - apply simF_store_load.
  Qed.

  Lemma ctxr : ⊢ ctx_refines Target Source.
  Proof using. eapply main_adequacy, sim. Qed.
End StateOptProof. End StateOptProof.
