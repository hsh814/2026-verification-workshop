(** * Exercise 3: compose the proofs and cancel the specifications *)

From CRIS.common Require Import CRIS.
From CRIS.cancellation Require Import Cancel.
From CRIS.imp_system.mem Require Import MemA MemI.
From CRIS.imp_system.safe_mem Require Import MemNB MemINBproof.
From prime_safe_answer Require Import
  LListA LListI LListIAproof PrimeA PrimeI PrimeIAproof.

(** Cancellation is applied to the complete body-preserving source module.
    Consequently [sp] is exactly [SMod.sp_from smod_src]; it contains the
    specifications of [PrimeA], [LListA], and [MemNB].  Cancellation removes
    those specifications but retains all three concrete bodies. *)
Section PrimeSafeAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !memGS}.

  Local Definition smod_src : SMod.t :=
    PrimeA.smod ☆ LListA.smod ☆ MemNB.smod [].

  Local Definition sp : specmap := SMod.sp_from smod_src.

  Local Definition mod_src : Mod.t :=
    SMod.to_mod sp smod_src.

  Local Definition mod_top : Mod.t :=
    SMod.to_mod ∅ (SMod.cancel smod_src).

  Local Definition mod_tgt : Mod.t :=
    PrimeI.t ★ LListI.t ★ MemI.t [].

  Local Definition init_cond : iProp Σ := MemA.init_cond [].

  Lemma prime_in_sp : PrimeA.sp ⊆ sp.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l;
      last apply map_empty_subseteq. all: mod_tac.
  Qed.

  Lemma llist_in_sp : LListA.sp ⊆ sp.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l;
      last apply map_empty_subseteq. all: mod_tac.
  Qed.

  Lemma mem_in_sp : MemNB.sp ⊆ sp.
  Proof.
    split; et.
    repeat try eapply insert_subseteq_l;
      last apply map_empty_subseteq. all: mod_tac.
  Qed.

  Lemma cancel_src :
    (init_cond ∗ Cancel.init_res)%I ⊢
      (init_cond ∗ refines mod_src mod_top)%I.
  Proof.
    iIntros "[INIT CANCEL]". iFrame "INIT".
    rewrite /mod_src /mod_top /sp /smod_src.
    iApply refines_trans. iSplitR "CANCEL".
    { iApply ctxr_refines. iApply Cancel.prepare; et; clarify. }
    iApply Cancel.cancel.
    { repeat apply SMod.cancellable_add; r; mod_tac ss. }
    { assert (Ht : (SMod.sp_from smod_src).1 !! entry =
          fsp_some PrimeA.main_spec)
        by mod_tac.
      rewrite Ht; clear Ht.
      ss; exists tt; split; refl.
    }
    { unfoldPrePost. iIntros "% % H".
      iDestruct "H" as "(-> & _)". done. }
    iDestruct "CANCEL" as "(X & Y & Z & $ & $)".
    unfoldPrePost; done.
  Qed.

  (** Compose the body-preserving layers in this order:

        PrimeI ★ LListI ★ MemI
          <= PrimeI ★ LListI ★ MemNB
          <= PrimeI ★ LListA ★ MemNB
          <= PrimeA ★ LListA ★ MemNB.

      Every intermediate module uses the one map [sp], so the adjacent sides
      match exactly. *)
  Lemma src_tgt :
    init_cond ⊢ refines mod_tgt mod_src.
  Proof.
    iIntros "INIT". iApply ctxr_refines.
    rewrite /mod_tgt /mod_src /sp /smod_src !SMod.to_mod_add.
    iApply ctxr_trans. iSplitL "INIT".
    { iApply ctxr_frameL. iApply ctxr_frameL.
      iApply (MemINB.ctxr sp [] mem_in_sp with "INIT"). }
    iApply ctxr_trans. iSplitL "".
    { iApply ctxr_frameL.
      iApply (LListIA.ctxr sp llist_in_sp mem_in_sp). done. }
    iApply (PrimeIA.ctxr sp prime_in_sp llist_in_sp mem_in_sp). done.
  Qed.

  Lemma top_tgt :
    (init_cond ∗ Cancel.init_res)%I ⊢ refines mod_tgt mod_top.
  Proof.
    iIntros "R".
    iPoseProof (cancel_src with "R") as "[INIT REF2]".
    iPoseProof (src_tgt with "INIT") as "REF1".
    iApply refines_trans. iFrame.
  Qed.

  Lemma tgt_wf : Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt; eapply Mod.add_wf.
    { econs; eauto; [mod_tac | prove_nodup]. }
    { eapply Mod.add_wf.
      { econs; eauto; [mod_tac | prove_nodup]. }
      { econs; eauto; [mod_tac | prove_nodup]. }
      { mod_tac. }
      { prove_nodup; set_solver. }
    }
    { mod_tac. }
    { prove_nodup; set_solver. }
  Qed.
End PrimeSafeAux.

Module PrimeSafeAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ; memΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  (** The target is the original concrete program with unsafe memory.  The
      cancelled source keeps the same Prime, list, and safe-memory bodies,
      but all their specifications have disappeared. *)
  Theorem behavioral_refinement :
    ∃ β τ
      (Hinv : invGS Γ Σ α)
      (_ : crisG Γ Σ α β τ _ Hinv)
      (_ : memGS)
      src_res tgt_res,
      refines_lmod
        (Mod.to_lmod mod_tgt tgt_res)
        (Mod.to_lmod mod_top src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "[% [% [% [% CRIS]]]]".
    iMod (mem_alloc []) as "[% MEM]".
    iExists _, _, _, _, _.
    iDestruct "CRIS" as "[WINV [TID [YIELD [TIDAUTH YIELDAUTH]]]]".
    iPoseProof (winv_split_empty with "WINV") as "[WINV WINV_EMPTY]".
    iEval (rewrite /mem_init own_op) in "MEM".
    iDestruct "MEM" as "[MEM _]".
    iPoseProof (top_tgt with
      "[MEM TID YIELD WINV TIDAUTH YIELDAUTH]") as "REF".
    { rewrite /init_cond /MemA.init_cond /mem_init_auth /Cancel.init_res.
      iFrame. }
    iPoseProof (refines_adequacy mod_tgt mod_top tgt_wf with
      "[$WINV_EMPTY $REF]") as "%ADEQ".
    destruct ADEQ as [src_res [_ REF]].
    iExists src_res, ε. done.
  Qed.
End PrimeSafeAll.

(* Print Assumptions PrimeSafeAll.behavioral_refinement. *)
