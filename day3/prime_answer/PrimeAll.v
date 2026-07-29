(** * Cancellation and final composition *)

From CRIS.common Require Import CRIS.
From CRIS.cancellation Require Import Cancel.
From CRIS.imp_system.mem Require Import MemI MemA MemIAproof.
From prime_answer Require Import
  LListA LListI LListIAproof PrimeA PrimeI PrimeIAproof.

(** Exercise 4 links the proof layers and then cancels the final abstract
    module.

    [LListA] is an internal proof layer, not part of [smod_src].  The
    [PrimeIA] refinement inlines calls to [LListA] on its target side and
    removes that auxiliary module.  Consequently, the abstract module left
    for cancellation is [PrimeA] alone.

    Each abstraction boundary has its own specification map.  This makes the
    intermediate modules match exactly during composition and leaves
    [sp_prime] exactly equal to [SMod.sp_from smod_src], as required by
    cancellation. *)
Section PrimeAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !llistGS, !memGS}.

  (** The abstract module that remains after all auxiliary specifications
      have been discharged. *)
  Local Definition smod_src : SMod.t := PrimeA.smod.

  Local Definition sp_prime : specmap := SMod.sp_from PrimeA.smod.
  Local Definition sp_list : specmap := SMod.sp_from LListA.smod.
  Local Definition sp_mem : specmap := SMod.sp_from MemA.smod.

  Local Definition mod_src : Mod.t :=
    SMod.to_mod sp_prime smod_src.

  Local Definition mod_top : Mod.t :=
    SMod.to_mod ∅ (SMod.cancel smod_src).

  Local Definition mod_tgt : Mod.t :=
    PrimeI.t ★ LListI.t ★ MemI.t [].

  Local Definition init_cond : iProp Σ :=
    (LListA.init_cond ∗ MemA.init_cond [])%I.

  (** The map derived from [LListA.smod] contains the public linked-list
      specifications used by both adjacent proof layers. *)
  Lemma llist_in_sp : LListA.sp ⊆ sp_list.
  Proof.
    split; et.
  Qed.

  (** Cancellation supplies the initial list fragment to [main_spec] and
      removes the specifications from [entry] and [get_prime]. *)
  Lemma cancel_src :
    (PrimeA.init_cond ∗ Cancel.init_res)%I ⊢
      refines mod_src mod_top.
  Proof.
    iIntros "[FRAG CANCEL]".
    rewrite /mod_src /mod_top /sp_prime /smod_src.
    iApply refines_trans. iSplitR "FRAG CANCEL".
    { iApply ctxr_refines. iApply Cancel.prepare; et; clarify. }
    iApply Cancel.cancel.
    { r; rewrite /=; mod_tac ss. }
    { assert (Ht : (SMod.sp_from smod_src).1 !! entry =
          fsp_some PrimeA.main_spec)
        by mod_tac.
      rewrite Ht; clear Ht.
      ss; exists tt; split; refl.
    }
    { unfoldPrePost. iIntros "% % H".
      iDestruct "H" as "(-> & _)". done. }
    iDestruct "CANCEL" as "(X & Y & Z & $ & $)".
    unfoldPrePost. rewrite /PrimeA.init_cond. iFrame. ss.
  Qed.

  (** Compose the implementation refinements in this order:

        MemI <= MemA
        LListI ★ MemA <= LListA
        PrimeI ★ LListA <= PrimeA.

      The source sides of [LListIA] and [PrimeIA] contain no auxiliary
      modules.  [PrimeIA] now needs no initial resource: the list fragment is
      reserved for entry cancellation, while [LListIA] consumes the
      authoritative half. *)
  Lemma src_tgt :
    (LListA.auth_init ∗ MemA.init_cond [])%I ⊢
      refines mod_tgt mod_src.
  Proof.
    iIntros "[AUTH MEM]".
    iPoseProof (MemIA.ctxr sp_mem [] with "MEM") as "MEMREF".
    iPoseProof (LListIA.ctxr sp_list sp_mem llist_in_sp with
      "AUTH") as "LISTREF".
    iPoseProof (PrimeIA.ctxr sp_list llist_in_sp) as "PRIMEREF".
    iApply ctxr_refines.
    rewrite /mod_tgt /mod_src /sp_prime /smod_src.
    iApply ctxr_trans. iSplitL "MEMREF".
    { iApply ctxr_frameL. iApply ctxr_frameL. iExact "MEMREF". }
    iApply ctxr_trans. iSplitL "LISTREF".
    { iApply ctxr_frameL. iExact "LISTREF". }
    iExact "PRIMEREF".
  Qed.

  Lemma top_tgt :
    (init_cond ∗ Cancel.init_res)%I ⊢ refines mod_tgt mod_top.
  Proof.
    rewrite /init_cond /LListA.init_cond.
    iIntros "[[[FRAG AUTH] MEM] CANCEL]".
    iPoseProof (cancel_src with "[$FRAG $CANCEL]") as "REF2".
    iPoseProof (src_tgt with "[$AUTH $MEM]") as "REF1".
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
End PrimeAux.

Module PrimeAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ; llistΓ; memΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  (** The final theorem compares the fully concrete linked implementation
      with the cancelled abstract prime program. *)
  Theorem behavioral_refinement :
    ∃ β τ
      (Hinv : invGS Γ Σ α)
      (_ : crisG Γ Σ α β τ _ Hinv)
      (_ : llistGS)
      (_ : memGS)
      src_res tgt_res,
      refines_lmod
        (Mod.to_lmod mod_tgt tgt_res)
        (Mod.to_lmod mod_top src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "[% [% [% [% CRIS]]]]".
    iMod llist_alloc as "[% LLIST]".
    iMod (mem_alloc []) as "[% MEM]".
    iExists _, _, _, _, _, _.
    iDestruct "CRIS" as "[WINV [TID [YIELD [TIDAUTH YIELDAUTH]]]]".
    iPoseProof (winv_split_empty with "WINV") as "[WINV WINV_EMPTY]".
    iEval (rewrite /mem_init own_op) in "MEM".
    iDestruct "MEM" as "[MEM _]".
    iPoseProof (top_tgt with
      "[LLIST MEM TID YIELD WINV TIDAUTH YIELDAUTH]") as "REF".
    { rewrite /init_cond /MemA.init_cond /mem_init_auth /Cancel.init_res.
      iFrame. }
    iPoseProof (refines_adequacy mod_tgt mod_top tgt_wf with
      "[$WINV_EMPTY $REF]") as "%ADEQ".
    destruct ADEQ as [src_res [_ REF]].
    iExists src_res, ε. done.
  Qed.
End PrimeAll.

(* Print Assumptions PrimeAll.behavioral_refinement. *)
