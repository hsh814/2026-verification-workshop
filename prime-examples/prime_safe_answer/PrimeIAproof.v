(** * Exercise 2: prove that the prime client is memory safe *)

From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemA.
From CRIS.imp_system.safe_mem Require Import MemNB.
From prime_safe_answer Require Import
  LListA PrimeA PrimeI.

(** [PrimeA] and [PrimeI] also have identical bodies.  The proof uses the
    supplied [LListA] specifications to show that every list access is safe
    and that the [None] branch leading to [triggerUB] is unreachable. *)
Module PrimeIA. Section PrimeIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Context (sp : specmap).
  Context (PRIME_IN_SP : PrimeA.sp ⊆ sp).
  Context (LIST_IN_SP : LListA.sp ⊆ sp).
  Context (MEM_IN_SP : MemNB.sp ⊆ sp).

  Local Definition AuxMod : Mod.t :=
    LListA.t sp ★ MemNB.t sp [].

  Local Definition PrimeAMod : Mod.t :=
    PrimeA.t sp ★ AuxMod.

  Local Definition PrimeIMod : Mod.t :=
    PrimeI.t ★ AuxMod.

  (** The proof state is owned by [LListA.is_list].  [IstProd] separates the
      prime layer from the common list-and-memory suffix. *)
  Definition IstLocal : ist_type Σ := IstTrue.

  Definition Ist : ist_type Σ :=
    IstProd (IstSB (PrimeA.t sp).(Mod.scopes) IstLocal) IstEq.

  Lemma simF_get_prime :
    ISim.sim_fun open PrimeAMod PrimeIMod Ist
      (fid PrimeHdr.get_prime).
  Proof.
    cStartFunSim.
    rewrite /PrimeA.get_prime /PrimeI.get_prime.
    destruct Any.downcast eqn:DOWNCAST.
    - cStepsS. cStepsT. iDestruct "ASM" as "[-> ->]". cSimpl.
      cStepsS. cStep.
      cStepsS. cStepsT.
      rewrite /SModTr.HoareCall. cStepsS.
      erewrite lookup_weaken; try eapply LIST_IN_SP; eauto.
      cForceS tt. cForceS (tt↑). cForcesS.
      iSplit; first done. cStepsS.
      cCall "IST" as (new_ret st_src' st_tgt') "IST".
      cStepsS.
      iDestruct "ASM" as "(-> & %list_loc & -> & LIST)". cSimpl.
      cStepsS. cStepsT.
      set (candidate := 2%nat).
      set (found := 0%nat).
      set (values := ([] : list nat)).
      iEval (fold values) in "LIST".
      iAssert (⌜length values = found⌝ ∗
        LListA.is_list list_loc values)%I
        with "[LIST]" as "LIST".
      { iFrame. done. }
      clearbody candidate found values.
      iApply wsim_reset.
      cCoind CIH g __ with st_src' st_tgt' candidate found values.
      iIntros "[IST [%LEN LIST]]".
      rewrite !unfold_iterC.
      cStepsS. cStepsT. rewrite /PrimeA.has_divisor.
      set (index := 0%nat) at 2 6.
      assert (INDEX : index <= found) by (subst index; lia).
      clearbody index.
      remember (found - index) as remaining eqn:REMAINING.
      iRevert "LIST". iRevert "IST". iStopProof.
      revert index INDEX REMAINING st_src' st_tgt'.
      induction remaining as [|remaining IH];
        intros index INDEX REMAINING st_src' st_tgt';
        iIntros "_ IST LIST".
      + assert (index = found) as INDEX_EQ by lia.
        rewrite INDEX_EQ.
        rewrite !unfold_iterC.
        destruct (Nat.eq_dec found found); last lia.
        cStepsS. cStepsT.
        rewrite /SModTr.HoareCall. cStepsS.
        erewrite lookup_weaken; try eapply LIST_IN_SP; eauto.
        cForceS (list_loc, values, candidate).
        cForceS ((list_loc, candidate)↑). cForcesS.
        iFrame "LIST". iSplit; first done. cStepsS.
        cCall "IST" as (push_ret st_src'' st_tgt'') "IST".
        cStepsS.
        iDestruct "ASM" as "(-> & -> & LIST)". cSimpl.
        cStepsS. cStepsT.
        destruct (Nat.eq_dec (length values) ret)
          as [FOUND | NOT_FOUND].
        * cStepsS. cStepsT.
          cForceS (candidate↑). cStepsS. cForceS. cSimpl.
          iSplitL "".
          { iSplitL ""; first done.
            iExists candidate. done. }
          cStep. iSplit; first done. iFrame.
        * cStepsS. cStepsT.
          cByCoind CIH; eauto.
          iFrame. iPureIntro. simpl. lia.
      + assert (INDEX_LT : index < found) by lia.
        destruct (lookup_lt_is_Some_2 values index)
          as [divisor LOOKUP].
        { rewrite LEN. exact INDEX_LT. }
        rewrite !unfold_iterC.
        destruct (Nat.eq_dec index found); first lia.
        cStepsS. cStepsT.
        rewrite /SModTr.HoareCall. cStepsS.
        erewrite lookup_weaken; try eapply LIST_IN_SP; eauto.
        cForceS (list_loc, values, index).
        cForceS ((list_loc, index)↑). cForcesS.
        iFrame "LIST". iSplit; first done. cStepsS.
        cCall "IST" as (get_ret st_src'' st_tgt'') "IST".
        cStepsS.
        iDestruct "ASM" as "(-> & -> & LIST)".
        rewrite LOOKUP. cSimpl. cStepsS. cStepsT.
        destruct (Nat.eqb (candidate mod divisor) 0) eqn:DIVIDES.
        * cStepsS. cStepsT.
          cByCoind CIH; eauto.
          iFrame. done.
        * cStepsS. cStepsT.
          iPoseProof
            (IH (S index) ltac:(lia) ltac:(lia)
              st_src'' st_tgt'' with "[]") as "IH".
          { done. }
          iSpecialize ("IH" with "IST").
          iSpecialize ("IH" with "LIST").
          iApply "IH".
    - cStepsS. iDestruct "ASM" as "[-> ->]". cSimpl.
  Qed.

  Lemma sim :
    ISim.t open PrimeAMod PrimeIMod emp%I Ist.
  Proof.
    cStartModSim.
    - apply simF_get_prime.
    - iIntros "_". unfold Ist, IstProd, IstLocal.
      do 4 iExists _. ss.
  Qed.
End PrimeIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Lemma ctxr
      (sp : specmap)
      (PRIME_IN_SP : PrimeA.sp ⊆ sp)
      (LIST_IN_SP : LListA.sp ⊆ sp)
      (MEM_IN_SP : MemNB.sp ⊆ sp) :
    emp%I ⊢ ctx_refines
      (PrimeI.t ★ LListA.t sp ★ MemNB.t sp [])
      (PrimeA.t sp ★ LListA.t sp ★ MemNB.t sp []).
  Proof.
    eapply main_adequacy, sim; eauto.
  Qed.
End contextual_refinement. End PrimeIA.
