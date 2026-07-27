(** * Exercise 1: prove the linked-list safety specification *)

From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemA.
From CRIS.imp_system.safe_mem Require Import MemNB.
From prime_safe_answer Require Import LListA LListI.

(** [LListA] and [LListI] have exactly the same linked-list bodies.
    [LListA] additionally attaches specifications to those bodies.  The
    memory module is kept on both sides of this refinement: its
    specifications provide the points-to rules used while checking the list
    bodies, and its concrete body is preserved for the final cancellation. *)
Module LListIA. Section LListIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Context (sp : specmap).
  Context (LIST_IN_SP : LListA.sp ⊆ sp).
  Context (MEM_IN_SP : MemNB.sp ⊆ sp).

  Local Definition ListAMod : Mod.t :=
    LListA.t sp ★ MemNB.t sp [].

  Local Definition ListIMod : Mod.t :=
    LListI.t ★ MemNB.t sp [].

  (** The list layer needs no private logical state.  [IstProd] separates its
      scopes from the shared [MemNB] suffix, whose state is related by
      [IstEq].  This lets the module simulation frame the common suffix
      automatically. *)
  Definition IstLocal : ist_type Σ := IstTrue.

  Definition Ist : ist_type Σ :=
    IstProd (IstSB (LListA.t sp).(Mod.scopes) IstLocal) IstEq.

  Lemma simF_new :
    ISim.sim_fun open ListAMod ListIMod Ist (fid LListHdr.new).
  Proof.
    cStartFunSim. rewrite /LListA.new /LListI.new. cStepsS. cStepsT.
    iDestruct "ASM" as "[-> ->]". cSimpl.
    cStepS. cStepsS. cStepT.
    rewrite /SModTr.HoareCall. cStepsS.
    erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
    cForceS 1%nat. cForceS ([Vint 1]↑). cForcesS.
    iSplit; first done. cStepsS.
    cCall "IST" as (ret st_src' st_tgt') "IST".
    cStepsS.
    iDestruct "ASM" as "(-> & %blk & -> & P & _)". cSimpl.
    cStepsS. cStepsT. rewrite /SModTr.HoareCall. cStepsS.
    erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
    cForceS (blk, 0%Z, Vundef, Vnullptr).
    cForceS ([Vptr (blk, 0%Z); Vnullptr]↑). cForcesS.
    iFrame "P". iSplit; first done. cStepsS.
    cCall "IST" as (ret st_src'' st_tgt'') "IST".
    cStepsS.
    iDestruct "ASM" as "(-> & P & ->)". cSimpl.
    cStepsS. cStepsT.
    cForceS ((Vptr (blk, 0%Z))↑). cStepsS.
    cForceS. cSimpl.
    iSplitL "P".
    { iSplitL ""; first done.
      iExists (Vptr (blk, 0%Z)). iSplitL ""; first done.
      iExists (blk, 0%Z), Vnullptr. iFrame. done. }
    cStep. iSplit; first done. iFrame.
  Qed.

  Lemma simF_push_front :
    ISim.sim_fun open ListAMod ListIMod Ist
      (fid LListHdr.push_front).
  Proof.
    cStartFunSim.
    rewrite /LListA.push_front /LListI.push_front.
    cStepsS. cStepsT.
    destruct _q as [[list_loc old] value].
    iDestruct "ASM" as "(-> & -> & LIST)". cSimpl.
    iDestruct "LIST" as (bo head) "(-> & HEAD & NODES)".
    destruct bo as [blk ofs].
    cStepS. cStepsS. cStepT.
    rewrite /SModTr.HoareCall. cStepsS.
    erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
    cForceS (blk, ofs, 1%Qp, head).
    cForceS ([Vptr (blk, ofs)]↑). cForcesS.
    iFrame "HEAD". iSplit; first done. cStepsS.
    cCall "IST" as (ret st_src' st_tgt') "IST".
    cStepsS.
    iDestruct "ASM" as "(-> & HEAD & ->)". cSimpl.
    cStepsS. cStepsT. rewrite /SModTr.HoareCall. cStepsS.
    erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
    cForceS 2%nat. cForceS ([Vint 2]↑). cForcesS.
    iSplit; first done. cStepsS.
    cCall "IST" as (ret st_src'' st_tgt'') "IST".
    cStepsS.
    iDestruct "ASM" as "(-> & %node & -> & VAL & NEXT & _)". cSimpl.
    cStepsS. cStepsT. rewrite /scale_int.
    case_match; ss.
    cStepsS. cStepsT. rewrite /SModTr.HoareCall. cStepsS.
    erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
    cForceS (node, 0%Z, Vundef, Vint (Z.of_nat value)).
    cForceS ([Vptr (node, 0%Z); Vint (Z.of_nat value)]↑).
    cForcesS. iFrame "VAL". iSplit; first done. cStepsS.
    cCall "IST" as (ret st_src''' st_tgt''') "IST".
    cStepsS. iDestruct "ASM" as "(-> & VAL & ->)". cSimpl.
    assert (OFF1 : (0 + 8 `div` 8)%Z = 1%Z) by reflexivity.
    rewrite OFF1.
    cStepsS. cStepsT. rewrite /SModTr.HoareCall. cStepsS.
    erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
    cForceS (node, 1%Z, Vundef, head).
    cForceS ([Vptr (node, 1%Z); head]↑). cForcesS.
    iFrame "NEXT". iSplit; first done. cStepsS.
    cCall "IST" as (ret st_src4 st_tgt4) "IST".
    cStepsS. iDestruct "ASM" as "(-> & NEXT & ->)". cSimpl.
    cStepsS. cStepsT. rewrite /SModTr.HoareCall. cStepsS.
    erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
    cForceS (blk, ofs, head, Vptr (node, 0%Z)).
    cForceS ([Vptr (blk, ofs); Vptr (node, 0%Z)]↑). cForcesS.
    iFrame "HEAD". iSplit; first done. cStepsS.
    cCall "IST" as (ret st_src5 st_tgt5) "IST".
    cStepsS. iDestruct "ASM" as "(-> & HEAD & ->)". cSimpl.
    cStepsS. cStepsT. cForceS (tt↑). cStepsS. cForceS. cSimpl.
    iSplitL "HEAD VAL NEXT NODES".
    { iSplitL "". { done. }
      iSplitL "". { done. }
      iExists (blk, ofs), (Vptr (node, 0%Z)).
      iSplitL "". { done. } iFrame "HEAD".
      iExists (node, 0%Z), head. iSplitL "". { done. }
      iFrame. done. }
    cStep. iSplit; first done. iFrame.
  Qed.

  Lemma simF_get :
    ISim.sim_fun open ListAMod ListIMod Ist (fid LListHdr.get).
  Proof.
    cStartFunSim. rewrite /LListA.get /LListI.get.
    cStepsS. cStepsT.
    destruct _q as [[list_loc values] index].
    iDestruct "ASM" as "(-> & -> & LIST)". cSimpl.
    iDestruct "LIST" as (bo head) "(-> & HEAD & NODES)".
    destruct bo as [blk ofs].
    cStepS. cStepsS. cStepT.
    rewrite /SModTr.HoareCall. cStepsS.
    erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
    cForceS (blk, ofs, 1%Qp, head).
    cForceS ([Vptr (blk, ofs)]↑). cForcesS.
    iFrame "HEAD". iSplit; first done. cStepsS.
    cCall "IST" as (ret st_src' st_tgt') "IST".
    cStepsS. iDestruct "ASM" as "(-> & HEAD & ->)". cSimpl.
    cStepsS. cStepsT.
    iAssert (LListA.nodes head values -∗
      LListA.is_list (Vptr (blk, ofs)) values)%I
      with "[HEAD]" as "REBUILD".
    { iIntros "NODES". iExists (blk, ofs), head. iFrame. done. }
    rename values into all_values.
    rename index into requested.
    set (remaining := requested) at 1 3.
    pose (cursor := head).
    iEval (fold cursor) in "NODES".
    iEval (fold cursor) in "REBUILD".
    fold cursor.
    iAssert (⌜all_values !! remaining = all_values !! requested⌝ ∗
      LListA.nodes cursor all_values)%I with "[NODES]" as "NODES".
    { iFrame. iPureIntro. subst remaining. done. }
    iRevert "NODES". iRevert "REBUILD". iRevert "IST".
    iStopProof.
    generalize all_values at 1 3 5 as suffix.
    clearbody cursor remaining.
    intro suffix.
    revert cursor remaining st_src' st_tgt'.
    induction suffix as [|value suffix IH];
      intros cursor remaining st_src' st_tgt';
      iIntros "_ IST REBUILD [%LOOKUP NODES]".
    - iDestruct "NODES" as %CURSOR. subst cursor.
      iAssert (LListA.nodes Vnullptr [])%I as "NODES". { done. }
      iSpecialize ("REBUILD" with "NODES").
      cStepsS. cStepsT. rewrite !unfold_iterC. cStepsS. cStepsT.
      rewrite !decide_True //. cStepsS. cStepsT.
      cForceS ((None : option nat)↑). cStepsS.
      cForceS. rewrite <- LOOKUP. cSimpl.
      iSplitL "REBUILD".
      { iSplitL "". { done. }
        iSplitL "". { done. }
        iFrame. }
      cStep. iSplit; first done. iFrame.
    - iDestruct "NODES" as (node next) "(-> & BLOCK & TAIL)".
      destruct node as [node_blk node_ofs].
      iDestruct "BLOCK" as "[VAL [NEXT _]]".
      assert (OFF0 : (node_ofs + 0%nat)%Z = node_ofs) by lia.
      iEval (rewrite OFF0) in "VAL".
      iAssert ((node_blk, node_ofs) ↦ Vint value)%I
        with "[VAL]" as "VAL0".
      { iExact "VAL". }
      cStepsS. cStepsT. rewrite !unfold_iterC. cStepS. cStepT.
      rewrite !decide_False; try done. cStepsS. cStepsT.
      rewrite /SModTr.HoareCall. cStepsS.
      erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
      cForceS (node_blk, node_ofs, 1%Qp, Vint value).
      cForceS ([Vptr (node_blk, node_ofs)]↑). cForcesS.
      iFrame "VAL0". iSplit; first done. cStepsS.
      cCall "IST" as (ret st_src'' st_tgt'') "IST".
      cStepsS. iDestruct "ASM" as "(-> & VAL0 & ->)". cSimpl.
      cStepsS. cStepsT.
      iAssert ((node_blk, (node_ofs + 0%nat)%Z) ↦ Vint value)%I
        with "[VAL0]" as "VAL".
      { iEval (rewrite OFF0). iExact "VAL0". }
      destruct remaining as [|remaining].
      + simpl in LOOKUP. cStepsS. cStepsT.
        iAssert
          (LListA.nodes (Vptr (node_blk, node_ofs))
            (value :: suffix))%I
          with "[VAL NEXT TAIL]" as "NODES".
        { iExists (node_blk, node_ofs), next.
          iSplitL ""; first done. iFrame. done. }
        iSpecialize ("REBUILD" with "NODES").
        cForceS ((Some value : option nat)↑). cStepsS.
        cForceS. rewrite <- LOOKUP. cSimpl.
        iSplitL "REBUILD".
        { iSplitL "".
          { iPureIntro. rewrite Nat2Z.id. done. }
          iSplitL "".
          { iPureIntro. rewrite Nat2Z.id. done. }
          iFrame. }
        cStep. rewrite /ist_with_eq. iSplit.
        { iPureIntro. rewrite Nat2Z.id. done. }
        iFrame.
      + simpl in LOOKUP. cStepsS. cStepsT. rewrite /scale_int.
        case_match; ss.
        cStepsS. cStepsT. rewrite /SModTr.HoareCall. cStepsS.
        erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
        cForceS
          (node_blk, (node_ofs + 1)%Z, 1%Qp, next).
        cForceS
          ([Vptr (node_blk, (node_ofs + 1)%Z)]↑).
        cForcesS. iFrame "NEXT". iSplit; first done. cStepsS.
        cCall "IST" as (ret st_src''' st_tgt''') "IST".
        cStepsS. iDestruct "ASM" as "(-> & NEXT & ->)". cSimpl.
        cStepsS. cStepsT.
        iAssert (LListA.nodes next suffix -∗
          LListA.is_list (Vptr (blk, ofs)) all_values)%I
          with "[REBUILD VAL NEXT]" as "REBUILD'".
        { iIntros "TAIL". iApply "REBUILD".
          iExists (node_blk, node_ofs), next.
          iSplitL ""; first done. iFrame. done. }
        iPoseProof
          (IH next remaining st_src''' st_tgt''' with "[]") as "IH".
        { done. }
        iSpecialize ("IH" with "IST").
        iSpecialize ("IH" with "REBUILD'").
        iApply "IH". iFrame. done.
  Qed.

  Lemma sim :
    ISim.t open ListAMod ListIMod emp%I Ist.
  Proof.
    cStartModSim.
    - apply simF_new.
    - apply simF_push_front.
    - apply simF_get.
    - iIntros "_". unfold Ist, IstProd, IstLocal.
      do 4 iExists _. ss.
  Qed.
End LListIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Lemma ctxr
      (sp : specmap)
      (LIST_IN_SP : LListA.sp ⊆ sp)
      (MEM_IN_SP : MemNB.sp ⊆ sp) :
    emp%I ⊢ ctx_refines
      (LListI.t ★ MemNB.t sp [])
      (LListA.t sp ★ MemNB.t sp []).
  Proof.
    eapply main_adequacy, sim; eauto.
  Qed.
End contextual_refinement. End LListIA.
