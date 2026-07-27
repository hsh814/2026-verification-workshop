(** * Proof that [StackI] Refines [StackA] Using [MemA] *)

From CRIS.common Require Import CRIS.
From mem_answer Require Import MemA.
From stack_answer Require Import StackA StackI.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Context (sp_stack sp_mem : specmap).
  Context (STACK_IN_SP : StackA.sp ⊆ sp_stack).

  Local Definition StackAMod := StackA.t sp_stack.
  Local Definition StackIMod := StackI.t ★ MemA.t sp_mem.

  (** Both stack modules have empty private state.  All concrete data is
      represented by client-visible memory resources. *)
  Definition Ist : ist_type Σ := λ _ _, True%I.

  Lemma simF_new_stack :
    ISim.sim_fun open StackAMod StackIMod Ist
      (fid StackHdr.new_stack).
  Proof.
    cStartFunSim.
    rewrite /StackI.new_stack.
    cStepsT. cStepsS.
    iDestruct "ASM" as "[-> ->]".
    cStepsT. cInlineT. cStepsT.
    cForceT tt. cForceT (tt↑). cForceT.
    iSplitR; first done.
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as (l) "[-> CELL]".
    cSimpl. cStepsT. cInlineT. cStepsT.
    cForceT (l, Vundef, Vloc None).
    cForceT ((l, Vloc None)↑). cForceT.
    iSplitL "CELL"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl. cStepsT.
    cForceS (l↑). cStepsS. cForcesS.
    iSplitL "HEADER".
    { iSplitR "HEADER"; first done.
      iExists l. iSplitR "HEADER"; first done.
      rewrite /is_stack. iExists None. iFrame. done. }
    cStep.
    rewrite /ist_with_eq /Ist. iFrame. done.
  Qed.

  Lemma simF_push :
    ISim.sim_fun open StackAMod StackIMod Ist
      (fid StackHdr.push).
  Proof.
    cStartFunSim.
    rewrite /StackI.push.
    cStepsT. cStepsS.
    cStepsT. cStepsS.
    destruct _q as [[l values] value].
    iDestruct "ASM" as "[-> [-> STACK]]".
    iDestruct "STACK" as (head) "[HEADER LIST]".
    cStepsT. cInlineT. cStepsT.
    cForceT tt. cForceT (tt↑). cForceT.
    iSplitR; first done.
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as (node) "[-> NODE]".
    cSimpl. cStepsT. cInlineT. cStepsT.
    cForceT (l, Vloc head).
    cForceT (l↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl. cStepsT. cInlineT. cStepsT.
    cForceT (node, Vundef, Vpair (Vnat value) (Vloc head)).
    cForceT ((node, Vpair (Vnat value) (Vloc head))↑).
    cForceT.
    iSplitL "NODE"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> NODE]".
    cSimpl. cStepsT. cInlineT. cStepsT.
    cForceT (l, Vloc head, Vloc (Some node)).
    cForceT ((l, Vloc (Some node))↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl. cStepsT.
    cForceS (tt↑). cStepsS. cForcesS.
    iSplitL "HEADER NODE LIST".
    { iSplitR "HEADER NODE LIST"; first done.
      iSplitR "HEADER NODE LIST"; first done.
      rewrite /is_stack. iExists (Some node).
      iSplitL "HEADER"; first done.
      simpl. iExists node, head. iFrame. done. }
    cStep.
    rewrite /ist_with_eq /Ist. iFrame. done.
  Qed.

  Lemma simF_pop :
    ISim.sim_fun open StackAMod StackIMod Ist
      (fid StackHdr.pop).
  Proof.
    cStartFunSim.
    rewrite /StackI.pop.
    cStepsT. cStepsS.
    cStepsT. cStepsS.
    destruct _q as [l values].
    iDestruct "ASM" as "[-> [-> STACK]]".
    iDestruct "STACK" as (head) "[HEADER LIST]".
    cStepsT. cInlineT. cStepsT.
    cForceT (l, Vloc head).
    cForceT (l↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl.
    destruct values as [|value values].
    - iDestruct "LIST" as %->.
      cStepsT.
      cForceS ((None : option nat)↑). cStepsS. cForcesS.
      iSplitL "HEADER".
      { iSplitR "HEADER"; first done.
        iSplitR "HEADER"; first done.
        rewrite /is_stack. iExists None. iFrame. done. }
      cStep.
      rewrite /ist_with_eq /Ist. iFrame. done.
    - iDestruct "LIST" as (node next) "(%HEAD & NODE & LIST)".
      subst head.
      cStepsT. cInlineT. cStepsT.
      cForceT (node, Vpair (Vnat value) (Vloc next)).
      cForceT (node↑). cForceT.
      iSplitL "NODE"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> NODE]".
      cSimpl. cStepsT. cInlineT. cStepsT.
      cForceT (l, Vloc (Some node), Vloc next).
      cForceT ((l, Vloc next)↑). cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. cStepsT.
      cForceS ((Some value : option nat)↑). cStepsS. cForcesS.
      iSplitL "HEADER LIST".
      { iSplitR "HEADER LIST"; first done.
        iSplitR "HEADER LIST"; first done.
        rewrite /is_stack. iExists next. iFrame. }
      cStep.
      rewrite /ist_with_eq /Ist. iFrame. done.
  Qed.

  Lemma sim :
    ISim.t open StackAMod StackIMod emp Ist.
  Proof.
    cStartModSim.
    - vm_compute. apply submseteq_cons, submseteq_skip, submseteq_nil.
    - iIntros "_". done.
    - apply simF_new_stack.
    - apply simF_push.
    - apply simF_pop.
  Qed.
End StackIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Lemma ctxr
      (sp_stack sp_mem : specmap)
      (STACK_IN_SP : StackA.sp ⊆ sp_stack) :
    emp ⊢ ctx_refines
      (StackI.t ★ MemA.t sp_mem)
      (StackA.t sp_stack).
  Proof.
    eapply main_adequacy, sim; eauto.
  Qed.
End contextual_refinement. End StackIA.
