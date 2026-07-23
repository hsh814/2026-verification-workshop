(** * Proofs that LListI refines LListA *)

From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemA MemTactics.
From prime_answer Require Import LListA LListI.

(** Exercise 2: refine the resource-level specification by the linked-list
    implementation. *)
Module LListIA. Section LListIA.
  Context `{!crisG Γ Σ α β τ _S _I, !llistGS, !memGS}.

  (** Keep the maps for the source list specification and the target memory
      specification separate.  The same [sp_list] is later used by
      [PrimeIA], while [sp_mem] matches the source side of [MemIA]. *)
  Context (sp_list sp_mem : specmap).
  Context (LIST_IN_SP : LListA.sp ⊆ sp_list).

  Local Definition ListAMod := LListA.t sp_list.
  Local Definition ListIMod := LListI.t ★ MemA.t sp_mem.

  (** A concrete node consists of adjacent value and next-pointer cells. *)
  Fixpoint nodes (cursor : val) (values : list nat) : iProp Σ :=
    match values with
    | [] => ⌜cursor = Vnullptr⌝
    | value :: values' =>
        ∃ bo next,
          ⌜cursor = Vptr bo⌝ ∗
          bo |-> [Vint (Z.of_nat value); next] ∗
          nodes next values'
    end%I.

  (** The stable header cell contains the first node pointer. *)
  Definition represents
      (list_loc : val) (values : list nat) : iProp Σ :=
    (∃ bo head,
      ⌜list_loc = Vptr bo⌝ ∗
      bo ↦ head ∗
      nodes head values)%I.

  (** The list modules have no private state: all concrete list data lives in
      Imp memory.  [list_auth] connects that representation to the
      client-owned [list_user].  [MemA] appears only in the target module,
      where its calls are inlined during the simulation. *)
  Definition Ist : ist_type Σ :=
    (fun st_src st_tgt =>
      ⌜st_src = ∅ /\ st_tgt = ∅⌝ ∗
      ∃ state,
        LListA.list_auth state ∗
        match state with
        | None => emp
        | Some (list_loc, values) => represents list_loc values
        end)%I.

  (** Function simulations for the three public list operations. *)
  Lemma simF_new :
    ISim.sim_fun open ListAMod ListIMod Ist (fid LListHdr.new).
  Proof.
    cStartFunSim. rewrite /LListI.new. cStepsS. cStepsT.
    iDestruct "ASM" as "(-> & -> & USER)". cSimpl.
    iDestruct "IST" as "[%ST IST]".
    destruct ST as [-> ->].
    iDestruct "IST" as (state) "[AUTH REP]".
    iPoseProof (LListA.list_agree with "AUTH USER") as "->".
    cStepsT.
    mAllocT as (blk) "[P _]".
    mStoreT "P".
    iMod (LListA.list_update _q
      (Some (Vptr (blk, 0%Z), [])) with "AUTH USER")
      as "[AUTH USER]".
    cForceS ((Vptr (blk, 0%Z))↑). cStepsS.
    cForceS ((Vptr (blk, 0%Z))↑). cStepsS.
    cForceS.
    iFrame. cSimpl.
    iSplit; first done.
    cStep. iSplit; first done.
    rewrite /Ist. iSplit; first done.
    iExists (Some (Vptr (blk, 0%Z), [])). iFrame.
    iSplit; done.
    (* The client fragment agrees with the currently tracked authoritative
       state.  Allocation creates a replacement header, and [list_update]
       moves both halves to [Some (list_loc, [])]. *)
  Qed.

  Lemma simF_push_front :
    ISim.sim_fun open ListAMod ListIMod Ist (fid LListHdr.push_front).
  Proof.
    cStartFunSim. rewrite /LListI.push_front. cStepsS. cStepsT.
    destruct _q as [[list_loc old] value].
    iDestruct "ASM" as "(-> & -> & USER)". cSimpl.
    iDestruct "IST" as "[%ST IST]".
    destruct ST as [-> ->].
    iDestruct "IST" as (state) "[AUTH REP]".
    iPoseProof (LListA.list_agree with "AUTH USER") as "->".
    iDestruct "REP" as (bo head) "(-> & HEAD & NODES)".
    destruct bo as [b ofs].
    cStepsT. mLoadT "HEAD".
    mAllocT as (blk) "[VAL [NEXT _]]".
    rewrite /scale_int; case_match; ss. cStepsT.
    mStoreT "VAL". mStoreT "NEXT". mStoreT "HEAD".
    iMod (LListA.list_update
      (Some (Vptr (b, ofs), old))
      (Some (Vptr (b, ofs), value :: old)) with "AUTH USER")
      as "[AUTH USER]".
    cForceS (tt↑). cStepsS. cForceS (tt↑). cStepsS. cForceS.
    iFrame. cSimpl. iSplit; first done.
    cStep. iSplit; first done.
    rewrite /Ist. iSplit; first done.
    iExists (Some (Vptr (b, ofs), value :: old)). iFrame.
    iSplit; first done. iExists (blk, 0%Z). iSplit; first done.
    iFrame. done.
    (* Open [represents], use [mLoadT], allocate the two-cell node with
       [mAllocT], and perform its three stores with [mStoreT].  Then apply
       [list_update] while preserving the stable [list_loc]. *)
  Qed.

  Lemma simF_get :
    ISim.sim_fun open ListAMod ListIMod Ist (fid LListHdr.get).
  Proof.
    cStartFunSim. rewrite /LListI.get. cStepsS. cStepsT.
    destruct _q as [[list_loc values] index].
    iDestruct "ASM" as "(-> & -> & USER)". cSimpl.
    iDestruct "IST" as "[%ST IST]".
    destruct ST as [-> ->].
    iDestruct "IST" as (state) "[AUTH REP]".
    iPoseProof (LListA.list_agree with "AUTH USER") as "->".
    iDestruct "REP" as (bo head) "(-> & HEAD & NODES)".
    destruct bo as [b ofs].
    cStepsT. mLoadT "HEAD".
    iAssert (nodes head values -∗
      represents (Vptr (b, ofs)) values)%I
      with "[HEAD]" as "REBUILD".
    { iIntros "NODES". iExists (b, ofs), head. iFrame. done. }
    rename values into all_values.
    rename index into requested.
    set (remaining := requested) at 2.
    pose (cursor := head).
    iEval (fold cursor) in "NODES".
    iEval (fold cursor) in "REBUILD".
    fold cursor.
    iAssert (⌜all_values !! remaining = all_values !! requested⌝ ∗
      nodes cursor all_values)%I with "[NODES]" as "NODES".
    { iFrame. iPureIntro. subst remaining. done. }
    iRevert "NODES". iRevert "REBUILD". iStopProof.
    generalize all_values at 3 5 7 as suffix.
    clearbody cursor remaining.
    intro suffix.
    revert cursor remaining.
    induction suffix as [|value suffix IH];
      intros cursor remaining;
      iIntros "[AUTH USER] REBUILD [%LOOKUP NODES]".
    - iDestruct "NODES" as %CURSOR. subst cursor.
      iAssert (nodes Vnullptr [])%I as "NODES". { done. }
      iSpecialize ("REBUILD" with "NODES").
      rewrite unfold_iterC. cStepT. rewrite decide_True //. cStepsT.
      simpl in LOOKUP.
      cForceS ((None : option nat)↑). cStepsS.
      cForceS ((None : option nat)↑). cStepsS.
      cForceS.
      rewrite <- LOOKUP.
      iFrame. cSimpl.
      iSplit; first done.
      cStep. iSplit; first done.
      rewrite /Ist. iSplit; first done.
      iExists (Some (Vptr (b, ofs), all_values)). iFrame.
    - iDestruct "NODES" as (node next) "(-> & BLOCK & TAIL)".
      destruct node as [blk node_ofs].
      iDestruct "BLOCK" as "[VAL [NEXT _]]".
      assert (OFF0 : (node_ofs + 0%nat)%Z = node_ofs) by lia.
      iEval (rewrite OFF0) in "VAL".
      iAssert ((blk, node_ofs) ↦ Vint value)%I
        with "[VAL]" as "VAL0".
      { iExact "VAL". }
      rewrite unfold_iterC. cStepT.
      rewrite decide_False; last done. cStepsT.
      mLoadT "VAL0". cStepsT.
      iAssert ((blk, (node_ofs + 0%nat)%Z) ↦ Vint value)%I
        with "[VAL0]" as "VAL".
      { iEval (rewrite OFF0). iExact "VAL0". }
      destruct remaining as [|remaining].
      + simpl in LOOKUP.
        cStepsT.
        iAssert (nodes (Vptr (blk, node_ofs)) (value :: suffix))%I
          with "[VAL NEXT TAIL]" as "NODES".
        { iExists (blk, node_ofs), next. iSplit; first done.
          iFrame. done. }
        iSpecialize ("REBUILD" with "NODES").
        cForceS ((Some value : option nat)↑). cStepsS.
        cForceS ((Some value : option nat)↑). cStepsS.
        cForceS.
        rewrite <- LOOKUP.
        iFrame. cSimpl. iSplit; first done.
        cStep. rewrite /ist_with_eq.
        iSplit; first (iPureIntro; rewrite Nat2Z.id; done).
        rewrite /Ist. iSplit; first done.
        iExists (Some (Vptr (b, ofs), all_values)). iFrame.
      + simpl in LOOKUP.
        rewrite /scale_int.
        destruct (Zdivide_dec 8 8) as [DIV | NDIV].
        2: { exfalso. apply NDIV. exists 1%Z. lia. }
        cStepsT.
        mLoadT "NEXT". cStepsT.
        iAssert (nodes next suffix -∗
          represents (Vptr (b, ofs)) all_values)%I
          with "[REBUILD VAL NEXT]" as "REBUILD'".
        { iIntros "TAIL". iApply "REBUILD".
          iExists (blk, node_ofs), next. iSplit; first done.
          iFrame. done. }
        iPoseProof (IH next remaining with "[$AUTH $USER]") as "IH".
        iSpecialize ("IH" with "REBUILD'").
        iApply "IH". iFrame. done.
    (* Preserve [is_list list_loc values], load the header with [mLoadT], and
       induct over [nodes] and the requested index.  Each [iterC] step loads a
       value and next pointer; reaching [Vnullptr] returns [None]. *)
  Qed.

  (** The module-level simulation theorem is intentionally already stated. *)
  Lemma sim :
    ISim.t open ListAMod ListIMod LListA.auth_init Ist.
  Proof.
    cStartModSim.
    - vm_compute. apply submseteq_skip, submseteq_cons, submseteq_nil.
    - iIntros "AUTH". rewrite /Ist. iSplit; first done.
      iExists None. iFrame.
    - apply simF_new.
    - apply simF_push_front.
    - apply simF_get.
  Qed.
End LListIA.

(** Contextual refinement is the public result of Exercises 1 and 2.
    Direction reminder: the implementation on the left refines the abstract
    resource specification on the right. *)
Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !llistGS, !memGS}.

  Lemma ctxr
      (sp_list sp_mem : specmap)
      (LIST_IN_SP : LListA.sp ⊆ sp_list) :
    LListA.auth_init ⊢ ctx_refines
      (LListI.t ★ MemA.t sp_mem)
      (LListA.t sp_list).
  Proof.
    eapply main_adequacy, sim; eauto.
  Qed.
End contextual_refinement. End LListIA.
