(** * Proof that [RefCellI] Refines [RefCellA] Using Fractional Memory *)

From Stdlib Require Import QArith.Qcanon.
From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From stdpp Require Import numbers.
From refcell.frac_mem_answer Require Import FracMemA.
From refcell.refcell_answer Require Import RefCellA RefCellI.

(** The empty sum must be representable, so ticket fractions are summed in
    [Qc] rather than [Qp]. *)
Definition borrow_total (bs : gmap nat Qp) : Qcanon.Qc :=
  map_fold
    (fun _ q (total : Qcanon.Qc) =>
      (Qp_to_Qc q + total)%Qc)
    0%Qc bs.

Lemma borrow_total_empty :
  borrow_total (∅ : gmap nat Qp) = 0%Qc.
Proof. reflexivity. Qed.

Lemma borrow_total_insert bs id q :
  bs !! id = None ->
  borrow_total (<[id := q]> bs) =
    (Qp_to_Qc q + borrow_total bs)%Qc.
Proof.
  intros FRESH. rewrite /borrow_total.
  rewrite map_fold_insert_L; last done.
  - done.
  - intros. ring.
Qed.

Lemma borrow_total_delete bs id q :
  bs !! id = Some q ->
  borrow_total bs =
    (Qp_to_Qc q + borrow_total (delete id bs))%Qc.
Proof.
  intros HIT. rewrite /borrow_total.
  rewrite (map_fold_delete_L
    (fun _ q (total : Qcanon.Qc) =>
      (Qp_to_Qc q + total)%Qc)
    0%Qc id q bs); last done.
  - done.
  - intros. ring.
Qed.

Lemma borrow_total_insert_half bs id q :
  bs !! id = None ->
  (borrow_total bs + Qp_to_Qc q = 1)%Qc ->
  (borrow_total (<[id := (q / 2)%Qp]> bs) +
    Qp_to_Qc (q / 2)%Qp = 1)%Qc.
Proof.
  intros FRESH CONS.
  pose proof (f_equal Qp_to_Qc (Qp.div_2 q)) as HALF.
  rewrite Qp.to_Qc_inj_add in HALF.
  rewrite borrow_total_insert; last done.
  rewrite <-CONS, <-HALF. ring.
Qed.

Lemma borrow_total_delete_merge bs id q q0 :
  bs !! id = Some q ->
  (borrow_total bs + Qp_to_Qc q0 = 1)%Qc ->
  (borrow_total (delete id bs) +
    Qp_to_Qc (q + q0) = 1)%Qc.
Proof.
  intros HIT CONS.
  rewrite Qp.to_Qc_inj_add.
  rewrite <-CONS.
  rewrite (borrow_total_delete bs id q); last done.
  ring.
Qed.

Lemma qp_half_lt_one (q : Qp) :
  (q ≤ 1)%Qp -> (q / 2 < 1)%Qp.
Proof.
  intros LE. eapply Qp.lt_le_trans; last exact LE.
  apply Qp.div_lt. vm_compute. done.
Qed.

Lemma map_size_delete_hit (bs : gmap nat Qp) id q :
  bs !! id = Some q ->
  size bs = S (size (delete id bs)).
Proof.
  intros HIT.
  have NONEMPTY : size bs <> 0.
  { eapply map_size_ne_0_lookup_2. eexists. exact HIT. }
  rewrite map_size_delete_Some; last (eexists; exact HIT).
  destruct (size bs); [done|lia].
Qed.

Module RefCellIA. Section RefCellIA.
  Context `{!crisG Γ Σ α β τ _S _I,
    !frac_memGS, !refcellGS}.
  Local Existing Instances
    frac_memGS_pre frac_mem_mapG frac_mem_countG
    refcellGS_pre refcell_registryG refcell_borrowG.

  Context (sp_refcell sp_mem : specmap).
  Context (REFCELL_IN_SP : RefCellA.sp ⊆ sp_refcell).

  Local Definition RefCellAMod := RefCellA.t sp_refcell.
  Local Definition RefCellIMod := RefCellI.t ★ FracMemA.t sp_mem.

  (** In shared mode, every active borrow has one full ghost-map ticket.
      The physical counter is exactly the number of tickets, and their
      fractions together with the residual fraction sum to one. *)
  Definition shared_rep
      (r l : loc) (γb : gname) (bs : gmap nat Qp) : iProp Σ :=
    (∃ q0 v,
      r ↦ shared_header l (size bs) ∗
      ghost_map_auth γb 1 bs ∗
      l ↦{q0} v ∗
      ⌜(borrow_total bs + Qp_to_Qc q0 = 1)%Qc ∧
        map_Forall (fun _ q => (q < 1)%Qp) bs⌝)%I.

  (** Mutable mode has exactly one ticket, carrying fraction one.  There is
      no residual points-to assertion: the successful caller owns it. *)
  Definition mutable_rep
      (r l : loc) (γb : gname) : iProp Σ :=
    (∃ id : nat,
      r ↦ mutable_header l ∗
      ghost_map_auth γb 1 ({[id := 1%Qp]} : gmap nat Qp))%I.

  Definition cell_rep (r : loc) (info : refcell_info) : iProp Σ :=
    let '(l, γb) := info in
    ((∃ bs : gmap nat Qp, shared_rep r l γb bs) ∨
      mutable_rep r l γb)%I.

  Definition Ist : ist_type Σ :=
    (fun _ _ =>
      ∃ registry : gmap loc refcell_info,
        ghost_map_auth refcell_registry_name 1 registry ∗
        [∗ map] r ↦ info ∈ registry, cell_rep r info)%I.

  Lemma pointsto_valid l q v :
    l ↦{q} v -∗ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    rewrite /pointsto. iIntros "CELL".
    iDestruct (ghost_map_elem_valid with "CELL") as %VALID.
    rewrite dfrac_valid_own in VALID. done.
  Qed.

  Lemma cell_rep_header r info :
    cell_rep r info -∗ ∃ value, r ↦ value.
  Proof.
    destruct info as [l γb].
    rewrite /cell_rep /shared_rep /mutable_rep.
    iIntros "[SHARED | MUTABLE]".
    - iDestruct "SHARED" as (bs q0 v) "(HEADER & _)".
      iExists (shared_header l _). iExact "HEADER".
    - iDestruct "MUTABLE" as (id) "(HEADER & _)".
      iExists (mutable_header l). iExact "HEADER".
  Qed.

  Lemma simF_new_refcell :
    ISim.sim_fun open RefCellAMod RefCellIMod Ist
      (fid RefCellHdr.new_refcell).
  Proof.
    cStartFunSim.
    rewrite /RefCellI.new_refcell.
    cStepsT. cStepsS.
    iDestruct "ASM" as "[-> ->]".
    iDestruct "IST" as (registry) "[REG REPS]".

    cStepsT. cInlineT. cStepsT.
    cForceT tt. cForceT (tt↑). cForceT.
    iSplitR; first done.
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as (l) "[-> CELL]".
    cSimpl.

    cStepsT. cInlineT. cStepsT.
    cForceT (l, Vundef, _q).
    cForceT ((l, _q)↑). cForceT.
    iSplitL "CELL"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> CELL]".
    cSimpl.

    cStepsT. cInlineT. cStepsT.
    cForceT tt. cForceT (tt↑). cForceT.
    iSplitR; first done.
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as (r) "[-> HEADER]".
    cSimpl.

    cStepsT. cInlineT. cStepsT.
    cForceT (r, Vundef, shared_header l 0).
    cForceT ((r, shared_header l 0)↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl. cStepsT.

    iMod (ghost_map_alloc_empty (K := nat) (V := Qp))
      as (γb) "BORROWS".
    destruct (registry !! r) as [[l' γb']|] eqn:FRESH.
    - iDestruct (big_sepM_lookup_acc _ _ r (l', γb')
        with "REPS") as "[OLD _]"; first exact FRESH.
      iDestruct (cell_rep_header with "OLD") as (old) "OLD".
      iDestruct (pointsto_agree_valid with "HEADER OLD")
        as %[_ INVALID].
      exfalso. move: INVALID. vm_compute.
      intros BAD. apply BAD. done.
    - iMod (ghost_map_insert_persist r (l, γb) with "REG")
        as "[REG #REF]"; first exact FRESH.
      iAssert (cell_rep r (l, γb))
        with "[HEADER BORROWS CELL]" as "NEW".
      { rewrite /cell_rep. iLeft. iExists (∅ : gmap nat Qp).
        rewrite /shared_rep map_size_empty.
        iExists 1%Qp, _q. iFrame.
        iPureIntro. split.
        - rewrite borrow_total_empty. done.
        - apply map_Forall_empty. }
      iAssert
        ([∗ map] r' ↦ info ∈ <[r := (l, γb)]> registry,
          cell_rep r' info)%I
        with "[NEW REPS]" as "REPS".
      { rewrite big_sepM_insert; last exact FRESH. iFrame. }

      cForceS (r↑). cStepsS. cForcesS.
      iSplitL "REF".
      { iSplitR "REF"; first done.
        iExists r, l. iSplitR "REF"; first done.
        rewrite /RefCell. iExists γb. iExact "REF". }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplitR "REG REPS"; first done.
      iExists (<[r := (l, γb)]> registry). iFrame.
  Qed.

  Lemma simF_try_borrow :
    ISim.sim_fun open RefCellAMod RefCellIMod Ist
      (fid RefCellHdr.try_borrow).
  Proof.
    cStartFunSim.
    rewrite /RefCellI.try_borrow.
    cStepsT. cStepsS.
    destruct _q as [r l].
    iDestruct "ASM" as "[-> [-> REF]]".
    iDestruct "REF" as (γb) "#REF".
    iDestruct "IST" as (registry) "[REG REPS]".
    iPoseProof (ghost_map_lookup with "REG REF") as "%LOOK".
    iDestruct (big_sepM_lookup_acc _ _ r (l, γb)
      with "REPS") as "[REP CLOSE]"; first exact LOOK.

    iEval (rewrite /cell_rep) in "REP".
    iDestruct "REP" as "[SHARED | MUTABLE]".
    - iDestruct "SHARED" as (bs q0 v)
        "(HEADER & BORROWS & CELL & %ACCOUNT)".
      destruct ACCOUNT as [CONS ALL_LT].
      cStepsT. cInlineT. cStepsT.
      cForceT (r, 1%Qp, shared_header l (size bs)).
      cForceT (r↑). cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. cStepsT.

      iPoseProof (pointsto_valid with "CELL") as "%Q0_VALID".
      iPoseProof (pointsto_split_merge l v
        (q0 / 2)%Qp (q0 / 2)%Qp) as "SPLIT".
      iEval (rewrite Qp.div_2) in "SPLIT".
      iDestruct ("SPLIT" with "CELL") as "[CELL RETCELL]".
      set (id := fresh (dom bs)).
      assert (FRESH : bs !! id = None).
      { apply not_elem_of_dom. subst id. apply is_fresh. }
      iMod (ghost_map_insert id (q0 / 2)%Qp with "BORROWS")
        as "[BORROWS TICKET]"; first exact FRESH.

      cStepsT. cInlineT. cStepsT.
      cForceT
        (r, shared_header l (size bs),
          shared_header l (S (size bs))).
      cForceT ((r, shared_header l (S (size bs)))↑).
      cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. cStepsT.

      have HALF_LT : (q0 / 2 < 1)%Qp.
      { apply qp_half_lt_one. exact Q0_VALID. }
      have CONS' :
          (borrow_total (<[id := (q0 / 2)%Qp]> bs) +
            Qp_to_Qc (q0 / 2)%Qp = 1)%Qc.
      { apply borrow_total_insert_half; done. }
      have ALL_LT' :
          map_Forall (fun _ q => (q < 1)%Qp)
            (<[id := (q0 / 2)%Qp]> bs).
      { apply map_Forall_insert_2; done. }
      iAssert (cell_rep r (l, γb))
        with "[HEADER BORROWS CELL]" as "REP".
      { rewrite /cell_rep. iLeft.
        iExists (<[id := (q0 / 2)%Qp]> bs).
        rewrite /shared_rep map_size_insert_None; last exact FRESH.
        iExists (q0 / 2)%Qp, v. iFrame.
        iPureIntro. split; done. }
      iSpecialize ("CLOSE" with "REP").

      cForceS ((Some l : option loc)↑). cStepsS. cForcesS.
      iSplitL "RETCELL TICKET".
      { iSplitR "RETCELL TICKET"; first done.
        iSplit.
        - rewrite /RefCell. iExists γb. iExact "REF".
        - iRight. iExists (q0 / 2)%Qp, v.
          iSplitR; first done.
          iSplitR; first done.
          iFrame "RETCELL".
          rewrite /Borrowed. iExists l, γb, id.
          iSplit; [iExact "REF"|iExact "TICKET"]. }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplitR "REG CLOSE"; first done.
      iExists registry. iFrame.

    - iDestruct "MUTABLE" as (id) "[HEADER BORROWS]".
      cStepsT. cInlineT. cStepsT.
      cForceT (r, 1%Qp, mutable_header l).
      cForceT (r↑). cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. cStepsT.
      iAssert (cell_rep r (l, γb))
        with "[HEADER BORROWS]" as "REP".
      { rewrite /cell_rep. iRight.
        rewrite /mutable_rep. iExists id. iFrame. }
      iSpecialize ("CLOSE" with "REP").

      cForceS ((None : option loc)↑). cStepsS. cForcesS.
      iSplitR "REG CLOSE".
      { iSplitR; first done.
        iSplit.
        - rewrite /RefCell. iExists γb. iExact "REF".
        - iLeft. done. }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplitR "REG CLOSE"; first done.
      iExists registry. iFrame.
  Qed.

  Lemma simF_try_borrow_mut :
    ISim.sim_fun open RefCellAMod RefCellIMod Ist
      (fid RefCellHdr.try_borrow_mut).
  Proof.
    cStartFunSim.
    rewrite /RefCellI.try_borrow_mut.
    cStepsT. cStepsS.
    destruct _q as [r l].
    iDestruct "ASM" as "[-> [-> REF]]".
    iDestruct "REF" as (γb) "#REF".
    iDestruct "IST" as (registry) "[REG REPS]".
    iPoseProof (ghost_map_lookup with "REG REF") as "%LOOK".
    iDestruct (big_sepM_lookup_acc _ _ r (l, γb)
      with "REPS") as "[REP CLOSE]"; first exact LOOK.

    iEval (rewrite /cell_rep) in "REP".
    iDestruct "REP" as "[SHARED | MUTABLE]".
    - iDestruct "SHARED" as (bs q0 v)
        "(HEADER & BORROWS & CELL & %ACCOUNT)".
      destruct ACCOUNT as [CONS ALL_LT].
      cStepsT. cInlineT. cStepsT.
      cForceT (r, 1%Qp, shared_header l (size bs)).
      cForceT (r↑). cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl.
      destruct (size bs) as [|n] eqn:SIZE.
      + cStepsT.
        apply map_size_empty_inv in SIZE. subst bs.
        rewrite borrow_total_empty Qcplus_0_l in CONS.
        have Q0_ONE : q0 = 1%Qp.
        { apply (proj1 (Qp.to_Qc_inj_iff q0 1%Qp)).
          change (Qp_to_Qc q0 = Qc_of_Z 1).
          rewrite Z2Qc_inj_1. exact CONS. }
        subst q0.
        iMod (ghost_map_insert 0 1%Qp with "BORROWS")
          as "[BORROWS TICKET]"; first apply lookup_empty.

        cStepsT. cInlineT. cStepsT.
        cForceT
          (r, shared_header l 0, mutable_header l).
        cForceT ((r, mutable_header l)↑). cForceT.
        iSplitL "HEADER"; first (iFrame; done).
        cStepsT.
        iDestruct "GRT" as "[-> GRT]".
        iDestruct "GRT" as "[-> HEADER]".
        cSimpl. cStepsT.

        iAssert (cell_rep r (l, γb))
          with "[HEADER BORROWS]" as "REP".
        { rewrite /cell_rep. iRight.
          rewrite /mutable_rep. iExists 0. iFrame. }
        iSpecialize ("CLOSE" with "REP").

        cForceS ((Some l : option loc)↑). cStepsS. cForcesS.
        iSplitL "CELL TICKET".
        { iSplitR "CELL TICKET"; first done.
          iSplit.
          - rewrite /RefCell. iExists γb. iExact "REF".
          - iRight. iExists v.
            iSplitR; first done.
            iFrame "CELL".
            rewrite /Borrowed. iExists l, γb, 0.
            iSplit; [iExact "REF"|iExact "TICKET"]. }
        cStep.
        rewrite /ist_with_eq /Ist.
        iSplitR "REG CLOSE"; first done.
        iExists registry. iFrame.

      + cStepsT.
        iAssert (cell_rep r (l, γb))
          with "[HEADER BORROWS CELL]" as "REP".
        { rewrite /cell_rep. iLeft. iExists bs.
          rewrite /shared_rep SIZE.
          iExists q0, v. iFrame.
          iPureIntro. split; done. }
        iSpecialize ("CLOSE" with "REP").

        cForceS ((None : option loc)↑). cStepsS. cForcesS.
        iSplitR "REG CLOSE".
        { iSplitR; first done.
          iSplit.
          - rewrite /RefCell. iExists γb. iExact "REF".
          - iLeft. done. }
        cStep.
        rewrite /ist_with_eq /Ist.
        iSplitR "REG CLOSE"; first done.
        iExists registry. iFrame.

    - iDestruct "MUTABLE" as (id) "[HEADER BORROWS]".
      cStepsT. cInlineT. cStepsT.
      cForceT (r, 1%Qp, mutable_header l).
      cForceT (r↑). cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. cStepsT.
      iAssert (cell_rep r (l, γb))
        with "[HEADER BORROWS]" as "REP".
      { rewrite /cell_rep. iRight.
        rewrite /mutable_rep. iExists id. iFrame. }
      iSpecialize ("CLOSE" with "REP").

      cForceS ((None : option loc)↑). cStepsS. cForcesS.
      iSplitR "REG CLOSE".
      { iSplitR; first done.
        iSplit.
        - rewrite /RefCell. iExists γb. iExact "REF".
        - iLeft. done. }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplitR "REG CLOSE"; first done.
      iExists registry. iFrame.
  Qed.

  Lemma simF_drop :
    ISim.sim_fun open RefCellAMod RefCellIMod Ist
      (fid RefCellHdr.drop).
  Proof.
    cStartFunSim.
    rewrite /RefCellI.drop.
    cStepsT. cStepsS.
    destruct _q as [[[r l] q] v].
    iDestruct "ASM" as "[-> ASM]".
    iDestruct "ASM" as "[-> ASM]".
    iDestruct "ASM" as "[REF ASM]".
    iDestruct "ASM" as "[BORROWED CELL]".
    iDestruct "REF" as (γb) "#REF".
    iDestruct "BORROWED" as (l' γb' id) "[#BREF TICKET]".
    iDestruct (ghost_map_elem_agree with "REF BREF") as %INFO.
    injection INFO as L_EQ G_EQ. subst l' γb'.

    iDestruct "IST" as (registry) "[REG REPS]".
    iPoseProof (ghost_map_lookup with "REG REF") as "%LOOK".
    iDestruct (big_sepM_lookup_acc _ _ r (l, γb)
      with "REPS") as "[REP CLOSE]"; first exact LOOK.
    iEval (rewrite /cell_rep) in "REP".
    iDestruct "REP" as "[SHARED | MUTABLE]".

    - iDestruct "SHARED" as (bs q0 v0)
        "(HEADER & BORROWS & RESIDUAL & %ACCOUNT)".
      destruct ACCOUNT as [CONS ALL_LT].
      iPoseProof (ghost_map_lookup with "BORROWS TICKET") as "%HIT".
      have SIZE :
          size bs = S (size (delete id bs)).
      { apply map_size_delete_hit with q. exact HIT. }
      iPoseProof (pointsto_agree_valid with "CELL RESIDUAL")
        as "%VALUE_VALID".
      destruct VALUE_VALID as [VALUE _]. subst v0.
      iAssert (l ↦{(q + q0)%Qp} v)%I
        with "[CELL RESIDUAL]" as "RESIDUAL".
      { iApply (pointsto_split_merge l v q q0). iFrame. }
      iMod (ghost_map_delete with "BORROWS TICKET") as "BORROWS".

      cStepsT. cInlineT. cStepsT.
      cForceT (r, 1%Qp, shared_header l (size bs)).
      cForceT (r↑). cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. rewrite SIZE. cStepsT.

      cStepsT. cInlineT. cStepsT.
      cForceT
        (r, shared_header l (S (size (delete id bs))),
          shared_header l (size (delete id bs))).
      cForceT ((r, shared_header l (size (delete id bs)))↑).
      cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. cStepsT.

      have CONS' :
          (borrow_total (delete id bs) +
            Qp_to_Qc (q + q0) = 1)%Qc.
      { apply borrow_total_delete_merge with (bs := bs) (id := id);
          done. }
      have ALL_LT' :
          map_Forall (fun _ q' => (q' < 1)%Qp) (delete id bs).
      { apply map_Forall_delete. exact ALL_LT. }
      iAssert (cell_rep r (l, γb))
        with "[HEADER BORROWS RESIDUAL]" as "REP".
      { rewrite /cell_rep. iLeft. iExists (delete id bs).
        rewrite /shared_rep.
        iExists (q + q0)%Qp, v. iFrame.
        iPureIntro. split; done. }
      iSpecialize ("CLOSE" with "REP").

      cForceS (tt↑). cStepsS. cForcesS.
      iSplitR "REG CLOSE".
      { iSplitR; first done.
        iSplitR; first done.
        rewrite /RefCell. iExists γb. iExact "REF". }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplitR "REG CLOSE"; first done.
      iExists registry. iFrame.

    - iDestruct "MUTABLE" as (owner)
        "[HEADER BORROWS]".
      iPoseProof (ghost_map_lookup with "BORROWS TICKET") as "%HIT".
      apply lookup_singleton_Some in HIT.
      destruct HIT as [ID QONE]. subst id q.
      iMod (ghost_map_delete with "BORROWS TICKET") as "BORROWS".
      iEval (rewrite delete_singleton) in "BORROWS".

      cStepsT. cInlineT. cStepsT.
      cForceT (r, 1%Qp, mutable_header l).
      cForceT (r↑). cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. cStepsT.

      cStepsT. cInlineT. cStepsT.
      cForceT
        (r, mutable_header l, shared_header l 0).
      cForceT ((r, shared_header l 0)↑). cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. cStepsT.

      iAssert (cell_rep r (l, γb))
        with "[HEADER BORROWS CELL]" as "REP".
      { rewrite /cell_rep. iLeft. iExists (∅ : gmap nat Qp).
        rewrite /shared_rep map_size_empty.
        iExists 1%Qp, v. iFrame.
        iPureIntro. split.
        - rewrite borrow_total_empty. done.
        - apply map_Forall_empty. }
      iSpecialize ("CLOSE" with "REP").

      cForceS (tt↑). cStepsS. cForcesS.
      iSplitR "REG CLOSE".
      { iSplitR; first done.
        iSplitR; first done.
        rewrite /RefCell. iExists γb. iExact "REF". }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplitR "REG CLOSE"; first done.
      iExists registry. iFrame.
  Qed.

  Lemma sim :
    ISim.t open RefCellAMod RefCellIMod
      RefCellA.auth_init Ist.
  Proof.
    cStartModSim.
    - vm_compute.
      apply submseteq_cons, submseteq_skip, submseteq_nil.
    - iIntros "REG".
      rewrite /RefCellA.auth_init /Ist.
      iExists (∅ : gmap loc refcell_info).
      rewrite big_sepM_empty. iFrame.
    - apply simF_new_refcell.
    - apply simF_try_borrow.
    - apply simF_try_borrow_mut.
    - apply simF_drop.
  Qed.

End RefCellIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I,
    !frac_memGS, !refcellGS}.

  Lemma ctxr
      (sp_refcell sp_mem : specmap)
      (REFCELL_IN_SP : RefCellA.sp ⊆ sp_refcell) :
    RefCellA.auth_init ⊢
      ctx_refines
        (RefCellI.t ★ FracMemA.t sp_mem)
        (RefCellA.t sp_refcell).
  Proof.
    eapply main_adequacy, sim; eauto.
  Qed.
End contextual_refinement. End RefCellIA.
