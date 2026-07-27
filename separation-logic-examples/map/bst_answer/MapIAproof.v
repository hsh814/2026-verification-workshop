(** * Refinement of the Abstract Map by the BST Implementation *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From mem_answer Require Import MemA.
From map.bst_answer Require Import MapA MapI.

Module MapIA. Section MapIA.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS, !memGS}.

  Context (sp_map sp_mem : specmap).
  Context (MAP_IN_SP : MapA.sp ⊆ sp_map).

  Local Definition MapAMod := MapA.t sp_map.
  Local Definition MapIMod := MapI.t ★ MemA.t sp_mem.

  Inductive tree : Type :=
  | Leaf
  | Node (key : nat) (payload : option nat)
      (left_tree right_tree : tree).

  Fixpoint tree_lookup (query : nat) (t : tree) : option nat :=
    match t with
    | Leaf => None
    | Node key payload left_tree right_tree =>
        match Nat.compare query key with
        | Eq => payload
        | Lt => tree_lookup query left_tree
        | Gt => tree_lookup query right_tree
        end
    end.

  Fixpoint tree_insert (query value : nat) (t : tree) : tree :=
    match t with
    | Leaf => Node query (Some value) Leaf Leaf
    | Node key payload left_tree right_tree =>
        match Nat.compare query key with
        | Eq => Node key (Some value) left_tree right_tree
        | Lt =>
            Node key payload
              (tree_insert query value left_tree) right_tree
        | Gt =>
            Node key payload
              left_tree (tree_insert query value right_tree)
        end
    end.

  Fixpoint tree_delete (query : nat) (t : tree) : tree :=
    match t with
    | Leaf => Leaf
    | Node key payload left_tree right_tree =>
        match Nat.compare query key with
        | Eq => Node key None left_tree right_tree
        | Lt =>
            Node key payload (tree_delete query left_tree) right_tree
        | Gt =>
            Node key payload left_tree (tree_delete query right_tree)
        end
    end.

  Fixpoint tree_Forall (P : nat → Prop) (t : tree) : Prop :=
    match t with
    | Leaf => True
    | Node key _ left_tree right_tree =>
        P key ∧ tree_Forall P left_tree ∧ tree_Forall P right_tree
    end.

  Fixpoint bst (t : tree) : Prop :=
    match t with
    | Leaf => True
    | Node key _ left_tree right_tree =>
        bst left_tree ∧
        bst right_tree ∧
        tree_Forall (λ child, child < key) left_tree ∧
        tree_Forall (λ child, key < child) right_tree
    end.

  Definition tree_models (t : tree) (m : amap) : Prop :=
    ∀ query, tree_lookup query t = m !! query.

  Lemma tree_lookup_insert query key value t :
    tree_lookup query (tree_insert key value t) =
      if decide (query = key)
      then Some value
      else tree_lookup query t.
  Proof.
    induction t as [|node payload left_tree IHl right_tree IHr].
    - simpl.
      destruct (Nat.compare_spec query key) as [-> | Hlt | Hgt];
        simpl; case_decide; try done; exfalso; lia.
    - simpl.
      destruct (Nat.compare_spec key node) as [-> | Hkn | Hnk].
      + simpl.
        destruct (Nat.compare_spec query node) as [-> | Hqn | Hnq];
          simpl; case_decide; try done; exfalso; lia.
      + simpl.
        destruct (Nat.compare_spec query node) as [-> | Hqn | Hnq];
          simpl; rewrite ?IHl; case_decide; try done; exfalso; lia.
      + simpl.
        destruct (Nat.compare_spec query node) as [-> | Hqn | Hnq];
          simpl; rewrite ?IHr; case_decide; try done; exfalso; lia.
  Qed.

  Lemma tree_lookup_delete query key t :
    tree_lookup query (tree_delete key t) =
      if decide (query = key)
      then None
      else tree_lookup query t.
  Proof.
    induction t as [|node payload left_tree IHl right_tree IHr].
    - simpl. case_decide; done.
    - simpl.
      destruct (Nat.compare_spec key node) as [-> | Hkn | Hnk].
      + simpl.
        destruct (Nat.compare_spec query node) as [-> | Hqn | Hnq];
          simpl; case_decide; try done; exfalso; lia.
      + simpl.
        destruct (Nat.compare_spec query node) as [-> | Hqn | Hnq];
          simpl; rewrite ?IHl; case_decide; try done; exfalso; lia.
      + simpl.
        destruct (Nat.compare_spec query node) as [-> | Hqn | Hnq];
          simpl; rewrite ?IHr; case_decide; try done; exfalso; lia.
  Qed.

  Lemma tree_Forall_insert P key value t :
    P key →
    tree_Forall P t →
    tree_Forall P (tree_insert key value t).
  Proof.
    induction t as [|node payload left_tree IHl right_tree IHr];
      simpl; intros Hkey Htree.
    - repeat split; done.
    - destruct Htree as (Hnode & Hleft & Hright).
      destruct (Nat.compare_spec key node) as [-> | Hkn | Hnk];
        simpl; repeat split; eauto.
  Qed.

  Lemma tree_Forall_delete P key t :
    tree_Forall P t →
    tree_Forall P (tree_delete key t).
  Proof.
    induction t as [|node payload left_tree IHl right_tree IHr];
      simpl; intros Htree; first done.
    destruct Htree as (Hnode & Hleft & Hright).
    destruct (Nat.compare_spec key node) as [-> | Hkn | Hnk];
      simpl; repeat split; eauto.
  Qed.

  Lemma bst_insert key value t :
    bst t → bst (tree_insert key value t).
  Proof.
    induction t as [|node payload left_tree IHl right_tree IHr];
      simpl; intros Hbst; first done.
    destruct Hbst as (Hbl & Hbr & Hleft & Hright).
    destruct (Nat.compare_spec key node) as [-> | Hkn | Hnk];
      simpl; repeat split; eauto using tree_Forall_insert.
  Qed.

  Lemma bst_delete key t :
    bst t → bst (tree_delete key t).
  Proof.
    induction t as [|node payload left_tree IHl right_tree IHr];
      simpl; intros Hbst; first done.
    destruct Hbst as (Hbl & Hbr & Hleft & Hright).
    destruct (Nat.compare_spec key node) as [-> | Hkn | Hnk];
      simpl; repeat split; eauto using tree_Forall_delete.
  Qed.

  Lemma tree_models_insert t m key value :
    tree_models t m →
    tree_models (tree_insert key value t) (<[key := value]> m).
  Proof.
    intros Hmodels query.
    rewrite tree_lookup_insert.
    destruct (decide (query = key)) as [-> | Hne].
    - symmetry. apply lookup_insert.
    - rewrite lookup_insert_ne; first apply Hmodels.
      done.
  Qed.

  Lemma tree_models_delete t m key :
    tree_models t m →
    tree_models (tree_delete key t) (delete key m).
  Proof.
    intros Hmodels query.
    rewrite tree_lookup_delete.
    destruct (decide (query = key)) as [-> | Hne].
    - symmetry. apply lookup_delete.
    - rewrite lookup_delete_ne; first apply Hmodels.
      done.
  Qed.

  Fixpoint tree_rep (root : option loc) (t : tree) : iProp Σ :=
    match t with
    | Leaf => ⌜root = None⌝
    | Node key payload left_tree right_tree =>
        ∃ node left_root right_root,
          ⌜root = Some node⌝ ∗
          node ↦ MapI.node_val key payload left_root right_root ∗
          tree_rep left_root left_tree ∗
          tree_rep right_root right_tree
    end%I.

  Definition represents (header : loc) (m : amap) : iProp Σ :=
    (∃ root t,
      header ↦ Vloc root ∗
      tree_rep root t ∗
      ⌜bst t ∧ tree_models t m⌝)%I.

  (** The authoritative map supports any number of simultaneously live map
      handles.  The separating big map owns one disjoint concrete BST per
      abstract entry. *)
  Definition Ist : ist_type Σ :=
    (λ st_src st_tgt,
      ⌜st_src = ∅ ∧ st_tgt = ∅⌝ ∗
      ∃ models : gmap loc amap,
        ghost_map_auth map_name 1 models ∗
        [∗ map] header ↦ m ∈ models, represents header m)%I.

  Lemma simF_new_map :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.new_map).
  Proof.
    cStartFunSim.
    rewrite /MapI.new_map.
    cStepsT. cStepsS.
    iDestruct "ASM" as "[-> ->]".
    iDestruct "IST" as "[%ST IST]".
    destruct ST as [-> ->].
    iDestruct "IST" as (models) "[AUTH REPS]".
    cStepsT. cInlineT. cStepsT.
    cForceT tt. cForceT (tt↑). cForceT.
    iSplitR; first done.
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as (header) "[-> CELL]".
    destruct (models !! header) as [old |] eqn:FRESH.
    {
      iPoseProof
        (big_sepM_lookup _ models header old FRESH with "REPS") as "OLD".
      iDestruct "OLD" as (root t) "(OLD_HEADER & TREE & MODEL)".
      iPoseProof
        (ghost_map_elem_ne with "CELL OLD_HEADER") as "%NE".
      exfalso. apply NE. done. }
    cSimpl. cStepsT. cInlineT. cStepsT.
    cForceT (header, Vundef, Vloc None).
    cForceT ((header, Vloc None)↑). cForceT.
    iSplitL "CELL"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    iMod (ghost_map_insert header (∅ : amap) FRESH with "AUTH")
      as "[AUTH MAP]".
    cSimpl. cStepsT.
    cForceS (header↑). cStepsS. cForcesS.
    iSplitL "MAP".
    { iSplitR "MAP"; first done.
      iExists header. iFrame. done. }
    cStep.
    rewrite /ist_with_eq /Ist.
    iSplit; first done.
    iSplit; first done.
    iExists (<[header := ∅]> models). iFrame.
    rewrite big_sepM_insert; last done.
    iFrame. rewrite /represents.
    iExists Leaf. iFrame. done.
  Qed.

  Lemma simF_get :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.get).
  Proof.
    cStartFunSim.
    rewrite /MapI.get.
    cStepsT. cStepsS.
    cStepsT. cStepsS.
    destruct _q as [[header m] query].
    iDestruct "ASM" as "[-> [-> MAP]]".
    iDestruct "IST" as "[%ST IST]".
    destruct ST as [-> ->].
    iDestruct "IST" as (models) "[AUTH REPS]".
    iPoseProof (ghost_map_lookup with "AUTH MAP") as "%HIT".
    iDestruct
      (big_sepM_lookup_acc _ models header m HIT with "REPS")
      as "[REP REPS]".
    iDestruct "REP" as (root t) "(HEADER & TREE & %BST & %MODEL)".
    cStepsT. cInlineT. cStepsT.
    cForceT (header, Vloc root).
    cForceT (header↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl.
    cStepsT.
    pose proof (MODEL query) as LOOKUP.
    iAssert (tree_rep root t -∗ represents header m)%I
      with "[HEADER]" as "REBUILD".
    { iIntros "TREE". iExists root, t. iFrame. done. }
    iAssert
      (⌜tree_lookup query t = m !! query⌝ ∗ tree_rep root t)%I
      with "[TREE]" as "TREE".
    { iFrame. done. }
    clear BST MODEL LOOKUP.
    iRevert "TREE". iRevert "REBUILD". iStopProof.
    revert root.
    induction t as [|key payload left_tree IHl right_tree IHr];
      intros root;
      iIntros "(AUTH & MAP & REPS) REBUILD [%LOOKUP TREE]".
    - iDestruct "TREE" as %->.
      cStepsT.
      rewrite unfold_iterC. cStepT. cStepsT.
      iAssert (tree_rep None Leaf)%I as "TREE"; first done.
      iSpecialize ("REBUILD" with "TREE").
      iSpecialize ("REPS" with "REBUILD").
      simpl in LOOKUP.
      cForceS ((None : option nat)↑). cStepsS. cForcesS.
      iSplitL "MAP".
      { iSplitR "MAP"; first done.
        iSplitR "MAP"; first (rewrite <- LOOKUP; done).
        iExact "MAP". }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplit; first done.
      iSplit; first done.
      iExists models. iFrame.
    - iDestruct "TREE" as
        (node left_root right_root)
        "(%ROOT & NODE & LEFT & RIGHT)".
      subst root.
      cStepsT. rewrite unfold_iterC. cStepT.
      cStepsT. cInlineT. cStepsT.
      cForceT
        (node, MapI.node_val key payload left_root right_root).
      cForceT (node↑). cForceT.
      iSplitL "NODE"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> NODE]".
      cSimpl.
      destruct payload as [value |]; cSimpl.
      all: destruct (Nat.compare_spec query key)
        as [-> | Hlt | Hgt]; cSimpl.
      + cStepsT. rewrite Nat.compare_refl. cStepsT.
        iAssert
          (tree_rep (Some node)
            (Node key (Some value) left_tree right_tree))%I
          with "[NODE LEFT RIGHT]" as "TREE".
        { simpl. iExists node, left_root, right_root. iFrame. done. }
        iSpecialize ("REBUILD" with "TREE").
        iSpecialize ("REPS" with "REBUILD").
        cForceS ((Some value : option nat)↑). cStepsS. cForcesS.
        iSplitL "MAP".
        { iSplitR "MAP"; first done.
          iSplitR "MAP"; first (rewrite <- LOOKUP; done).
          iExact "MAP". }
        cStep.
        rewrite /ist_with_eq /Ist.
        iSplit; first done.
        iSplit; first done.
        iExists models. iFrame.
      + assert (CMP : Nat.compare query key = Lt).
        { apply Nat.compare_lt_iff. done. }
        cStepsT. rewrite CMP. cStepsT.
        iAssert
          (tree_rep left_root left_tree -∗ represents header m)%I
          with "[REBUILD NODE RIGHT]" as "REBUILD'".
        { iIntros "LEFT".
          iApply "REBUILD".
          simpl. iExists node, left_root, right_root. iFrame. done. }
        iPoseProof
          (IHl left_root with "[$AUTH $MAP $REPS]") as "IH".
        iSpecialize ("IH" with "REBUILD'").
        iApply "IH". iFrame. done.
      + assert (CMP : Nat.compare query key = Gt).
        { apply Nat.compare_gt_iff. done. }
        cStepsT. rewrite CMP. cStepsT.
        iAssert
          (tree_rep right_root right_tree -∗ represents header m)%I
          with "[REBUILD NODE LEFT]" as "REBUILD'".
        { iIntros "RIGHT".
          iApply "REBUILD".
          simpl. iExists node, left_root, right_root. iFrame. done. }
        iPoseProof
          (IHr right_root with "[$AUTH $MAP $REPS]") as "IH".
        iSpecialize ("IH" with "REBUILD'").
        iApply "IH". iFrame. done.
      + cStepsT. rewrite Nat.compare_refl. cStepsT.
        iAssert
          (tree_rep (Some node)
            (Node key None left_tree right_tree))%I
          with "[NODE LEFT RIGHT]" as "TREE".
        { simpl. iExists node, left_root, right_root. iFrame. done. }
        iSpecialize ("REBUILD" with "TREE").
        iSpecialize ("REPS" with "REBUILD").
        cForceS ((None : option nat)↑). cStepsS. cForcesS.
        iSplitL "MAP".
        { iSplitR "MAP"; first done.
          iSplitR "MAP"; first (rewrite <- LOOKUP; done).
          iExact "MAP". }
        cStep.
        rewrite /ist_with_eq /Ist.
        iSplit; first done.
        iSplit; first done.
        iExists models. iFrame.
      + assert (CMP : Nat.compare query key = Lt).
        { apply Nat.compare_lt_iff. done. }
        cStepsT. rewrite CMP. cStepsT.
        iAssert
          (tree_rep left_root left_tree -∗ represents header m)%I
          with "[REBUILD NODE RIGHT]" as "REBUILD'".
        { iIntros "LEFT".
          iApply "REBUILD".
          simpl. iExists node, left_root, right_root. iFrame. done. }
        iPoseProof
          (IHl left_root with "[$AUTH $MAP $REPS]") as "IH".
        iSpecialize ("IH" with "REBUILD'").
        iApply "IH". iFrame. done.
      + assert (CMP : Nat.compare query key = Gt).
        { apply Nat.compare_gt_iff. done. }
        cStepsT. rewrite CMP. cStepsT.
        iAssert
          (tree_rep right_root right_tree -∗ represents header m)%I
          with "[REBUILD NODE LEFT]" as "REBUILD'".
        { iIntros "RIGHT".
          iApply "REBUILD".
          simpl. iExists node, left_root, right_root. iFrame. done. }
        iPoseProof
          (IHr right_root with "[$AUTH $MAP $REPS]") as "IH".
        iSpecialize ("IH" with "REBUILD'").
        iApply "IH". iFrame. done.
  Qed.

  Lemma simF_delete :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.delete).
  Proof.
    cStartFunSim.
    rewrite /MapI.delete.
    cStepsT. cStepsS.
    cStepsT. cStepsS.
    destruct _q as [[header m] query].
    iDestruct "ASM" as "[-> [-> MAP]]".
    iDestruct "IST" as "[%ST IST]".
    destruct ST as [-> ->].
    iDestruct "IST" as (models) "[AUTH REPS]".
    iPoseProof (ghost_map_lookup with "AUTH MAP") as "%HIT".
    iDestruct
      (big_sepM_delete _ models header m HIT with "REPS")
      as "[REP REST]".
    iDestruct "REP" as (root t) "(HEADER & TREE & %BST & %MODEL)".
    cStepsT. cInlineT. cStepsT.
    cForceT (header, Vloc root).
    cForceT (header↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl. cStepsT.
    iAssert
      (tree_rep root (tree_delete query t) -∗
        represents header (delete query m))%I
      with "[HEADER]" as "REBUILD".
    { iIntros "TREE".
      iExists root, (tree_delete query t). iFrame.
      iPureIntro. split.
      - apply bst_delete. done.
      - apply tree_models_delete. done. }
    iRevert "TREE". iRevert "REBUILD". iStopProof.
    clear BST MODEL.
    revert root.
    induction t as [|key payload left_tree IHl right_tree IHr];
      intros root;
      iIntros "(AUTH & MAP & REST) REBUILD TREE".
    - iDestruct "TREE" as %->.
      rewrite unfold_iterC. cStepT. cStepsT.
      iAssert (tree_rep None (tree_delete query Leaf))%I
        as "TREE"; first done.
      iSpecialize ("REBUILD" with "TREE").
      iMod (ghost_map_update (delete query m) with "AUTH MAP")
        as "[AUTH MAP]".
      cForceS (tt↑). cStepsS. cForcesS.
      iSplitL "MAP".
      { iSplitR "MAP"; first done.
        iSplitR "MAP"; first done.
        iExact "MAP". }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplit; first done.
      iSplit; first done.
      iExists (<[header := delete query m]> models). iFrame.
      rewrite <- insert_delete_insert.
      rewrite big_sepM_insert; last apply lookup_delete.
      iFrame.
    - iDestruct "TREE" as
        (node left_root right_root)
        "(%ROOT & NODE & LEFT & RIGHT)".
      subst root.
      rewrite unfold_iterC. cStepT.
      cStepsT. cInlineT. cStepsT.
      cForceT
        (node, MapI.node_val key payload left_root right_root).
      cForceT (node↑). cForceT.
      iSplitL "NODE"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> NODE]".
      cSimpl.
      destruct payload as [value |]; cSimpl.
      all: destruct (Nat.compare_spec query key)
        as [-> | Hlt | Hgt]; cSimpl.
      + cStepsT. rewrite Nat.compare_refl. cStepsT.
        cInlineT. cStepsT.
        cForceT
          (node,
            MapI.node_val key (Some value) left_root right_root,
            MapI.node_val key None left_root right_root).
        cForceT
          ((node, MapI.node_val key None left_root right_root)↑).
        cForceT.
        iSplitL "NODE"; first (iFrame; done).
        cStepsT.
        iDestruct "GRT" as "[-> GRT]".
        iDestruct "GRT" as "[-> NODE]".
        cSimpl. cStepsT.
        iAssert
          (tree_rep (Some node)
            (Node key None left_tree right_tree))%I
          with "[NODE LEFT RIGHT]" as "TREE".
        { simpl. iExists node, left_root, right_root. iFrame. done. }
        iSpecialize ("REBUILD" with "TREE").
        iMod (ghost_map_update (delete key m) with "AUTH MAP")
          as "[AUTH MAP]".
        cForceS (tt↑). cStepsS. cForcesS.
        iSplitL "MAP".
        { iSplitR "MAP"; first done.
          iSplitR "MAP"; first done.
          iExact "MAP". }
        cStep.
        rewrite /ist_with_eq /Ist.
        iSplit; first done.
        iSplit; first done.
        iExists (<[header := delete key m]> models). iFrame.
        rewrite <- insert_delete_insert.
        rewrite big_sepM_insert; last apply lookup_delete.
        iFrame.
      + assert (CMP : Nat.compare query key = Lt).
        { apply Nat.compare_lt_iff. done. }
        cStepsT. rewrite CMP. cStepsT.
        iAssert
          (tree_rep left_root (tree_delete query left_tree) -∗
            represents header (delete query m))%I
          with "[REBUILD NODE RIGHT]" as "REBUILD'".
        { iIntros "LEFT".
          iApply "REBUILD".
          simpl. iExists node, left_root, right_root. iFrame. done. }
        iPoseProof
          (IHl left_root with "[$AUTH $MAP $REST]") as "IH".
        iSpecialize ("IH" with "REBUILD'").
        iApply "IH". iExact "LEFT".
      + assert (CMP : Nat.compare query key = Gt).
        { apply Nat.compare_gt_iff. done. }
        cStepsT. rewrite CMP. cStepsT.
        iAssert
          (tree_rep right_root (tree_delete query right_tree) -∗
            represents header (delete query m))%I
          with "[REBUILD NODE LEFT]" as "REBUILD'".
        { iIntros "RIGHT".
          iApply "REBUILD".
          simpl. iExists node, left_root, right_root. iFrame. done. }
        iPoseProof
          (IHr right_root with "[$AUTH $MAP $REST]") as "IH".
        iSpecialize ("IH" with "REBUILD'").
        iApply "IH". iExact "RIGHT".
      + cStepsT. rewrite Nat.compare_refl. cStepsT.
        cInlineT. cStepsT.
        cForceT
          (node,
            MapI.node_val key None left_root right_root,
            MapI.node_val key None left_root right_root).
        cForceT
          ((node, MapI.node_val key None left_root right_root)↑).
        cForceT.
        iSplitL "NODE"; first (iFrame; done).
        cStepsT.
        iDestruct "GRT" as "[-> GRT]".
        iDestruct "GRT" as "[-> NODE]".
        cSimpl. cStepsT.
        iAssert
          (tree_rep (Some node)
            (Node key None left_tree right_tree))%I
          with "[NODE LEFT RIGHT]" as "TREE".
        { simpl. iExists node, left_root, right_root. iFrame. done. }
        iSpecialize ("REBUILD" with "TREE").
        iMod (ghost_map_update (delete key m) with "AUTH MAP")
          as "[AUTH MAP]".
        cForceS (tt↑). cStepsS. cForcesS.
        iSplitL "MAP".
        { iSplitR "MAP"; first done.
          iSplitR "MAP"; first done.
          iExact "MAP". }
        cStep.
        rewrite /ist_with_eq /Ist.
        iSplit; first done.
        iSplit; first done.
        iExists (<[header := delete key m]> models). iFrame.
        rewrite <- insert_delete_insert.
        rewrite big_sepM_insert; last apply lookup_delete.
        iFrame.
      + assert (CMP : Nat.compare query key = Lt).
        { apply Nat.compare_lt_iff. done. }
        cStepsT. rewrite CMP. cStepsT.
        iAssert
          (tree_rep left_root (tree_delete query left_tree) -∗
            represents header (delete query m))%I
          with "[REBUILD NODE RIGHT]" as "REBUILD'".
        { iIntros "LEFT".
          iApply "REBUILD".
          simpl. iExists node, left_root, right_root. iFrame. done. }
        iPoseProof
          (IHl left_root with "[$AUTH $MAP $REST]") as "IH".
        iSpecialize ("IH" with "REBUILD'").
        iApply "IH". iExact "LEFT".
      + assert (CMP : Nat.compare query key = Gt).
        { apply Nat.compare_gt_iff. done. }
        cStepsT. rewrite CMP. cStepsT.
        iAssert
          (tree_rep right_root (tree_delete query right_tree) -∗
            represents header (delete query m))%I
          with "[REBUILD NODE LEFT]" as "REBUILD'".
        { iIntros "RIGHT".
          iApply "REBUILD".
          simpl. iExists node, left_root, right_root. iFrame. done. }
        iPoseProof
          (IHr right_root with "[$AUTH $MAP $REST]") as "IH".
        iSpecialize ("IH" with "REBUILD'").
        iApply "IH". iExact "RIGHT".
  Qed.

  Lemma simF_insert :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.insert).
  Proof.
    cStartFunSim.
    rewrite /MapI.insert.
    cStepsT. cStepsS.
    cStepsT. cStepsS.
    destruct _q as [[[header m] query] value].
    iDestruct "ASM" as "[-> [-> MAP]]".
    iDestruct "IST" as "[%ST IST]".
    destruct ST as [-> ->].
    iDestruct "IST" as (models) "[AUTH REPS]".
    iPoseProof (ghost_map_lookup with "AUTH MAP") as "%HIT".
    iDestruct
      (big_sepM_delete _ models header m HIT with "REPS")
      as "[REP REST]".
    iDestruct "REP" as (root t) "(HEADER & TREE & %BST & %MODEL)".
    cStepsT. cInlineT. cStepsT.
    cForceT (header, Vloc root).
    cForceT (header↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl. cStepsT.
    destruct t as [|key payload left_tree right_tree].
    - iDestruct "TREE" as %->.
      cStepsT. cInlineT. cStepsT.
      cForceT tt. cForceT (tt↑). cForceT.
      iSplitR; first done.
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as (node) "[-> NODE]".
      cSimpl. cStepsT. cInlineT. cStepsT.
      cForceT
        (node, Vundef,
          MapI.node_val query (Some value) None None).
      cForceT
        ((node, MapI.node_val query (Some value) None None)↑).
      cForceT.
      iSplitL "NODE"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> NODE]".
      cSimpl. cStepsT. cInlineT. cStepsT.
      cForceT (header, Vloc None, Vloc (Some node)).
      cForceT ((header, Vloc (Some node))↑). cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. cStepsT.
      iMod (ghost_map_update (<[query := value]> m) with "AUTH MAP")
        as "[AUTH MAP]".
      cForceS (tt↑). cStepsS. cForcesS.
      iSplitL "MAP".
      { iSplitR "MAP"; first done.
        iSplitR "MAP"; first done.
        iExact "MAP". }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplit; first done.
      iSplit; first done.
      iExists (<[header := <[query := value]> m]> models). iFrame.
      rewrite <- insert_delete_insert.
      rewrite big_sepM_insert; last apply lookup_delete.
      iFrame.
      rewrite /represents.
      iExists (Node query (Some value) Leaf Leaf).
      iFrame. simpl.
      iSplit; first done.
      iPureIntro. split.
      + done.
      + change
          (tree_models (tree_insert query value Leaf)
            (<[query := value]> m)).
        apply tree_models_insert. done.
    - iDestruct "TREE" as
        (node left_root right_root)
        "(%ROOT & NODE & LEFT & RIGHT)".
      subst root.
      cStepsT.
      iAssert
        (tree_rep (Some node)
          (tree_insert query value
            (Node key payload left_tree right_tree)) -∗
          represents header (<[query := value]> m))%I
        with "[HEADER]" as "REBUILD".
      { iIntros "TREE".
        iExists (Some node),
          (tree_insert query value
            (Node key payload left_tree right_tree)).
        iFrame. iPureIntro. split.
        - apply bst_insert. done.
        - apply tree_models_insert. done. }
      iAssert
        (tree_rep (Some node)
          (Node key payload left_tree right_tree))%I
        with "[NODE LEFT RIGHT]" as "TREE".
      { simpl. iExists node, left_root, right_root. iFrame. done. }
      iRevert "TREE". iRevert "REBUILD". iStopProof.
      clear BST MODEL.
      generalize (Node key payload left_tree right_tree) as current.
      intro current.
      clear key payload left_tree right_tree.
      revert node.
      induction current as
        [|key payload left_tree IHl right_tree IHr];
        intros node;
        iIntros "(AUTH & MAP & REST) REBUILD TREE".
      + iDestruct "TREE" as %BAD. done.
      + iDestruct "TREE" as
          (node' left_root' right_root')
          "(%ROOT & NODE & LEFT & RIGHT)".
        simplify_eq.
        rewrite unfold_iterC. cStepT.
        cStepsT. cInlineT. cStepsT.
        cForceT
          (node',
            MapI.node_val key payload left_root' right_root').
        cForceT (node'↑). cForceT.
        iSplitL "NODE"; first (iFrame; done).
        cStepsT.
        iDestruct "GRT" as "[-> GRT]".
        iDestruct "GRT" as "[-> NODE]".
        cSimpl.
        destruct payload as [old_value |]; cSimpl.
        all: destruct (Nat.compare_spec query key)
          as [-> | Hlt | Hgt]; cSimpl.
        * cStepsT. rewrite Nat.compare_refl. cStepsT.
          cInlineT. cStepsT.
          cForceT
            (node',
              MapI.node_val key (Some old_value)
                left_root' right_root',
              MapI.node_val key (Some value)
                left_root' right_root').
          cForceT
            ((node',
              MapI.node_val key (Some value)
                left_root' right_root')↑).
          cForceT.
          iSplitL "NODE"; first (iFrame; done).
          cStepsT.
          iDestruct "GRT" as "[-> GRT]".
          iDestruct "GRT" as "[-> NODE]".
          cSimpl. cStepsT.
          iAssert
            (tree_rep (Some node')
              (Node key (Some value) left_tree right_tree))%I
            with "[NODE LEFT RIGHT]" as "TREE".
          { simpl. iExists node', left_root', right_root'.
            iFrame. done. }
          iSpecialize ("REBUILD" with "TREE").
          iMod
            (ghost_map_update (<[key := value]> m) with "AUTH MAP")
            as "[AUTH MAP]".
          cForceS (tt↑). cStepsS. cForcesS.
          iSplitL "MAP".
          { iSplitR "MAP"; first done.
            iSplitR "MAP"; first done.
            iExact "MAP". }
          cStep.
          rewrite /ist_with_eq /Ist.
          iSplit; first done.
          iSplit; first done.
          iExists (<[header := <[key := value]> m]> models).
          iFrame.
          rewrite <- insert_delete_insert.
          rewrite big_sepM_insert; last apply lookup_delete.
          iFrame.
        * assert (CMP : Nat.compare query key = Lt).
          { apply Nat.compare_lt_iff. done. }
          cStepsT. rewrite CMP. cStepsT.
          destruct left_tree as
            [|left_key left_payload left_left left_right].
          { iDestruct "LEFT" as %->.
            cStepsT. cInlineT. cStepsT.
            cForceT tt. cForceT (tt↑). cForceT.
            iSplitR; first done.
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as (fresh) "[-> FRESH]".
            cSimpl. cStepsT. cInlineT. cStepsT.
            cForceT
              (fresh, Vundef,
                MapI.node_val query (Some value) None None).
            cForceT
              ((fresh,
                MapI.node_val query (Some value) None None)↑).
            cForceT.
            iSplitL "FRESH"; first (iFrame; done).
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as "[-> FRESH]".
            cSimpl. cStepsT. cInlineT. cStepsT.
            cForceT
              (node',
                MapI.node_val key (Some old_value)
                  None right_root',
                MapI.node_val key (Some old_value)
                  (Some fresh) right_root').
            cForceT
              ((node',
                MapI.node_val key (Some old_value)
                  (Some fresh) right_root')↑).
            cForceT.
            iSplitL "NODE"; first (iFrame; done).
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as "[-> NODE]".
            cSimpl. cStepsT.
            iAssert
              (tree_rep (Some node')
                (Node key (Some old_value)
                  (Node query (Some value) Leaf Leaf)
                  right_tree))%I
              with "[NODE FRESH RIGHT]" as "TREE".
            { simpl.
              iExists node', (Some fresh), right_root'. iFrame.
              done. }
            iSpecialize ("REBUILD" with "TREE").
            iMod
              (ghost_map_update (<[query := value]> m)
                with "AUTH MAP") as "[AUTH MAP]".
            cForceS (tt↑). cStepsS. cForcesS.
            iSplitL "MAP".
            { iSplitR "MAP"; first done.
              iSplitR "MAP"; first done.
              iExact "MAP". }
            cStep.
            rewrite /ist_with_eq /Ist.
            iSplit; first done.
            iSplit; first done.
            iExists
              (<[header := <[query := value]> m]> models).
            iFrame.
            rewrite <- insert_delete_insert.
            rewrite big_sepM_insert; last apply lookup_delete.
            iFrame. }
          { iDestruct "LEFT" as
              (child child_left child_right)
              "(%ROOT & CHILD & CHILD_LEFT & CHILD_RIGHT)".
            simplify_eq.
            cStepsT.
            iAssert
              (tree_rep (Some child)
                (Node left_key left_payload left_left left_right))%I
              with "[CHILD CHILD_LEFT CHILD_RIGHT]" as "LEFT".
            { simpl. iExists child, child_left, child_right.
              iFrame. done. }
            iAssert
              (tree_rep (Some child)
                  (tree_insert query value
                    (Node left_key left_payload
                      left_left left_right)) -∗
                represents header (<[query := value]> m))%I
              with "[REBUILD NODE RIGHT]" as "REBUILD'".
            { iIntros "LEFT".
              iApply "REBUILD".
              simpl. iExists node', (Some child), right_root'.
              iFrame. done. }
            iPoseProof
              (IHl child with "[$AUTH $MAP $REST]") as "IH".
            iSpecialize ("IH" with "REBUILD'").
            iApply "IH". iExact "LEFT". }
        * assert (CMP : Nat.compare query key = Gt).
          { apply Nat.compare_gt_iff. done. }
          cStepsT. rewrite CMP. cStepsT.
          destruct right_tree as
            [|right_key right_payload right_left right_right].
          { iDestruct "RIGHT" as %->.
            cStepsT. cInlineT. cStepsT.
            cForceT tt. cForceT (tt↑). cForceT.
            iSplitR; first done.
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as (fresh) "[-> FRESH]".
            cSimpl. cStepsT. cInlineT. cStepsT.
            cForceT
              (fresh, Vundef,
                MapI.node_val query (Some value) None None).
            cForceT
              ((fresh,
                MapI.node_val query (Some value) None None)↑).
            cForceT.
            iSplitL "FRESH"; first (iFrame; done).
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as "[-> FRESH]".
            cSimpl. cStepsT. cInlineT. cStepsT.
            cForceT
              (node',
                MapI.node_val key (Some old_value)
                  left_root' None,
                MapI.node_val key (Some old_value)
                  left_root' (Some fresh)).
            cForceT
              ((node',
                MapI.node_val key (Some old_value)
                  left_root' (Some fresh))↑).
            cForceT.
            iSplitL "NODE"; first (iFrame; done).
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as "[-> NODE]".
            cSimpl. cStepsT.
            iAssert
              (tree_rep (Some node')
                (Node key (Some old_value) left_tree
                  (Node query (Some value) Leaf Leaf)))%I
              with "[NODE LEFT FRESH]" as "TREE".
            { simpl.
              iExists node', left_root', (Some fresh). iFrame.
              done. }
            iSpecialize ("REBUILD" with "TREE").
            iMod
              (ghost_map_update (<[query := value]> m)
                with "AUTH MAP") as "[AUTH MAP]".
            cForceS (tt↑). cStepsS. cForcesS.
            iSplitL "MAP".
            { iSplitR "MAP"; first done.
              iSplitR "MAP"; first done.
              iExact "MAP". }
            cStep.
            rewrite /ist_with_eq /Ist.
            iSplit; first done.
            iSplit; first done.
            iExists
              (<[header := <[query := value]> m]> models).
            iFrame.
            rewrite <- insert_delete_insert.
            rewrite big_sepM_insert; last apply lookup_delete.
            iFrame. }
          { iDestruct "RIGHT" as
              (child child_left child_right)
              "(%ROOT & CHILD & CHILD_LEFT & CHILD_RIGHT)".
            simplify_eq.
            cStepsT.
            iAssert
              (tree_rep (Some child)
                (Node right_key right_payload
                  right_left right_right))%I
              with "[CHILD CHILD_LEFT CHILD_RIGHT]" as "RIGHT".
            { simpl. iExists child, child_left, child_right.
              iFrame. done. }
            iAssert
              (tree_rep (Some child)
                  (tree_insert query value
                    (Node right_key right_payload
                      right_left right_right)) -∗
                represents header (<[query := value]> m))%I
              with "[REBUILD NODE LEFT]" as "REBUILD'".
            { iIntros "RIGHT".
              iApply "REBUILD".
              simpl. iExists node', left_root', (Some child).
              iFrame. done. }
            iPoseProof
              (IHr child with "[$AUTH $MAP $REST]") as "IH".
            iSpecialize ("IH" with "REBUILD'").
            iApply "IH". iExact "RIGHT". }
        * cStepsT. rewrite Nat.compare_refl. cStepsT.
          cInlineT. cStepsT.
          cForceT
            (node',
              MapI.node_val key None left_root' right_root',
              MapI.node_val key (Some value)
                left_root' right_root').
          cForceT
            ((node',
              MapI.node_val key (Some value)
                left_root' right_root')↑).
          cForceT.
          iSplitL "NODE"; first (iFrame; done).
          cStepsT.
          iDestruct "GRT" as "[-> GRT]".
          iDestruct "GRT" as "[-> NODE]".
          cSimpl. cStepsT.
          iAssert
            (tree_rep (Some node')
              (Node key (Some value) left_tree right_tree))%I
            with "[NODE LEFT RIGHT]" as "TREE".
          { simpl. iExists node', left_root', right_root'.
            iFrame. done. }
          iSpecialize ("REBUILD" with "TREE").
          iMod
            (ghost_map_update (<[key := value]> m) with "AUTH MAP")
            as "[AUTH MAP]".
          cForceS (tt↑). cStepsS. cForcesS.
          iSplitL "MAP".
          { iSplitR "MAP"; first done.
            iSplitR "MAP"; first done.
            iExact "MAP". }
          cStep.
          rewrite /ist_with_eq /Ist.
          iSplit; first done.
          iSplit; first done.
          iExists (<[header := <[key := value]> m]> models).
          iFrame.
          rewrite <- insert_delete_insert.
          rewrite big_sepM_insert; last apply lookup_delete.
          iFrame.
        * assert (CMP : Nat.compare query key = Lt).
          { apply Nat.compare_lt_iff. done. }
          cStepsT. rewrite CMP. cStepsT.
          destruct left_tree as
            [|left_key left_payload left_left left_right].
          { iDestruct "LEFT" as %->.
            cStepsT. cInlineT. cStepsT.
            cForceT tt. cForceT (tt↑). cForceT.
            iSplitR; first done.
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as (fresh) "[-> FRESH]".
            cSimpl. cStepsT. cInlineT. cStepsT.
            cForceT
              (fresh, Vundef,
                MapI.node_val query (Some value) None None).
            cForceT
              ((fresh,
                MapI.node_val query (Some value) None None)↑).
            cForceT.
            iSplitL "FRESH"; first (iFrame; done).
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as "[-> FRESH]".
            cSimpl. cStepsT. cInlineT. cStepsT.
            cForceT
              (node',
                MapI.node_val key None None right_root',
                MapI.node_val key None
                  (Some fresh) right_root').
            cForceT
              ((node',
                MapI.node_val key None
                  (Some fresh) right_root')↑).
            cForceT.
            iSplitL "NODE"; first (iFrame; done).
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as "[-> NODE]".
            cSimpl. cStepsT.
            iAssert
              (tree_rep (Some node')
                (Node key None
                  (Node query (Some value) Leaf Leaf)
                  right_tree))%I
              with "[NODE FRESH RIGHT]" as "TREE".
            { simpl.
              iExists node', (Some fresh), right_root'. iFrame.
              done. }
            iSpecialize ("REBUILD" with "TREE").
            iMod
              (ghost_map_update (<[query := value]> m)
                with "AUTH MAP") as "[AUTH MAP]".
            cForceS (tt↑). cStepsS. cForcesS.
            iSplitL "MAP".
            { iSplitR "MAP"; first done.
              iSplitR "MAP"; first done.
              iExact "MAP". }
            cStep.
            rewrite /ist_with_eq /Ist.
            iSplit; first done.
            iSplit; first done.
            iExists
              (<[header := <[query := value]> m]> models).
            iFrame.
            rewrite <- insert_delete_insert.
            rewrite big_sepM_insert; last apply lookup_delete.
            iFrame. }
          { iDestruct "LEFT" as
              (child child_left child_right)
              "(%ROOT & CHILD & CHILD_LEFT & CHILD_RIGHT)".
            simplify_eq.
            cStepsT.
            iAssert
              (tree_rep (Some child)
                (Node left_key left_payload left_left left_right))%I
              with "[CHILD CHILD_LEFT CHILD_RIGHT]" as "LEFT".
            { simpl. iExists child, child_left, child_right.
              iFrame. done. }
            iAssert
              (tree_rep (Some child)
                  (tree_insert query value
                    (Node left_key left_payload
                      left_left left_right)) -∗
                represents header (<[query := value]> m))%I
              with "[REBUILD NODE RIGHT]" as "REBUILD'".
            { iIntros "LEFT".
              iApply "REBUILD".
              simpl. iExists node', (Some child), right_root'.
              iFrame. done. }
            iPoseProof
              (IHl child with "[$AUTH $MAP $REST]") as "IH".
            iSpecialize ("IH" with "REBUILD'").
            iApply "IH". iExact "LEFT". }
        * assert (CMP : Nat.compare query key = Gt).
          { apply Nat.compare_gt_iff. done. }
          cStepsT. rewrite CMP. cStepsT.
          destruct right_tree as
            [|right_key right_payload right_left right_right].
          { iDestruct "RIGHT" as %->.
            cStepsT. cInlineT. cStepsT.
            cForceT tt. cForceT (tt↑). cForceT.
            iSplitR; first done.
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as (fresh) "[-> FRESH]".
            cSimpl. cStepsT. cInlineT. cStepsT.
            cForceT
              (fresh, Vundef,
                MapI.node_val query (Some value) None None).
            cForceT
              ((fresh,
                MapI.node_val query (Some value) None None)↑).
            cForceT.
            iSplitL "FRESH"; first (iFrame; done).
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as "[-> FRESH]".
            cSimpl. cStepsT. cInlineT. cStepsT.
            cForceT
              (node',
                MapI.node_val key None left_root' None,
                MapI.node_val key None
                  left_root' (Some fresh)).
            cForceT
              ((node',
                MapI.node_val key None
                  left_root' (Some fresh))↑).
            cForceT.
            iSplitL "NODE"; first (iFrame; done).
            cStepsT.
            iDestruct "GRT" as "[-> GRT]".
            iDestruct "GRT" as "[-> NODE]".
            cSimpl. cStepsT.
            iAssert
              (tree_rep (Some node')
                (Node key None left_tree
                  (Node query (Some value) Leaf Leaf)))%I
              with "[NODE LEFT FRESH]" as "TREE".
            { simpl.
              iExists node', left_root', (Some fresh). iFrame.
              done. }
            iSpecialize ("REBUILD" with "TREE").
            iMod
              (ghost_map_update (<[query := value]> m)
                with "AUTH MAP") as "[AUTH MAP]".
            cForceS (tt↑). cStepsS. cForcesS.
            iSplitL "MAP".
            { iSplitR "MAP"; first done.
              iSplitR "MAP"; first done.
              iExact "MAP". }
            cStep.
            rewrite /ist_with_eq /Ist.
            iSplit; first done.
            iSplit; first done.
            iExists
              (<[header := <[query := value]> m]> models).
            iFrame.
            rewrite <- insert_delete_insert.
            rewrite big_sepM_insert; last apply lookup_delete.
            iFrame. }
          { iDestruct "RIGHT" as
              (child child_left child_right)
              "(%ROOT & CHILD & CHILD_LEFT & CHILD_RIGHT)".
            simplify_eq.
            cStepsT.
            iAssert
              (tree_rep (Some child)
                (Node right_key right_payload
                  right_left right_right))%I
              with "[CHILD CHILD_LEFT CHILD_RIGHT]" as "RIGHT".
            { simpl. iExists child, child_left, child_right.
              iFrame. done. }
            iAssert
              (tree_rep (Some child)
                  (tree_insert query value
                    (Node right_key right_payload
                      right_left right_right)) -∗
                represents header (<[query := value]> m))%I
              with "[REBUILD NODE LEFT]" as "REBUILD'".
            { iIntros "RIGHT".
              iApply "REBUILD".
              simpl. iExists node', left_root', (Some child).
              iFrame. done. }
            iPoseProof
              (IHr child with "[$AUTH $MAP $REST]") as "IH".
            iSpecialize ("IH" with "REBUILD'").
            iApply "IH". iExact "RIGHT". }
  Qed.

  Lemma sim :
    ISim.t open MapAMod MapIMod MapA.auth_init Ist.
  Proof.
    cStartModSim.
    - vm_compute.
      apply submseteq_skip, submseteq_cons, submseteq_nil.
    - iIntros "AUTH".
      rewrite /Ist /MapA.auth_init.
      iSplit; first done.
      iExists (∅ : gmap loc amap). iFrame. done.
    - apply simF_new_map.
    - apply simF_insert.
    - apply simF_delete.
    - apply simF_get.
  Qed.

End MapIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS, !memGS}.

  Lemma ctxr
      (sp_map sp_mem : specmap)
      (MAP_IN_SP : MapA.sp ⊆ sp_map) :
    MapA.auth_init ⊢ ctx_refines
      (MapI.t ★ MemA.t sp_mem)
      (MapA.t sp_map).
  Proof.
    eapply main_adequacy, sim; eauto.
  Qed.
End contextual_refinement. End MapIA.
