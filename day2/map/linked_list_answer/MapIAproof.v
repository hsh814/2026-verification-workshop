(** * Proof that the Linked-List Map Refines [MapA] *)

From CRIS.common Require Import CRIS.
From CRIS.scheduler Require Import Atomic.
From CRIS.iris_system.lib Require Import ghost_map.
From mem_answer Require Import MemA.
From map.linked_list_answer Require Import MapA MapI.

(** The concrete list remembers deleted keys.  A historical entry carries
    [None] exactly when its node contains the [Vundef] tombstone. *)
Definition map_entry : Type := (nat * option nat)%type.

Definition entry_keys (entries : list map_entry) : list nat :=
  fst <$> entries.

Fixpoint entries_lookup
    (key : nat) (entries : list map_entry) : option nat :=
  match entries with
  | [] => None
  | (key', value) :: entries' =>
      if Nat.eq_dec key key'
      then value
      else entries_lookup key entries'
  end.

Fixpoint update_entry
    (key : nat) (value : option nat) (entries : list map_entry) :
    list map_entry :=
  match entries with
  | [] => []
  | (key', value') :: entries' =>
      if Nat.eq_dec key key'
      then (key', value) :: entries'
      else (key', value') :: update_entry key value entries'
  end.

Definition insert_entries
    (key value : nat) (entries : list map_entry) : list map_entry :=
  if decide (key ∈ entry_keys entries)
  then update_entry key (Some value) entries
  else (key, Some value) :: entries.

Definition delete_entries
    (key : nat) (entries : list map_entry) : list map_entry :=
  update_entry key None entries.

Definition entries_model
    (entries : list map_entry) (model : gmap nat nat) : Prop :=
  ∀ key, model !! key = entries_lookup key entries.

Lemma entries_lookup_not_in key entries :
  key ∉ entry_keys entries →
  entries_lookup key entries = None.
Proof.
  induction entries as [|[key' value] entries IH]; simpl.
  - done.
  - intros NOTIN.
    apply not_elem_of_cons in NOTIN as [NE NOTIN].
    destruct (Nat.eq_dec key key'); [congruence |].
    apply IH. exact NOTIN.
Qed.

Lemma entry_keys_update key value entries :
  entry_keys (update_entry key value entries) = entry_keys entries.
Proof.
  induction entries as [|[key' value'] entries IH]; simpl.
  - done.
  - destruct (Nat.eq_dec key key'); simpl; [done |].
    by rewrite IH.
Qed.

Lemma update_entry_not_in key value entries :
  key ∉ entry_keys entries →
  update_entry key value entries = entries.
Proof.
  induction entries as [|[key' value'] entries IH]; simpl.
  - done.
  - intros NOTIN.
    apply not_elem_of_cons in NOTIN as [NE NOTIN].
    destruct (Nat.eq_dec key key'); [congruence |].
    f_equal. apply IH. exact NOTIN.
Qed.

Lemma entries_lookup_update_same key value entries :
  key ∈ entry_keys entries →
  entries_lookup key (update_entry key value entries) = value.
Proof.
  induction entries as [|[key' value'] entries IH]; simpl.
  - set_solver.
  - intros IN.
    destruct (Nat.eq_dec key key') as [->|NE].
    + simpl. destruct (Nat.eq_dec key' key'); congruence.
    + simpl. destruct (Nat.eq_dec key key'); [congruence |].
      apply IH. apply elem_of_cons in IN as [EQ|IN]; [congruence | done].
Qed.

Lemma entries_lookup_update_ne query key value entries :
  query ≠ key →
  entries_lookup query (update_entry key value entries) =
    entries_lookup query entries.
Proof.
  induction entries as [|[key' value'] entries IH]; simpl.
  - done.
  - intros NEQ.
    destruct (Nat.eq_dec key key') as [EQ|NE].
    + subst key'.
      simpl. destruct (Nat.eq_dec query key); [congruence | done].
    + simpl. destruct (Nat.eq_dec query key'); [done |].
      apply IH. exact NEQ.
Qed.

Lemma NoDup_insert_entries key value entries :
  NoDup (entry_keys entries) →
  NoDup (entry_keys (insert_entries key value entries)).
Proof.
  intros NODUP. rewrite /insert_entries.
  destruct (decide (key ∈ entry_keys entries)).
  - by rewrite entry_keys_update.
  - simpl. constructor; done.
Qed.

Lemma NoDup_delete_entries key entries :
  NoDup (entry_keys entries) →
  NoDup (entry_keys (delete_entries key entries)).
Proof. rewrite /delete_entries entry_keys_update. done. Qed.

Lemma entries_lookup_insert_same key value entries :
  entries_lookup key (insert_entries key value entries) = Some value.
Proof.
  rewrite /insert_entries.
  destruct (decide (key ∈ entry_keys entries)) as [IN|NOTIN].
  - apply entries_lookup_update_same. exact IN.
  - simpl. destruct (Nat.eq_dec key key); congruence.
Qed.

Lemma entries_lookup_insert_ne query key value entries :
  query ≠ key →
  entries_lookup query (insert_entries key value entries) =
    entries_lookup query entries.
Proof.
  intros NE. rewrite /insert_entries.
  destruct (decide (key ∈ entry_keys entries)).
  - apply entries_lookup_update_ne. exact NE.
  - simpl. destruct (Nat.eq_dec query key); congruence.
Qed.

Lemma entries_lookup_delete_same key entries :
  entries_lookup key (delete_entries key entries) = None.
Proof.
  rewrite /delete_entries.
  destruct (decide (key ∈ entry_keys entries)) as [IN|NOTIN].
  - apply entries_lookup_update_same. exact IN.
  - rewrite update_entry_not_in; [|exact NOTIN].
    apply entries_lookup_not_in. exact NOTIN.
Qed.

Lemma entries_lookup_delete_ne query key entries :
  query ≠ key →
  entries_lookup query (delete_entries key entries) =
    entries_lookup query entries.
Proof. apply entries_lookup_update_ne. Qed.

Lemma entries_model_insert entries model key value :
  entries_model entries model →
  entries_model
    (insert_entries key value entries) (<[key := value]> model).
Proof.
  intros MODEL query. destruct (Nat.eq_dec query key) as [->|NE].
  - rewrite lookup_insert entries_lookup_insert_same //.
  - rewrite lookup_insert_ne; [|congruence].
    rewrite MODEL. symmetry. apply entries_lookup_insert_ne. exact NE.
Qed.

Lemma entries_model_delete entries model key :
  entries_model entries model →
  entries_model (delete_entries key entries) (delete key model).
Proof.
  intros MODEL query. destruct (Nat.eq_dec query key) as [->|NE].
  - rewrite lookup_delete entries_lookup_delete_same //.
  - rewrite lookup_delete_ne; [|congruence].
    rewrite MODEL. symmetry. apply entries_lookup_delete_ne. exact NE.
Qed.

Section representation.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Fixpoint linked_nodes
      (head : option loc) (entries : list map_entry) : iProp Σ :=
    match entries with
    | [] => ⌜head = None⌝
    | (key, value) :: entries' =>
        ∃ node next,
          ⌜head = Some node⌝ ∗
          node ↦ MapI.node_contents key value next ∗
          linked_nodes next entries'
    end%I.

  Definition map_rep
      (handle : loc) (model : gmap nat nat) : iProp Σ :=
    (∃ head entries,
      handle ↦ Vloc head ∗
      linked_nodes head entries ∗
      ⌜NoDup (entry_keys entries) ∧ entries_model entries model⌝)%I.
End representation.

Module MapIA. Section MapIA.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS, !memGS}.
  Local Existing Instances mapGS_pre map_modelG.

  Context (sp_map sp_mem : specmap).
  Context (MAP_IN_SP : MapA.sp ⊆ sp_map).

  Local Definition MapAMod := MapA.t sp_map.
  Local Definition MapIMod := MapI.t ★ MemA.t sp_mem.

  Definition representations
      (models : gmap loc (gmap nat nat)) : iProp Σ :=
    ([∗ map] handle ↦ model ∈ models, map_rep handle model)%I.

  Lemma representations_insert models handle model :
    models !! handle = None →
    representations models -∗
    map_rep handle model -∗
    representations (<[handle := model]> models).
  Proof.
    intros FRESH. rewrite /representations big_sepM_insert //.
    iIntros "REPS REP". iFrame.
  Qed.

  Lemma representations_update models handle old_model new_model :
    models !! handle = Some old_model →
    representations models -∗
    map_rep handle new_model -∗
    representations (<[handle := new_model]> models).
  Proof.
    intros HIT. rewrite /representations.
    iIntros "REPS REP".
    iDestruct (big_sepM_delete _ _ _ _ HIT with "REPS")
      as "[_ REPS]".
    rewrite -insert_delete_insert big_sepM_insert; last apply lookup_delete.
    iFrame.
  Qed.

  Lemma representations_reinsert models handle old_model new_model :
    models !! handle = Some old_model →
    ([∗ map] h ↦ model ∈ delete handle models, map_rep h model) -∗
    map_rep handle new_model -∗
    representations (<[handle := new_model]> models).
  Proof.
    intros HIT. rewrite /representations.
    iIntros "REPS REP".
    rewrite -insert_delete_insert big_sepM_insert; last apply lookup_delete.
    iFrame.
  Qed.

  Lemma representations_fresh models handle value :
    handle ↦ value -∗
    representations models -∗
    ⌜models !! handle = None⌝.
  Proof.
    iIntros "HEADER REPS".
    destruct (models !! handle) as [old_model|] eqn:HIT; [|done].
    iDestruct (big_sepM_delete _ _ _ _ HIT with "REPS")
      as "[OLD _]".
    iDestruct "OLD" as (old_head old_entries)
      "(OLD_HEADER & _ & _)".
    iEval (rewrite /pointsto) in "HEADER OLD_HEADER".
    iPoseProof (ghost_map_elem_ne mem_map_name
      with "HEADER OLD_HEADER") as "%NE".
    done.
  Qed.

  Definition Ist : ist_type Σ :=
    (λ st_src st_tgt,
      ∃ models,
        ⌜st_src = ∅ ∧ st_tgt = ∅⌝ ∗
        map_auth models ∗
        representations models)%I.

  Lemma simF_new_map :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.new_map).
  Proof.
    cStartFunSim.
    rewrite /MapI.new_map.
    cStepsT. cStepsS.
    iDestruct "ASM" as "[-> ->]".
    cStepsT. cInlineT. cStepsT.
    cForceT tt. cForceT (tt↑). cForceT.
    iSplitR; first done.
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as (header) "[-> HEADER]".
    cSimpl. cStepsT. cInlineT. cStepsT.
    cForceT (header, Vundef, Vloc None).
    cForceT ((header, Vloc None)↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    iDestruct "IST" as (models) "(%ST & AUTH & REPS)".
    destruct ST as [-> ->].
    iPoseProof
      (representations_fresh models header (Vloc None)
        with "HEADER REPS") as "%FRESH".
    iEval (rewrite /map_auth) in "AUTH".
    iMod (ghost_map_insert header (∅ : gmap nat nat) with "AUTH")
      as "[AUTH MAP]"; first exact FRESH.
    iAssert (map_rep header (∅ : gmap nat nat))
      with "[HEADER]" as "REP".
    { iExists None, []. iFrame.
      iPureIntro. rewrite /entry_keys /entries_model /=.
      split; [reflexivity |].
      split; [constructor |].
      intros key. apply lookup_empty. }
    iPoseProof
      (representations_insert models header (∅ : gmap nat nat) FRESH
        with "REPS REP") as "REPS".
    cSimpl. cStepsT.
    cForceS (header↑). cStepsS. cForcesS.
    iSplitL "MAP".
    { iSplitR "MAP"; first done.
      iExists header. iSplitR "MAP"; first done.
      rewrite /is_map. iExact "MAP". }
    cStep.
    rewrite /ist_with_eq /Ist.
    iSplitR "AUTH REPS"; first done.
    iExists (<[header := (∅ : gmap nat nat)]> models).
    iSplitR "AUTH REPS"; first done.
    iFrame.
  Qed.

  Lemma simF_insert :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.insert).
  Proof.
    cStartFunSim.
    rewrite /MapI.insert.
    cStepsT. cStepsS.
    cStepsT. cStepsS.
    destruct _q as [[[handle model] key] value].
    iDestruct "ASM" as "[-> [-> MAP]]".
    iDestruct "IST" as (models) "(%ST & AUTH & REPS)".
    destruct ST as [-> ->].
    iEval (rewrite /map_auth) in "AUTH".
    iEval (rewrite /is_map) in "MAP".
    iPoseProof (ghost_map_lookup with "AUTH MAP") as "%HIT".
    iDestruct (big_sepM_delete _ _ _ _ HIT with "REPS")
      as "[REP REST]".
    iDestruct "REP" as (head entries)
      "(HEADER & NODES & %PURE)".
    destruct PURE as [NODUP MODEL].
    cStepsT. cInlineT. cStepsT.
    cForceT (handle, Vloc head).
    cForceT (handle↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl.
    cStepsT.
    rewrite /MapI.find.
    rename head into original_head.
    rename entries into all_entries.
    pose (root := original_head).
    iAssert (handle ↦ (Vloc root))%I with "[HEADER]" as "HEADER".
    { subst root. iExact "HEADER". }
    pose (cursor := original_head).
    pose (suffix := all_entries).
    iAssert (linked_nodes cursor suffix)
      with "[NODES]" as "NODES".
    { subst cursor suffix. iExact "NODES". }
    iAssert
      (handle ↦ (Vloc root) ∗
       ((linked_nodes cursor suffix -∗
         linked_nodes root all_entries) ∧
        (linked_nodes cursor
           (update_entry key (Some value) suffix) -∗
         linked_nodes root
           (update_entry key (Some value) all_entries))))%I
      with "[HEADER]" as "FRAME".
    { iFrame. iSplit; iIntros "NODES";
        subst root cursor suffix; iExact "NODES". }
    iAssert
      (⌜key ∈ entry_keys all_entries ↔
         key ∈ entry_keys suffix⌝)%I
      with "[]" as "KEYS".
    { iPureIntro. subst suffix. reflexivity. }
    change original_head with root at 2.
    fold cursor.
    clearbody cursor suffix.
    iInduction suffix as [|[stored_key stored_value] tail] "IH"
      forall (cursor) "NODES FRAME KEYS".
    - iDestruct "NODES" as %->.
      iDestruct "KEYS" as %KEYS.
      iDestruct "FRAME" as "[HEADER FRAME]".
      iDestruct "FRAME" as "[KEEP _]".
      aUnfoldT.
      assert (NOTIN : key ∉ entry_keys all_entries).
      { intros IN. apply KEYS in IN. inversion IN. }
      iAssert (linked_nodes root all_entries)
        with "[KEEP]" as "OLD_NODES".
      { iApply "KEEP". done. }
      cStepsT. cInlineT. cStepsT.
      cForceT tt. cForceT (tt↑). cForceT.
      iSplitR; first done.
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as (node) "[-> NODE]".
      cSimpl. cStepsT. cInlineT. cStepsT.
      cForceT
        (node, Vundef,
          MapI.node_contents key (Some value) root).
      cForceT
        ((node, MapI.node_contents key (Some value) root)↑).
      cForceT.
      iSplitL "NODE"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> NODE]".
      cSimpl. cStepsT. cInlineT. cStepsT.
      cForceT
        (handle, Vloc root, Vloc (Some node)).
      cForceT ((handle, Vloc (Some node))↑). cForceT.
      iSplitL "HEADER"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> HEADER]".
      cSimpl. cStepsT.
      iAssert
        (linked_nodes (Some node)
          (insert_entries key value all_entries))
        with "[NODE OLD_NODES]" as "NEW_NODES".
      { rewrite /insert_entries decide_False; last exact NOTIN.
        simpl. iExists node, root.
        iSplitR; first done.
        iFrame "NODE".
        iExact "OLD_NODES". }
      iAssert
        (map_rep handle (<[key := value]> model))
        with "[HEADER NEW_NODES]" as "REP".
      { iExists (Some node), (insert_entries key value all_entries).
        iFrame. iPureIntro. split.
        - apply NoDup_insert_entries. exact NODUP.
        - apply entries_model_insert. exact MODEL. }
      iMod
        (ghost_map_update (<[key := value]> model)
          with "AUTH MAP") as "[AUTH MAP]".
      iPoseProof
        (representations_reinsert models handle model
          (<[key := value]> model) HIT
          with "REST REP") as "REPS".
      cForceS (tt↑). cStepsS. cForcesS.
      iSplitL "MAP".
      { rewrite /is_map. iFrame. done. }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplitR "AUTH REPS"; first done.
      iExists (<[handle := <[key := value]> model]> models).
      iSplitR "AUTH REPS"; first done.
      iFrame.
    - iDestruct "NODES" as (node next)
        "(%CURSOR & NODE & TAIL)".
      subst cursor.
      iDestruct "KEYS" as %KEYS.
      aUnfoldT. simpl.
      cStepsT. cInlineT. cStepsT.
      cForceT
        (node, MapI.node_contents stored_key stored_value next).
      cForceT (node↑). cForceT.
      iSplitL "NODE"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> NODE]".
      cSimpl.
      destruct (Nat.eq_dec key stored_key) as [EQ|NE].
      + subst stored_key.
        iDestruct "FRAME" as "[HEADER FRAME]".
        iDestruct "FRAME" as "[_ UPDATE]".
        cStepsT. case_match; last congruence.
        cStepsT. cInlineT. cStepsT.
        cForceT
          (node, MapI.node_contents key stored_value next,
            MapI.node_contents key (Some value) next).
        cForceT
          ((node, MapI.node_contents key (Some value) next)↑).
        cForceT.
        iSplitL "NODE"; first (iFrame; done).
        cStepsT.
        iDestruct "GRT" as "[-> GRT]".
        iDestruct "GRT" as "[-> NODE]".
        cSimpl. cStepsT.
        assert (IN : key ∈ entry_keys all_entries).
        { apply KEYS0. simpl. left. }
        iAssert
          (linked_nodes root
            (insert_entries key value all_entries))
          with "[UPDATE NODE TAIL]" as "NEW_NODES".
        { rewrite /insert_entries decide_True; last exact IN.
          iApply "UPDATE". simpl. iExists node, next.
          iSplitR; first done. iFrame. }
        iAssert
          (map_rep handle (<[key := value]> model))
          with "[HEADER NEW_NODES]" as "REP".
        { iExists root, (insert_entries key value all_entries).
          iFrame. iPureIntro. split.
          - apply NoDup_insert_entries. exact NODUP.
          - apply entries_model_insert. exact MODEL. }
        iMod
          (ghost_map_update (<[key := value]> model)
            with "AUTH MAP") as "[AUTH MAP]".
        iPoseProof
          (representations_reinsert models handle model
            (<[key := value]> model) HIT
            with "REST REP") as "REPS".
        cForceS (tt↑). cStepsS. cForcesS.
        iSplitL "MAP".
        { rewrite /is_map. iFrame. done. }
        cStep.
        rewrite /ist_with_eq /Ist.
        iSplitR "AUTH REPS"; first done.
        iExists (<[handle := <[key := value]> model]> models).
        iSplitR "AUTH REPS"; first done.
        iFrame.
      + cStepsT. case_match; first congruence.
        cStepT.
        iDestruct "FRAME" as "[HEADER CONTEXT]".
        iAssert
          (handle ↦ (Vloc root) ∗
           ((linked_nodes next tail -∗
             linked_nodes root all_entries) ∧
            (linked_nodes next
               (update_entry key (Some value) tail) -∗
             linked_nodes root
               (update_entry key (Some value) all_entries))))%I
          with "[HEADER CONTEXT NODE]" as "FRAME".
        { iFrame "HEADER". iSplit.
          - iIntros "TAIL".
            iDestruct "CONTEXT" as "[KEEP _]".
            iApply "KEEP". iExists node, next.
            iSplitR; first done. iFrame.
          - iIntros "TAIL".
            iDestruct "CONTEXT" as "[_ UPDATE]".
            iApply "UPDATE". iExists node, next.
            iSplitR; first done. iFrame. }
        iAssert
          (⌜key ∈ entry_keys all_entries ↔
             key ∈ entry_keys tail⌝)%I
          with "[]" as "KEYS'".
        { iPureIntro. split.
          - intros IN. apply KEYS in IN.
            apply elem_of_cons in IN as [EQ|IN];
              [congruence | exact IN].
          - intros IN. apply KEYS0.
            apply elem_of_cons. right. exact IN. }
        iApply
          ("IH" $! next
            with "AUTH MAP REST TAIL FRAME KEYS'").
  Qed.

  Lemma simF_delete :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.delete).
  Proof.
    cStartFunSim.
    rewrite /MapI.delete.
    cStepsT. cStepsS.
    cStepsT. cStepsS.
    destruct _q as [[handle model] key].
    iDestruct "ASM" as "[-> [-> MAP]]".
    iDestruct "IST" as (models) "(%ST & AUTH & REPS)".
    destruct ST as [-> ->].
    iEval (rewrite /map_auth) in "AUTH".
    iEval (rewrite /is_map) in "MAP".
    iPoseProof (ghost_map_lookup with "AUTH MAP") as "%HIT".
    iDestruct (big_sepM_delete _ _ _ _ HIT with "REPS")
      as "[REP REST]".
    iDestruct "REP" as (head entries)
      "(HEADER & NODES & %PURE)".
    destruct PURE as [NODUP MODEL].
    cStepsT. cInlineT. cStepsT.
    cForceT (handle, Vloc head).
    cForceT (handle↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl.
    cStepsT.
    rewrite /MapI.find.
    rename head into original_head.
    rename entries into all_entries.
    pose (root := original_head).
    iAssert (handle ↦ (Vloc root))%I
      with "[HEADER]" as "HEADER".
    { subst root. iExact "HEADER". }
    pose (cursor := original_head).
    pose (suffix := all_entries).
    iAssert (linked_nodes cursor suffix)
      with "[NODES]" as "NODES".
    { subst cursor suffix. iExact "NODES". }
    iAssert
      (handle ↦ (Vloc root) ∗
       (linked_nodes cursor (update_entry key None suffix) -∗
        linked_nodes root
          (update_entry key None all_entries)))%I
      with "[HEADER]" as "FRAME".
    { iFrame. iIntros "NODES".
      subst root cursor suffix. iExact "NODES". }
    fold cursor.
    clearbody cursor suffix.
    iInduction suffix as [|[stored_key stored_value] tail] "IH"
      forall (cursor) "NODES FRAME".
    - iDestruct "NODES" as %->.
      iDestruct "FRAME" as "[HEADER UPDATE]".
      aUnfoldT. cStepsT.
      iAssert
        (linked_nodes root (delete_entries key all_entries))
        with "[UPDATE]" as "NEW_NODES".
      { rewrite /delete_entries. iApply "UPDATE". done. }
      iAssert
        (map_rep handle (delete key model))
        with "[HEADER NEW_NODES]" as "REP".
      { iExists root, (delete_entries key all_entries).
        iFrame. iPureIntro. split.
        - apply NoDup_delete_entries. exact NODUP.
        - apply entries_model_delete. exact MODEL. }
      iMod
        (ghost_map_update (delete key model)
          with "AUTH MAP") as "[AUTH MAP]".
      iPoseProof
        (representations_reinsert models handle model
          (delete key model) HIT
          with "REST REP") as "REPS".
      cForceS (tt↑). cStepsS. cForcesS.
      iSplitL "MAP".
      { rewrite /is_map. iFrame. done. }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplitR "AUTH REPS"; first done.
      iExists (<[handle := delete key model]> models).
      iSplitR "AUTH REPS"; first done.
      iFrame.
    - iDestruct "NODES" as (node next)
        "(%CURSOR & NODE & TAIL)".
      subst cursor.
      aUnfoldT. simpl.
      cStepsT. cInlineT. cStepsT.
      cForceT
        (node, MapI.node_contents stored_key stored_value next).
      cForceT (node↑). cForceT.
      iSplitL "NODE"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> NODE]".
      cSimpl.
      destruct (Nat.eq_dec key stored_key) as [EQ|NE].
      + subst stored_key.
        iDestruct "FRAME" as "[HEADER UPDATE]".
        cStepsT. case_match; last congruence.
        cStepsT. cInlineT. cStepsT.
        cForceT
          (node, MapI.node_contents key stored_value next,
            MapI.node_contents key None next).
        cForceT ((node, MapI.node_contents key None next)↑).
        cForceT.
        iSplitL "NODE"; first (iFrame; done).
        cStepsT.
        iDestruct "GRT" as "[-> GRT]".
        iDestruct "GRT" as "[-> NODE]".
        cSimpl. cStepsT.
        iAssert
          (linked_nodes root (delete_entries key all_entries))
          with "[UPDATE NODE TAIL]" as "NEW_NODES".
        { rewrite /delete_entries. iApply "UPDATE".
          simpl. iExists node, next.
          iSplitR; first done. iFrame. }
        iAssert
          (map_rep handle (delete key model))
          with "[HEADER NEW_NODES]" as "REP".
        { iExists root, (delete_entries key all_entries).
          iFrame. iPureIntro. split.
          - apply NoDup_delete_entries. exact NODUP.
          - apply entries_model_delete. exact MODEL. }
        iMod
          (ghost_map_update (delete key model)
            with "AUTH MAP") as "[AUTH MAP]".
        iPoseProof
          (representations_reinsert models handle model
            (delete key model) HIT
            with "REST REP") as "REPS".
        cForceS (tt↑). cStepsS. cForcesS.
        iSplitL "MAP".
        { rewrite /is_map. iFrame. done. }
        cStep.
        rewrite /ist_with_eq /Ist.
        iSplitR "AUTH REPS"; first done.
        iExists (<[handle := delete key model]> models).
        iSplitR "AUTH REPS"; first done.
        iFrame.
      + cStepsT. case_match; first congruence.
        cStepT.
        iDestruct "FRAME" as "[HEADER UPDATE]".
        iAssert
          (handle ↦ (Vloc root) ∗
           (linked_nodes next (update_entry key None tail) -∗
            linked_nodes root
              (update_entry key None all_entries)))%I
          with "[HEADER UPDATE NODE]" as "FRAME".
        { iFrame "HEADER". iIntros "TAIL".
          iApply "UPDATE". iExists node, next.
          iSplitR; first done. iFrame. }
        iApply
          ("IH" $! next
            with "AUTH MAP REST TAIL FRAME").
  Qed.

  Lemma simF_get :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.get).
  Proof.
    cStartFunSim.
    rewrite /MapI.get.
    cStepsT. cStepsS.
    cStepsT. cStepsS.
    destruct _q as [[handle model] key].
    iDestruct "ASM" as "[-> [-> MAP]]".
    iDestruct "IST" as (models) "(%ST & AUTH & REPS)".
    destruct ST as [-> ->].
    iEval (rewrite /map_auth) in "AUTH".
    iEval (rewrite /is_map) in "MAP".
    iPoseProof (ghost_map_lookup with "AUTH MAP") as "%HIT".
    iDestruct
      (big_sepM_lookup_acc _ models handle model HIT with "REPS")
      as "[REP CLOSE]".
    iDestruct "REP" as (head entries)
      "(HEADER & NODES & %PURE)".
    destruct PURE as [NODUP MODEL].
    cStepsT. cInlineT. cStepsT.
    cForceT (handle, Vloc head).
    cForceT (handle↑). cForceT.
    iSplitL "HEADER"; first (iFrame; done).
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as "[-> HEADER]".
    cSimpl.
    cStepsT.
    rewrite /MapI.find.
    rename head into original_head.
    rename entries into all_entries.
    pose (root := original_head).
    iAssert (handle ↦ (Vloc root))%I
      with "[HEADER]" as "HEADER".
    { subst root. iExact "HEADER". }
    pose (cursor := original_head).
    pose (suffix := all_entries).
    iAssert (linked_nodes cursor suffix)
      with "[NODES]" as "NODES".
    { subst cursor suffix. iExact "NODES". }
    iAssert
      (handle ↦ (Vloc root) ∗
       (linked_nodes cursor suffix -∗
        linked_nodes root all_entries))%I
      with "[HEADER]" as "FRAME".
    { iFrame. iIntros "NODES".
      subst root cursor suffix. iExact "NODES". }
    iAssert
      (⌜entries_lookup key all_entries =
         entries_lookup key suffix⌝)%I
      with "[]" as "LOOKUP".
    { iPureIntro. subst suffix. reflexivity. }
    fold cursor.
    clearbody cursor suffix.
    iInduction suffix as [|[stored_key stored_value] tail] "IH"
      forall (cursor) "NODES FRAME LOOKUP".
    - iDestruct "NODES" as %->.
      iDestruct "FRAME" as "[HEADER KEEP]".
      iDestruct "LOOKUP" as %LOOKUP.
      aUnfoldT. cStepsT.
      iAssert (linked_nodes root all_entries)
        with "[KEEP]" as "NODES".
      { iApply "KEEP". done. }
      assert (RESULT : model !! key = None).
      { rewrite MODEL LOOKUP. reflexivity. }
      iAssert (map_rep handle model)
        with "[HEADER NODES]" as "REP".
      { iExists root, all_entries. iFrame. done. }
      iSpecialize ("CLOSE" with "REP").
      cForceS ((None : option nat)↑). cStepsS. cForcesS.
      iSplitL "MAP".
      { rewrite /is_map. iFrame. rewrite RESULT. done. }
      cStep.
      rewrite /ist_with_eq /Ist.
      iSplitR "AUTH CLOSE"; first done.
      iExists models.
      iSplitR "AUTH CLOSE"; first done.
      iFrame.
    - iDestruct "NODES" as (node next)
        "(%CURSOR & NODE & TAIL)".
      subst cursor.
      iDestruct "LOOKUP" as %LOOKUP.
      aUnfoldT. simpl.
      cStepsT. cInlineT. cStepsT.
      cForceT
        (node, MapI.node_contents stored_key stored_value next).
      cForceT (node↑). cForceT.
      iSplitL "NODE"; first (iFrame; done).
      cStepsT.
      iDestruct "GRT" as "[-> GRT]".
      iDestruct "GRT" as "[-> NODE]".
      cSimpl.
      destruct (Nat.eq_dec key stored_key) as [EQ|NE].
      + subst stored_key.
        cStepsT. case_match; last congruence.
        cStepsT.
        assert (RESULT : model !! key = stored_value).
        { rewrite MODEL LOOKUP. reflexivity. }
        iDestruct "FRAME" as "[HEADER KEEP]".
        iAssert (linked_nodes root all_entries)
          with "[KEEP NODE TAIL]" as "NODES".
        { iApply "KEEP". iExists node, next.
          iSplitR; first done. iFrame. }
        iAssert (map_rep handle model)
          with "[HEADER NODES]" as "REP".
        { iExists root, all_entries. iFrame. done. }
        iSpecialize ("CLOSE" with "REP").
        destruct stored_value as [found_value|].
        * cSimpl. cStepsT.
          cForceS ((Some found_value : option nat)↑).
          cStepsS. cForcesS.
          iSplitL "MAP".
          { rewrite /is_map. iFrame. rewrite RESULT. done. }
          cStep.
          rewrite /ist_with_eq /Ist.
          iSplitR "AUTH CLOSE"; first done.
          iExists models.
          iSplitR "AUTH CLOSE"; first done.
          iFrame.
        * cSimpl. cStepsT.
          cForceS ((None : option nat)↑).
          cStepsS. cForcesS.
          iSplitL "MAP".
          { rewrite /is_map. iFrame. rewrite RESULT. done. }
          cStep.
          rewrite /ist_with_eq /Ist.
          iSplitR "AUTH CLOSE"; first done.
          iExists models.
          iSplitR "AUTH CLOSE"; first done.
          iFrame.
      + cStepsT. case_match; first congruence.
        cStepT.
        iDestruct "FRAME" as "[HEADER KEEP]".
        iAssert
          (handle ↦ (Vloc root) ∗
           (linked_nodes next tail -∗
            linked_nodes root all_entries))%I
          with "[HEADER KEEP NODE]" as "FRAME".
        { iFrame "HEADER". iIntros "TAIL".
          iApply "KEEP". iExists node, next.
          iSplitR; first done. iFrame. }
        iAssert
          (⌜entries_lookup key all_entries =
             entries_lookup key tail⌝)%I
          with "[]" as "LOOKUP'".
        { done. }
        iApply
          ("IH" $! next
            with "AUTH MAP CLOSE TAIL FRAME LOOKUP'").
  Qed.

  Lemma sim :
    ISim.t open MapAMod MapIMod MapA.auth_init Ist.
  Proof.
    cStartModSim.
    - vm_compute.
      apply submseteq_skip, submseteq_cons, submseteq_nil.
    - iIntros "AUTH".
      rewrite /MapA.auth_init /Ist.
      iExists (∅ : gmap loc (gmap nat nat)).
      iSplitR "AUTH"; first done.
      iFrame. rewrite /representations big_sepM_empty. done.
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
