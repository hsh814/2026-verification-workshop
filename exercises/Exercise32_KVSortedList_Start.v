From CRIS Require Import CRIS.
From Stdlib Require Import Sorting.Sorted Lia.
From Workshop Require Import KVSource SortedListTarget KVSortedListProof.

Set Implicit Arguments.

Module KVSortedListExercises. Section Exercises.
  Import KVSource SortedListTarget.

  (** This is the relation agreed on before the break.  The target list is a
      mathematical value in module-local state, not a heap-linked structure. *)
  Definition ExerciseStateRel (m : amap) (xs : entries) : Prop :=
    sorted_keys xs /\ forall k, m k = list_get k xs.

  (** Pure list induction is supplied.  Students use these two facts but do
      not have to reprove them during the simulation block. *)
  Lemma exercise_state_rel_empty :
    ExerciseStateRel empty_map [].
  Proof. exact KVSortedListProof.state_rel_empty. Qed.

  Lemma exercise_state_rel_put m xs k v :
    ExerciseStateRel m xs ->
    ExerciseStateRel (map_put m k v) (list_put k v xs).
  Proof.
    intros Hrel.
    apply (KVSortedListProof.state_rel_put (m := m) (xs := xs)); exact Hrel.
  Qed.

  Section Refinement.
    Context `{!crisG Γ Σ α β τ _S _I}.

    Definition ExerciseIstLocal : ist_type Σ :=
      fun st_src st_tgt =>
        (∃ m xs,
          ⌜st_src = {[KVSource.v_map # m↑]} /\
           st_tgt = {[SortedListTarget.v_entries # xs↑]} /\
           ExerciseStateRel m xs⌝)%I.

    Local Definition Source := KVSource.t.
    Local Definition Target := SortedListTarget.t.

    Definition ExerciseIst : ist_type Σ :=
      IstProd (IstSB Source.(Mod.scopes) ExerciseIstLocal) IstEq.

    (** Exercise 6 ([get]).  After reading both local states, instantiate the
        pointwise part of [ExerciseStateRel] at [k].  Then match the returns
        and rebuild the unchanged state relation. *)
    Lemma exercise_simF_get :
      ISim.sim_fun open Source Target ExerciseIst (fid KVHdr.get).
    Proof.
      cStartFunSim. rewrite /KVSource.get /SortedListTarget.get.
      cStepsS.
      destruct (Any.downcast arg) as [k|] eqn:Harg; cStepsS; [|done].
      cStepsT.
      iDestruct "IST" as (? ? ? ?) "%". des. cSimpl.
      cStepsS. cStepsT.
      (* TODO: use the lookup equality in the relation at [k], match [Ret],
         and restore [ExerciseIst] with the same map and list. *)
    Abort.

    (** Exercise 7 ([put]).  Use [exercise_state_rel_put] for the updated map
        and list, then choose those updated states when rebuilding the
        simulation invariant. *)
    Lemma exercise_simF_put :
      ISim.sim_fun open Source Target ExerciseIst (fid KVHdr.put).
    Proof.
      cStartFunSim. rewrite /KVSource.put /SortedListTarget.put.
      cStepsS.
      destruct (Any.downcast arg) as [[k v]|] eqn:Harg; cStepsS; [|done].
      cStepsT.
      iDestruct "IST" as (? ? ? ?) "%". des. cSimpl.
      cStepsS. cStepsT.
      (* TODO: derive the updated relation, match [Ret tt], and rebuild
         [ExerciseIst] with [map_put] and [list_put]. *)
    Abort.

    (** Stretch exercise: the initial-state branch is boilerplate and is
        supplied.  The remaining two branches apply the function simulations. *)
    Lemma exercise_module_sim :
      ISim.t open Source Target emp%I ExerciseIst.
    Proof.
      cStartModSim.
      - rewrite /ExerciseIst /Source /Target. unfold_mod.
        iIntros "_".
        rewrite /IstProd /IstSB /ExerciseIstLocal /IstEq.
        iExists {[KVSource.v_map # KVSource.empty_map↑]},
          {[SortedListTarget.v_entries # ([] : entries)↑]}, ∅, ∅.
        iSplit; [iPureIntro; split; ss |].
        iSplit.
        + iSplit; [iPureIntro; split; set_solver |].
          iExists KVSource.empty_map, ([] : entries).
          iPureIntro. repeat split; try reflexivity.
          apply exercise_state_rel_empty.
        + iPureIntro. reflexivity.
      (* TODO: apply [exercise_simF_get] and [exercise_simF_put]. *)
    Abort.

    (** Stretch exercise: remember that adequacy presents target first. *)
    Lemma exercise_contextual_refinement :
      ctx_refines (Target, emp%I) (Source, emp%I).
    Proof.
      (* TODO after [exercise_module_sim]: [eapply main_adequacy, ...]. *)
    Abort.
  End Refinement.
End Exercises. End KVSortedListExercises.
