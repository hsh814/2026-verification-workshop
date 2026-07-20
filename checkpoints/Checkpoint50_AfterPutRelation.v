From CRIS Require Import CRIS.
From Stdlib Require Import Sorting.Sorted Lia.
From Workshop Require Import KVSource SortedListTarget KVSortedListProof.

Set Implicit Arguments.

Module AfterPutRelationCheckpoint. Section Checkpoint.
  Import KVSource SortedListTarget.

  Definition CheckpointStateRel (m : amap) (xs : entries) : Prop :=
    sorted_keys xs /\ forall k, m k = list_get k xs.

  Lemma checkpoint_state_rel_put m xs k v :
    CheckpointStateRel m xs ->
    CheckpointStateRel (map_put m k v) (list_put k v xs).
  Proof.
    intros Hrel.
    apply (KVSortedListProof.state_rel_put (m := m) (xs := xs)); exact Hrel.
  Qed.

  Section Refinement.
    Context `{!crisG Γ Σ α β τ _S _I}.

    Definition CheckpointIstLocal : ist_type Σ :=
      fun st_src st_tgt =>
        (∃ m xs,
          ⌜st_src = {[KVSource.v_map # m↑]} /\
           st_tgt = {[SortedListTarget.v_entries # xs↑]} /\
           CheckpointStateRel m xs⌝)%I.

    Local Definition Source := KVSource.t.
    Local Definition Target := SortedListTarget.t.

    Definition CheckpointIst : ist_type Σ :=
      IstProd (IstSB Source.(Mod.scopes) CheckpointIstLocal) IstEq.

    Lemma checkpoint_simF_get :
      ISim.sim_fun open Source Target CheckpointIst (fid KVHdr.get).
    Proof.
      cStartFunSim. rewrite /KVSource.get /SortedListTarget.get.
      cStepsS.
      destruct (Any.downcast arg) as [k|] eqn:Harg; cStepsS; [|done].
      cStepsT.
      iDestruct "IST" as (? ? ? ?) "%". des. cSimpl.
      cStepsS. cStepsT.
      destruct H4 as [Hsorted Hlookup]. rewrite Hlookup.
      cStep. iSplit; [eauto |].
      iPureIntro. repeat (esplits; eauto).
      split; assumption.
    Qed.

    (** Checkpoint: the hard pure step for [put] is already in [Hrel].  Match
        the returns and use that witness to rebuild the updated invariant. *)
    Lemma checkpoint_exercise_simF_put :
      ISim.sim_fun open Source Target CheckpointIst (fid KVHdr.put).
    Proof.
      cStartFunSim. rewrite /KVSource.put /SortedListTarget.put.
      cStepsS.
      destruct (Any.downcast arg) as [[k v]|] eqn:Harg; cStepsS; [|done].
      cStepsT.
      iDestruct "IST" as (? ? ? ?) "%". des. cSimpl.
      cStepsS. cStepsT.
      pose proof (checkpoint_state_rel_put (m := x) (xs := x0) k v H4)
        as Hrel.
      (* TODO: match [Ret tt] and rebuild [CheckpointIst] with [Hrel]. *)
    Abort.
  End Refinement.
End Checkpoint. End AfterPutRelationCheckpoint.
