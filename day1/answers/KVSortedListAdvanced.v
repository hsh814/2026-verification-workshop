From CRIS Require Import CRIS Atomic.
From Stdlib Require Import Sorting.Sorted Lia.
From answers Require Import KVSortedList.

(** Optional advanced exercise.

    [KVSortedList.v] used [ITree.iter] for [get] and a pure [list_put] call for
    [put].  This file keeps the same abstract source and representation
    relation.  The target insertion now visits one list cell per iterator
    step.

    The cursor splits the list into a processed prefix and an unprocessed
    suffix:

      (prefix, rest)

    Each [inl] result moves one head element from [rest] to [prefix].
    An [inr] result returns the completed sorted list. *)

Module IterPutTarget. Section IterPutTarget.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Import SortedListTarget.

  Definition put_cursor := (entries * entries)%type.

  Definition put_step (k v : Z)
      (cursor : put_cursor) : itree crisE (put_cursor + entries) :=
    let '(prefix, rest) := cursor in
    match rest with
    | [] =>
        Ret (inr (prefix ++ [(k, v)]))
    | (k', v') :: tl =>
        match Z.compare k k' with
        | Lt =>
            Ret (inr (prefix ++ (k, v) :: rest))
        | Eq =>
            Ret (inr (prefix ++ (k, v) :: tl))
        | Gt =>
            Ret (inl (prefix ++ [(k', v')], tl))
        end
    end.

  Definition iter_put (k v : Z) (xs : entries) : itree crisE entries :=
    ITree.iter (put_step k v) ([], xs).

  Definition scopes := [KVHdr.mn].
  Definition v_entries := KVHdr.mn ↯ "entries".

  Definition get : Z -> itree crisE (option Z) :=
    SortedListTarget.get.

  Definition put : Z * Z -> itree crisE () :=
    fun kv =>
      let '(k, v) := kv in
      'xs : entries <- cgetU v_entries;;
      ys <- iter_put k v xs;;
      cput v_entries ys;;;
      Ret tt.

  Definition fnsems : fnsemmap :=
    {[fid KVHdr.get #
        (msk_scp scopes msk_true,
          (fsp_none, cfunU KVHdr.get get));
      fid KVHdr.put #
        (msk_scp scopes msk_true,
          (fsp_none, cfunU KVHdr.put put))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_entries # ([] : entries)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End IterPutTarget. End IterPutTarget.

Module KVSortedListAdvancedProof.
  Import KVSource SortedListTarget IterPutTarget.

  Definition state_rel := KVSortedListProof.state_rel.

  Section Refinement.
    Context `{!crisG Γ Σ α β τ _S _I}.

    Definition IstLocal : ist_type Σ :=
      fun st_src st_tgt =>
        (∃ m xs,
          ⌜st_src = {[KVSource.v_map # m↑]} /\
           st_tgt = {[IterPutTarget.v_entries # xs↑]} /\
           state_rel m xs⌝)%I.

    Local Definition Source := KVSource.t.
    Local Definition Target := IterPutTarget.t.

    Definition Ist : ist_type Σ :=
      IstProd (IstSB Source.(Mod.scopes) IstLocal) IstEq.

    Lemma Ist_from_state_rel m xs st :
      ⌜state_rel m xs⌝ ⊢ Ist
        (union_with uwnd {[KVSource.v_map # m↑]} st)
        (union_with uwnd {[IterPutTarget.v_entries # xs↑]} st).
    Proof.
      iIntros "%Hrel".
      unfold Ist, IstProd, IstSB, IstLocal, IstEq.
      iExists
        {[KVSource.v_map # m↑]},
        {[IterPutTarget.v_entries # xs↑]}, st, st.
      iSplit; [iPureIntro; split; ss |].
      iSplit.
      - iSplit; [iPureIntro; split; set_solver |].
        iExists m, xs. iPureIntro.
        destruct Hrel as [Hsorted Hlookup].
        repeat split; try reflexivity; assumption.
      - iPureIntro. reflexivity.
    Qed.

    Lemma simF_put :
      ISim.sim_fun open Source Target Ist (fid KVHdr.put).
    Proof.
      cStartFunSim.
      unfold KVSource.put, IterPutTarget.put.
      cStepsS.
      lazymatch goal with
      | arg : Any.t |- _ =>
          destruct (Any.downcast arg) as [[k v]|] eqn:Harg;
            cStepsS; [|done]
      end.
      cStepsT.
      iDestruct "IST" as
        (st_srcL st_tgtL st_srcR st_tgtR) "%Hparts".
      destruct Hparts as
        [[Hsrc Htgt]
         [[[Hscope_src Hscope_tgt]
           [m [xs [HsrcL [HtgtL Hrel]]]]]
          Hright]].
      subst st_src st_tgt st_srcL st_tgtL st_srcR.
      cStepsS. cStepsT.
      pose proof
        (KVSortedListProof.state_rel_put m xs k v Hrel) as Hupdated.
      unfold IterPutTarget.iter_put.
      assert (Hcursor :
        [] ++ list_put k v xs = list_put k v xs) by reflexivity.
      revert Hcursor.
      generalize (@nil (Z * Z)) as prefix.
      generalize xs at 1 4. iIntros (cursor prefix Hcursor).
      iInduction cursor as [|[k' v'] tl] "IH" forall (prefix Hcursor).
      - aUnfoldT.
        cStepT. cStep.
        iSplit; [eauto |].
        iApply (Ist_from_state_rel _ _ st_tgtR).
        iPureIntro.
        simpl in Hcursor.
        rewrite Hcursor.
        exact Hupdated.
      - aUnfoldT. unfold IterPutTarget.put_step.
        destruct (Z.compare k k') eqn:Hcmp.
        + cStepT. cStep.
          iSplit; [eauto |].
          iApply (Ist_from_state_rel _ _ st_tgtR).
          iPureIntro.
          simpl in Hcursor. rewrite Hcmp in Hcursor.
          rewrite Hcursor.
          exact Hupdated.
        + cStepT. cStep.
          iSplit; [eauto |].
          iApply (Ist_from_state_rel _ _ st_tgtR).
          iPureIntro.
          simpl in Hcursor. rewrite Hcmp in Hcursor.
          rewrite Hcursor.
          exact Hupdated.
        + cStepT.
          iApply ("IH" $! (prefix ++ [(k', v')])).
          iPureIntro.
          simpl in Hcursor. rewrite Hcmp in Hcursor.
          rewrite <- app_assoc. simpl.
          exact Hcursor.
    Qed.

    Lemma simF_get :
      ISim.sim_fun open Source Target Ist (fid KVHdr.get).
    Proof.
      cStartFunSim.
      unfold KVSource.get, IterPutTarget.get, SortedListTarget.get.
      cStepsS.
      lazymatch goal with
      | arg : Any.t |- _ =>
          destruct (Any.downcast arg) as [k|] eqn:Harg;
            cStepsS; [|done]
      end.
      cStepsT.
      iDestruct "IST" as
        (st_srcL st_tgtL st_srcR st_tgtR) "%Hparts".
      destruct Hparts as
        [[Hsrc Htgt]
         [[[Hscope_src Hscope_tgt]
           [m [xs [HsrcL [HtgtL Hrel]]]]]
          Hright]].
      subst st_src st_tgt st_srcL st_tgtL st_srcR.
      cStepsS. cStepsT.
      pose proof Hrel as Hstate.
      destruct Hrel as [_ Hlookup]. rewrite Hlookup.
      generalize xs at 1 3. iIntros (cursor).
      iInduction cursor as [|[k' v'] tl] "IH".
      - aUnfoldT.
        cStep.
        iSplit; [eauto |].
        iApply (Ist_from_state_rel _ _ st_tgtR).
        iPureIntro.
        exact Hstate.
      - aUnfoldT. simpl. destruct (Z.compare k k') eqn:Hcmp.
        + cStep.
          iSplit; [eauto |].
          iApply (Ist_from_state_rel _ _ st_tgtR).
          iPureIntro.
          exact Hstate.
        + cStep.
          iSplit; [eauto |].
          iApply (Ist_from_state_rel _ _ st_tgtR).
          iPureIntro.
          exact Hstate.
        + cStepT. iApply "IH".
    Qed.

    Lemma sim : ISim.t open Source Target emp%I Ist.
    Proof.
      cStartModSim.
      - unfold Source, Target, Ist. unfold_mod.
        iIntros "_". unfold IstProd, IstSB, IstLocal, IstEq.
        iExists {[KVSource.v_map # KVSource.empty_map↑]},
          {[IterPutTarget.v_entries # ([] : entries)↑]}, ∅, ∅.
        iSplit; [iPureIntro; split; ss |].
        iSplit.
        + iSplit; [iPureIntro; split; set_solver |].
          iExists KVSource.empty_map, ([] : entries).
          iPureIntro. repeat split; try reflexivity.
          apply KVSortedListProof.state_rel_empty.
        + iPureIntro. reflexivity.
      - apply simF_get.
      - apply simF_put.
    Qed.

    Lemma ctxr : ⊢ ctx_refines Target Source.
    Proof. eapply main_adequacy, sim. Qed.
  End Refinement.
End KVSortedListAdvancedProof.
