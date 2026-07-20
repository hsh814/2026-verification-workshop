From CRIS Require Import CRIS.
From Stdlib Require Import Sorting.Sorted Lia.
From Workshop Require Import KVSource SortedListTarget.

Set Implicit Arguments.

Module KVSortedListProof.
  Import KVSource SortedListTarget.

  Lemma Forall_list_put_lower lo k v xs :
    (lo < k)%Z ->
    Forall (fun kv => (lo < fst kv)%Z) xs ->
    Forall (fun kv => (lo < fst kv)%Z) (list_put k v xs).
  Proof.
    intros Hlok Hxs. induction xs as [|[k' v'] tl IH]; simpl in *.
    - constructor; [exact Hlok | constructor].
    - inversion Hxs as [|? ? Hlok' Htl]; subst.
      destruct (Z.compare k k') eqn:Hcmp.
      + constructor; [exact Hlok | exact Htl].
      + constructor; [exact Hlok | constructor; assumption].
      + constructor; [exact Hlok' | apply IH; exact Htl].
  Qed.

  Lemma sorted_keys_put xs k v :
    sorted_keys xs ->
    sorted_keys (list_put k v xs).
  Proof.
    intros Hsorted. induction Hsorted as [|[k' v'] tl Htl IH Hall].
    - simpl. constructor; [constructor | constructor].
    - simpl. destruct (Z.compare k k') eqn:Hcmp.
      + rewrite Z.compare_eq_iff in Hcmp. subst k.
        constructor; assumption.
      + rewrite Z.compare_lt_iff in Hcmp.
        constructor.
        * constructor; assumption.
        * constructor; [exact Hcmp |].
          eapply Forall_impl; [exact Hall |].
          intros [k'' v''] Hlt. unfold key_lt in *. simpl in *. lia.
      + rewrite Z.compare_gt_iff in Hcmp.
        constructor; [exact IH |].
        apply Forall_list_put_lower; [exact Hcmp | exact Hall].
  Qed.

  Lemma list_get_put xs k v q :
    list_get q (list_put k v xs) =
      map_put (fun q => list_get q xs) k v q.
  Proof.
    unfold map_put.
    induction xs as [|[k' v'] tl IH]; simpl.
    - destruct (Z.compare q k) eqn:Hqk;
        destruct (Z.eq_dec q k) as [->|Hne]; simpl; try reflexivity.
      + rewrite Z.compare_eq_iff in Hqk. contradiction.
      + rewrite Z.compare_refl in Hqk. discriminate.
      + rewrite Z.compare_refl in Hqk. discriminate.
    - destruct (Z.compare k k') eqn:Hkk'; simpl.
      + rewrite Z.compare_eq_iff in Hkk'. subst k'.
        destruct (Z.compare q k) eqn:Hqk;
          destruct (Z.eq_dec q k) as [->|Hne]; simpl; try reflexivity.
        * rewrite Z.compare_eq_iff in Hqk. contradiction.
        * rewrite Z.compare_refl in Hqk. discriminate.
        * rewrite Z.compare_refl in Hqk. discriminate.
      + rewrite Z.compare_lt_iff in Hkk'.
        destruct (Z.compare q k) eqn:Hqk;
          destruct (Z.eq_dec q k) as [->|Hne]; simpl; try reflexivity.
        * rewrite Z.compare_eq_iff in Hqk. contradiction.
        * rewrite Z.compare_refl in Hqk. discriminate.
        * rewrite Z.compare_lt_iff in Hqk.
          assert ((q ?= k')%Z = Lt) as -> by (apply Z.compare_lt_iff; lia).
          reflexivity.
        * rewrite Z.compare_refl in Hqk. discriminate.
      + rewrite Z.compare_gt_iff in Hkk'.
        destruct (Z.compare q k') eqn:Hqk'.
        * rewrite Z.compare_eq_iff in Hqk'. subst q.
          destruct (Z.eq_dec k' k) as [Heq|Hne]; [lia | reflexivity].
        * rewrite Z.compare_lt_iff in Hqk'.
          destruct (Z.eq_dec q k) as [Heq|Hne]; [lia | reflexivity].
        * exact IH.
  Qed.

  Definition state_rel (m : amap) (xs : entries) : Prop :=
    sorted_keys xs /\ forall k, m k = list_get k xs.

  Lemma state_rel_empty :
    state_rel empty_map [].
  Proof.
    split; [constructor | reflexivity].
  Qed.

  Lemma state_rel_put m xs k v :
    state_rel m xs ->
    state_rel (map_put m k v) (list_put k v xs).
  Proof.
    intros [Hsorted Hlookup]. split.
    - apply sorted_keys_put. exact Hsorted.
    - intros q. rewrite list_get_put /map_put.
      destruct (Z.eq_dec q k); [reflexivity | apply Hlookup].
  Qed.

  Section Refinement.
    Context `{!crisG Γ Σ α β τ _S _I}.

    Definition IstLocal : ist_type Σ :=
      fun st_src st_tgt =>
        (∃ m xs,
          ⌜st_src = {[KVSource.v_map # m↑]} /\
           st_tgt = {[SortedListTarget.v_entries # xs↑]} /\
           state_rel m xs⌝)%I.

    Local Definition KVSourceMod := KVSource.t.
    Local Definition SortedListTargetMod := SortedListTarget.t.

    Definition Ist : ist_type Σ :=
      IstProd (IstSB KVSourceMod.(Mod.scopes) IstLocal) IstEq.

    Lemma simF_get :
      ISim.sim_fun open KVSourceMod SortedListTargetMod Ist (fid KVHdr.get).
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

    Lemma simF_put :
      ISim.sim_fun open KVSourceMod SortedListTargetMod Ist (fid KVHdr.put).
    Proof.
      cStartFunSim. rewrite /KVSource.put /SortedListTarget.put.
      cStepsS.
      destruct (Any.downcast arg) as [[k v]|] eqn:Harg; cStepsS; [|done].
      cStepsT.
      iDestruct "IST" as (? ? ? ?) "%". des. cSimpl.
      cStepsS. cStepsT.
      pose proof (state_rel_put (m := x) (xs := x0) k v H4)
        as Hrel.
      cStep. iSplit; [eauto |].
      iPureIntro. repeat (esplits; eauto).
    Qed.

    Lemma sim :
      ISim.t open KVSourceMod SortedListTargetMod emp%I Ist.
    Proof.
      cStartModSim.
      - rewrite /Ist /KVSourceMod /SortedListTargetMod. unfold_mod.
        iIntros "_". rewrite /IstProd /IstSB /IstLocal /IstEq.
        iExists {[KVSource.v_map # KVSource.empty_map↑]},
          {[SortedListTarget.v_entries # ([] : entries)↑]}, ∅, ∅.
        iSplit; [iPureIntro; split; ss |].
        iSplit.
        + iSplit; [iPureIntro; split; set_solver |].
          iExists KVSource.empty_map, ([] : entries).
          iPureIntro. repeat split; try reflexivity.
          apply state_rel_empty.
        + iPureIntro. reflexivity.
      - apply simF_get.
      - apply simF_put.
    Qed.

    Lemma ctxr :
      ctx_refines
        (SortedListTargetMod, emp%I)
        (KVSourceMod, emp%I).
    Proof.
      eapply main_adequacy, sim.
    Qed.
  End Refinement.
End KVSortedListProof.
