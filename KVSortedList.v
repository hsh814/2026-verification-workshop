From CRIS Require Import CRIS Atomic.
From Stdlib Require Import Sorting.Sorted Lia.

Module KVHdr.
  Definition mn := "WorkshopKV".

  Definition fn (method : string) := mn +:+ "." +:+ method.

  Definition get := fnsig (fn "get") (fntyp Z (option Z)).
  Definition put := fnsig (fn "put") (fntyp (Z * Z) ()).
End KVHdr.

(** The source module is the abstract key-value store. *)
Module KVSource. Section KVSource.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition amap := Z -> option Z.

  Definition empty_map : amap := fun _ => None.

  Definition map_put (m : amap) (k v : Z) : amap :=
    fun q => if Z.eq_dec q k then Some v else m q.

  Definition scopes := [KVHdr.mn].
  Definition v_map := KVHdr.mn ↯ "map".

  Definition get : Z -> itree crisE (option Z) :=
    fun k =>
      'm : amap <- cgetU v_map;;
      Ret (m k).

  Definition put : Z * Z -> itree crisE () :=
    fun kv =>
      let '(k, v) := kv in
      'm : amap <- cgetU v_map;;
      cput v_map (map_put m k v);;;
      Ret tt.

  Definition fnsems : fnsemmap :=
    {[fid KVHdr.get #
        (msk_real (msk_scp scopes msk_true),
          (fsp_none, cfunU KVHdr.get get));
      fid KVHdr.put #
        (msk_real (msk_scp scopes msk_true),
          (fsp_none, cfunU KVHdr.put put))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_map # empty_map↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End KVSource. End KVSource.

(** The target module represents the map as a sorted mathematical list. *)
Module SortedListTarget. Section SortedListTarget.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition entries := list (Z * Z).

  Fixpoint list_get (q : Z) (xs : entries) : option Z :=
    match xs with
    | [] => None
    | (k, v) :: tl =>
        match Z.compare q k with
        | Lt => None
        | Eq => Some v
        | Gt => list_get q tl
        end
    end.

  Fixpoint list_put (k v : Z) (xs : entries) : entries :=
    match xs with
    | [] => [(k, v)]
    | (k', v') :: tl =>
        match Z.compare k k' with
        | Lt => (k, v) :: xs
        | Eq => (k, v) :: tl
        | Gt => (k', v') :: list_put k v tl
        end
    end.

  Definition key_lt (x y : Z * Z) : Prop := (fst x < fst y)%Z.

  Definition sorted_keys (xs : entries) : Prop := StronglySorted key_lt xs.

  (** One iterator step inspects exactly one list cell.  [inl tl] continues
      with the tail; [inr result] terminates the search. *)
  Definition get_step (q : Z) (rest : entries) :
      itree crisE (entries + option Z) :=
    match rest with
    | [] => Ret (inr None)
    | (k, v) :: tl =>
        match Z.compare q k with
        | Lt => Ret (inr None)
        | Eq => Ret (inr (Some v))
        | Gt => Ret (inl tl)
        end
    end.

  Definition iter_get (q : Z) (xs : entries) : itree crisE (option Z) :=
    ITree.iter (get_step q) xs.

  Definition scopes := [KVHdr.mn].
  Definition v_entries := KVHdr.mn ↯ "entries".

  (** The module state is read once.  The iterator then carries a local suffix
      and exposes one silent [Tau] for every skipped head. *)
  Definition get : Z -> itree crisE (option Z) :=
    fun k =>
      'xs : entries <- cgetU v_entries;;
      iter_get k xs.

  (** Insertion remains a direct list function so the exercise can focus on
      the induction caused by [get]'s iterator. *)
  Definition put : Z * Z -> itree crisE () :=
    fun kv =>
      let '(k, v) := kv in
      'xs : entries <- cgetU v_entries;;
      cput v_entries (list_put k v xs);;;
      Ret tt.

  Definition fnsems : fnsemmap :=
    {[fid KVHdr.get #
        (msk_real (msk_scp scopes msk_true),
          (fsp_none, cfunU KVHdr.get get));
      fid KVHdr.put #
        (msk_real (msk_scp scopes msk_true),
          (fsp_none, cfunU KVHdr.put put))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_entries # ([] : entries)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End SortedListTarget. End SortedListTarget.

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
    sorted_keys xs -> sorted_keys (list_put k v xs).
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
          assert ((q ?= k')%Z = Lt) as -> by
            (apply Z.compare_lt_iff; lia).
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

  Lemma state_rel_empty : state_rel empty_map [].
  Proof. split; [constructor | reflexivity]. Qed.

  Lemma state_rel_put m xs k v :
    state_rel m xs -> state_rel (map_put m k v) (list_put k v xs).
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

    Local Definition Source := KVSource.t.
    Local Definition Target := SortedListTarget.t.

    Definition Ist : ist_type Σ :=
      IstProd (IstSB Source.(Mod.scopes) IstLocal) IstEq.

    Lemma simF_get :
      ISim.sim_fun open Source Target Ist (fid KVHdr.get).
    Proof.
      cStartFunSim. unfold KVSource.get, SortedListTarget.get.
      cStepsS.
      destruct (Any.downcast arg) as [k|] eqn:Harg; cStepsS; [|done].
      cStepsT.
      iDestruct "IST" as (? ? ? ?) "%". des. cSimpl.
      cStepsS. cStepsT.
      destruct H4 as [Hsorted Hlookup]. rewrite Hlookup.
      unfold SortedListTarget.iter_get.
      generalize x0 at 1 3. iIntros (cursor).
      iInduction cursor as [|[k' v'] tl] "IH".
      - aUnfoldT. cStep. iSplit; [eauto |].
        iPureIntro. repeat (esplits; eauto).
        split; assumption.
      - aUnfoldT. simpl. destruct (Z.compare k k') eqn:Hcmp.
        + cStep. iSplit; [eauto |].
          iPureIntro. repeat (esplits; eauto).
          split; assumption.
        + cStep. iSplit; [eauto |].
          iPureIntro. repeat (esplits; eauto).
          split; assumption.
        + cStepT. iApply "IH".
    Qed.

    Lemma simF_put :
      ISim.sim_fun open Source Target Ist (fid KVHdr.put).
    Proof.
      cStartFunSim. unfold KVSource.put, SortedListTarget.put.
      cStepsS.
      destruct (Any.downcast arg) as [[k v]|] eqn:Harg; cStepsS; [|done].
      cStepsT.
      iDestruct "IST" as (? ? ? ?) "%". des. cSimpl.
      cStepsS. cStepsT.
      pose proof (state_rel_put x x0 k v H4) as Hrel.
      cStep. iSplit; [eauto |].
      iPureIntro. repeat (esplits; eauto).
    Qed.

    Lemma sim : ISim.t open Source Target emp%I Ist.
    Proof.
      cStartModSim.
      - unfold Source, Target, Ist. unfold_mod.
        iIntros "_". unfold IstProd, IstSB, IstLocal, IstEq.
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

    Lemma ctxr : ⊢ ctx_refines Target Source.
    Proof. eapply main_adequacy, sim. Qed.
  End Refinement.
End KVSortedListProof.
