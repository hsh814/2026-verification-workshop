From CRIS Require Import CRIS.
From Stdlib Require Import Sorting.Sorted Lia.
From Workshop Require Import KVSource.

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

  Definition key_lt (x y : Z * Z) : Prop :=
    (fst x < fst y)%Z.

  Definition sorted_keys (xs : entries) : Prop :=
    StronglySorted key_lt xs.

  Definition scopes := [KVHdr.mn].
  Definition v_entries := KVHdr.mn ↯ "entries".

  Definition get : Z -> itree crisE (option Z) :=
    fun k =>
      'xs : entries <- cgetU v_entries;;
      Ret (list_get k xs).

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
