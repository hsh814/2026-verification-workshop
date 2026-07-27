(** * Concrete Memory Implementation

    This file is supplied.  Read it before writing the resources: the logical
    map must agree with [cells], and the authoritative monotone natural must
    agree with [count].  Only successful [load] and [store] calls increment
    the counter. *)

From CRIS.common Require Import CRIS.
From mem Require Export MemHeader.

Module MemState.
  Record t : Type := mk {
    cells : gmap loc memval;
    count : nat;
  }.

  Definition empty : t := mk ∅ 0.

  Definition alloc (m : t) : loc * t :=
    let l := fresh (dom m.(cells)) in
    (l, mk (<[l := Vundef]> m.(cells)) m.(count)).

  Definition load (m : t) (l : loc) : option (memval * t) :=
    v ← m.(cells) !! l;
    Some (v, mk m.(cells) (S m.(count))).

  Definition store (m : t) (l : loc) (v : memval) : option t :=
    _ ← m.(cells) !! l;
    Some (mk (<[l := v]> m.(cells)) (S m.(count))).
End MemState.

Module MemI. Section MemI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["Mem"].
  Definition v_mem : key := "Mem" ↯ "state".

  Definition alloc : unit → itree crisE loc :=
    λ _,
      m <- trigger (SGet v_mem);;
      m <- m↓?;;
      let result := MemState.alloc m in
      trigger (SPut v_mem (snd result)↑);;;
      Ret (fst result).

  Definition load : loc → itree crisE memval :=
    λ l,
      m <- trigger (SGet v_mem);;
      m <- m↓?;;
      '(v, m') : _ <- (MemState.load m l)?;;
      trigger (SPut v_mem m'↑);;;
      Ret v.

  Definition store : loc * memval → itree crisE unit :=
    λ '(l, v),
      m <- trigger (SGet v_mem);;
      m <- m↓?;;
      m' <- (MemState.store m l v)?;;
      trigger (SPut v_mem m'↑);;;
      Ret tt.

  Definition get_cnt : unit → itree crisE nat :=
    λ _,
      m <- trigger (SGet v_mem);;
      m <- m↓?;;
      Ret m.(MemState.count).

  Definition fnsems : fnsemmap :=
    {[fid MemHdr.alloc #
        (msk_scp scopes msk_true,
          (None, cfunU MemHdr.alloc alloc));
      fid MemHdr.load #
        (msk_scp scopes msk_true,
          (None, cfunU MemHdr.load load));
      fid MemHdr.store #
        (msk_scp scopes msk_true,
          (None, cfunU MemHdr.store store));
      fid MemHdr.get_cnt #
        (msk_scp scopes msk_true,
          (None, cfunU MemHdr.get_cnt get_cnt))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_mem # (MemState.empty)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End MemI. End MemI.
