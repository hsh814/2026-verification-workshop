(** * Supplied Concrete Implementation for Fractional Memory

    Fractions exist only in the abstract logical resources.  The executable
    memory remains an ordinary finite map with an access counter. *)

From CRIS.common Require Import CRIS.
From refcell.frac_mem Require Export FracMemHeader.

Module FracMemState.
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
End FracMemState.

Module FracMemI. Section FracMemI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["FracMem"].
  Definition v_mem : key := "FracMem" ↯ "state".

  Definition alloc : unit -> itree crisE loc :=
    fun _ =>
      m <- trigger (SGet v_mem);;
      m <- m↓?;;
      let result := FracMemState.alloc m in
      trigger (SPut v_mem (snd result)↑);;;
      Ret (fst result).

  Definition load : loc -> itree crisE memval :=
    fun l =>
      m <- trigger (SGet v_mem);;
      m <- m↓?;;
      '(v, m') : _ <- (FracMemState.load m l)?;;
      trigger (SPut v_mem m'↑);;;
      Ret v.

  Definition store : loc * memval -> itree crisE unit :=
    fun '(l, v) =>
      m <- trigger (SGet v_mem);;
      m <- m↓?;;
      m' <- (FracMemState.store m l v)?;;
      trigger (SPut v_mem m'↑);;;
      Ret tt.

  Definition get_cnt : unit -> itree crisE nat :=
    fun _ =>
      m <- trigger (SGet v_mem);;
      m <- m↓?;;
      Ret m.(FracMemState.count).

  Definition fnsems : fnsemmap :=
    {[fid FracMemHdr.alloc #
        (msk_scp scopes msk_true,
          (None, cfunU FracMemHdr.alloc alloc));
      fid FracMemHdr.load #
        (msk_scp scopes msk_true,
          (None, cfunU FracMemHdr.load load));
      fid FracMemHdr.store #
        (msk_scp scopes msk_true,
          (None, cfunU FracMemHdr.store store));
      fid FracMemHdr.get_cnt #
        (msk_scp scopes msk_true,
          (None, cfunU FracMemHdr.get_cnt get_cnt))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_mem # (FracMemState.empty)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End FracMemI. End FracMemI.
