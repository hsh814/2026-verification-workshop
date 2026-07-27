(** * Reference Cell Implementation *)

From CRIS.common Require Import CRIS.
From refcell.frac_mem Require Import FracMemHeader.
From refcell.refcell Require Export RefCellHeader.

(** The header at [r] stores the protected location and a borrow flag.

    - [Vnat n] records [n] active shared borrows.
    - [Vundef] records one active mutable borrow.

    The protected value itself is stored in a separate cell [l]. *)
Definition shared_header (l : loc) (n : nat) : memval :=
  Vpair (Vloc (Some l)) (Vnat n).

Definition mutable_header (l : loc) : memval :=
  Vpair (Vloc (Some l)) Vundef.

Module RefCellI. Section RefCellI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["RefCell"].

  Definition new_refcell : memval -> itree crisE loc :=
    fun value =>
      l <- ccallU FracMemHdr.alloc tt;;
      _ <- ccallU FracMemHdr.store (l, value);;
      r <- ccallU FracMemHdr.alloc tt;;
      _ <- ccallU FracMemHdr.store (r, shared_header l 0);;
      Ret r.

  Definition try_borrow : loc -> itree crisE (option loc) :=
    fun r =>
      raw <- ccallU FracMemHdr.load r;;
      match raw with
      | Vpair (Vloc (Some l)) (Vnat n) =>
          _ <- ccallU FracMemHdr.store
            (r, shared_header l (S n));;
          Ret (Some l)
      | Vpair (Vloc (Some _)) Vundef =>
          Ret None
      | _ => triggerUB
      end.

  Definition try_borrow_mut : loc -> itree crisE (option loc) :=
    fun r =>
      raw <- ccallU FracMemHdr.load r;;
      match raw with
      | Vpair (Vloc (Some l)) (Vnat 0) =>
          _ <- ccallU FracMemHdr.store (r, mutable_header l);;
          Ret (Some l)
      | Vpair (Vloc (Some _)) (Vnat (S _)) =>
          Ret None
      | Vpair (Vloc (Some _)) Vundef =>
          Ret None
      | _ => triggerUB
      end.

  Definition drop : loc -> itree crisE unit :=
    fun r =>
      raw <- ccallU FracMemHdr.load r;;
      match raw with
      | Vpair (Vloc (Some _)) (Vnat 0) =>
          triggerUB
      | Vpair (Vloc (Some l)) (Vnat (S n)) =>
          _ <- ccallU FracMemHdr.store (r, shared_header l n);;
          Ret tt
      | Vpair (Vloc (Some l)) Vundef =>
          _ <- ccallU FracMemHdr.store (r, shared_header l 0);;
          Ret tt
      | _ => triggerUB
      end.

  Definition fnsems : fnsemmap :=
    {[fid RefCellHdr.new_refcell #
        (msk_scp scopes msk_true,
          (None, cfunU RefCellHdr.new_refcell new_refcell));
      fid RefCellHdr.try_borrow #
        (msk_scp scopes msk_true,
          (None, cfunU RefCellHdr.try_borrow try_borrow));
      fid RefCellHdr.try_borrow_mut #
        (msk_scp scopes msk_true,
          (None, cfunU RefCellHdr.try_borrow_mut try_borrow_mut));
      fid RefCellHdr.drop #
        (msk_scp scopes msk_true,
          (None, cfunU RefCellHdr.drop drop))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End RefCellI. End RefCellI.
