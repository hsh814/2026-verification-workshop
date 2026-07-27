(** * Template: Your Map Implementation *)

From CRIS.common Require Import CRIS.
From mem Require Import MemHeader.
From map.try Require Export MapHeader.

Module MapI. Section MapI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (** TODO: choose a representation and implement all four operations.
      Calls to memory should go through [MemHdr.alloc], [MemHdr.load], and
      [MemHdr.store]. *)
  Definition new_map : unit -> itree crisE loc.
  Admitted.

  Definition insert : loc * (nat * nat) -> itree crisE unit.
  Admitted.

  Definition delete : loc * nat -> itree crisE unit.
  Admitted.

  Definition get : loc * nat -> itree crisE (option nat).
  Admitted.

  Definition scopes : list string := ["Map"].

  Definition fnsems : fnsemmap :=
    {[fid MapHdr.new_map #
        (msk_scp scopes msk_true,
          (None, cfunU MapHdr.new_map new_map));
      fid MapHdr.insert #
        (msk_scp scopes msk_true,
          (None, cfunU MapHdr.insert insert));
      fid MapHdr.delete #
        (msk_scp scopes msk_true,
          (None, cfunU MapHdr.delete delete));
      fid MapHdr.get #
        (msk_scp scopes msk_true,
          (None, cfunU MapHdr.get get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End MapI. End MapI.
