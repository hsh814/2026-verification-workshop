From CRIS Require Import CRIS.

(** A CRIS module packages named function bodies and private initial state.

    Process the [Check] commands one at a time in the editor.  This file follows
    one call from an entry module to a service module, then links the modules
    into a closed program. *)

Check SMod.t.
Check SMod.fnsems.
Check SMod.initial_st.
Check Mod.t.
Check Mod.add.
Check LMod.compile.

(** The header gives the exported function a name and a type. *)

Module ConstHdr.
  Definition mn := "WorkshopConst".

  Definition fn (method : string) := mn +:+ "." +:+ method.

  Definition get := fnsig (fn "get") (fntyp () Z).
End ConstHdr.

Check ConstHdr.get.

(** The service module implements [get()].  For this demo, read the [fnsems]
    entry as a mapping from [ConstHdr.get] to its body.  The mask and
    [fsp_none] fields stay fixed. *)

Module ConstModule. Section ConstModule.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [ConstHdr.mn].

  Definition get : () -> itree crisE Z :=
    fun _ => Ret 42%Z.

  Definition fnsems : fnsemmap :=
    {[fid ConstHdr.get #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU ConstHdr.get get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.

  Check get.
  Print get.
  Check smod.
  Check t.
End ConstModule. End ConstModule.

(** A client module supplies the program entry point.  Its body calls the
    exported service function and returns the result. *)

Module MainModule. Section MainModule.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition main : Any.t -> itree crisE Any.t :=
    fun _ =>
      n <- ccallU ConstHdr.get tt;;
      Ret n↑.

  Definition fnsems : fnsemmap :=
    {[entry #
        (msk_scp scopes msk_true,
         (fsp_none, main))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.

  Check main.
  Check smod.
  Check t.
End MainModule. End MainModule.

(** Linking places both function bodies in one closed module.  Compilation
    resolves the call and produces the interaction tree whose behaviors are
    observed by [Beh.of_itree]. *)

Module LinkedProgram. Section LinkedProgram.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition modules : Mod.t := MainModule.t ★ ConstModule.t.

  Definition program : itree coreE Any.t :=
    LMod.compile (Mod.to_lmod modules ε) tt↑.

  Check modules.
  Check program.
  Check (Beh.of_itree program).
  Check (Beh.of_itree program (Tr.done (42%Z)↑)).
End LinkedProgram. End LinkedProgram.
