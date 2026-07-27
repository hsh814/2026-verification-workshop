From CRIS Require Import CRIS.

(** [Behavior.v] showed how CRIS observes a closed [itree coreE].  A CRIS
    module packages the named function bodies and private initial state from
    which that closed tree is built.

    The definitions below follow one call from an entry module to a service
    module, then link the modules into a closed program.  Each [Check] reports
    the type of a concrete object immediately after its definition. *)

(** The header gives the exported function a name and the signature
    [unit -> Z]. *)

Module ConstHdr.
  Definition mn := "WorkshopConst".

  Definition fn (method : string) := mn +:+ "." +:+ method.

  Definition get := fnsig (fn "get") (fntyp () Z).
End ConstHdr.

Check ConstHdr.get.

(** The service module implements [get()].  Its [fnsems] entry maps
    [ConstHdr.get] to the function body.  The mask and [fsp_none] fields stay
    fixed. *)

Module ConstModule. Section ConstModule.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [ConstHdr.mn].

  Definition get : () -> itree crisE Z :=
    fun _ => Ret 42%Z.

  (** The implementation receives [unit] and returns [Z] in [itree crisE]. *)
  Check get.

  Definition fnsems : fnsemmap :=
    {[fid ConstHdr.get #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU ConstHdr.get get))]}.

  (** [fnsems] registers the implementation under [fid ConstHdr.get]. *)
  Check fnsems.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  (** [smod] packages its scopes, function semantics, and initial local state.
      Applying the record projections reveals the type of each field. *)
  Check smod.
  Check (SMod.scopes smod).
  Check (SMod.fnsems smod).
  Check (SMod.initial_st smod).

  (** [SMod.to_mod] produces a linkable [Mod.t]. *)
  Definition t : Mod.t := SMod.to_mod ∅ smod.
  Check t.
End ConstModule. End ConstModule.

(** A client module supplies the program entry point.  Its body calls the
    exported service function and returns the result. *)

Module MainModule. Section MainModule.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  (** The header determines the argument and result types of [ccallU]. *)
  Check (ccallU ConstHdr.get : () -> itree crisE Z).

  Definition main : Any.t -> itree crisE Any.t :=
    fun _ =>
      n <- ccallU ConstHdr.get tt;;
      Ret n↑.

  (** The entry function uses CRIS's [Any.t] program interface. *)
  Check main.

  Definition fnsems : fnsemmap :=
    {[entry #
        (msk_scp scopes msk_true,
         (fsp_none, main))]}.

  (** This map registers [main] under the distinguished [entry] name. *)
  Check fnsems.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Check smod.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
  Check t.
End MainModule. End MainModule.

(** Linking places both function bodies in one closed module.  Compilation
    resolves the call and produces the interaction tree whose behaviors are
    observed by [Beh.of_itree]. *)

Module LinkedProgram. Section LinkedProgram.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition modules : Mod.t := MainModule.t ★ ConstModule.t.

  (** Linking two [Mod.t] objects produces another [Mod.t]. *)
  Check modules.

  Definition linked : LMod.t := Mod.to_lmod modules ε.

  (** [Mod.to_lmod] produces the [LMod.t] consumed by [LMod.compile]. *)
  Check linked.

  Definition program : itree coreE Any.t :=
    LMod.compile linked tt↑.

  (** Compilation produces the closed interaction tree from [Behavior.v]. *)
  Check program.

  (** Partial application gives a predicate on traces.  Supplying a trace
      gives one concrete behavior proposition. *)
  Check (Beh.of_itree program).
  Check (Beh.of_itree program (Tr.done (42%Z)↑)).
End LinkedProgram. End LinkedProgram.

(** Next: [RefinementIntro.v].

    Linking and compilation gave one closed program and its behaviors.  A
    compiler or library implementation must establish when another module may
    replace [ConstModule] in every compatible linking context. *)
