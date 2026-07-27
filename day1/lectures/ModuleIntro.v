From CRIS Require Import CRIS.

(** [Behavior.v] ended at the whole-program observation layer:

      Beh.of_itree : itree coreE Any.t -> Tr.t -> Prop.

    This file constructs the following ordinary program:

      ConstService.get() = 42
      Main.main() = ConstService.get()

    We define the service and client separately, package each one as a module,
    link them, and compile the result for [Beh.of_itree].  Each [Check] reports
    the type of a concrete object immediately after its definition.

    Rocq's [Module ... End] commands create namespaces.  CRIS semantic modules
    are ordinary values whose types are [SMod.t], [Mod.t], and [LMod.t]. *)

(** The header gives the exported function a name and the signature
    [unit -> Z].  [fntyp A R] describes an [A -> R] function type, and
    [fnsig name type] attaches a global function name to that type. *)

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
  (** These parameters provide CRIS's ambient logic and semantic
      infrastructure.  This file leaves their internals abstract. *)
  Context `{!crisG Γ Σ α β τ _S _I}.

  (** A scope names the module-owned region of the linked state. *)
  Definition scopes := [ConstHdr.mn].

  Definition get : () -> itree crisE Z :=
    fun _ => Ret 42%Z.

  (** The implementation receives [unit] and returns [Z] in [itree crisE]. *)
  Check get.

  (** [get] is our first concrete function body.  [crisE] includes named calls,
      module-local state operations, and the residual [coreE] effects. *)
  Print crisE.
  Check Call.
  Check SGet.
  Check SPut.

  (** One function-map entry has the shape

        function id # (event mask, (optional specification, erased body)).

      [cfunU] packages the typed body behind CRIS's [Any.t] runtime
      interface.  The mask and optional-specification fields remain fixed in
      this introductory executable module. *)
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
  (** [Program] generates well-scopedness obligations for this record.
      [mod_tac] discharges this mechanical module bookkeeping. *)
  Solve All Obligations with mod_tac.

  (** [smod] packages its scopes, function semantics, and initial local state.
      Applying the record projections reveals the type of each field. *)
  Check smod.
  Check (SMod.scopes smod).
  Check (SMod.fnsems smod).
  Check (SMod.initial_st smod).

  (** The empty map in [initial_st] above is a local-state map.  The empty map
      passed to [SMod.to_mod] below is a specification map; Rocq infers their
      distinct types from context.  [SMod.to_mod] produces a linkable [Mod.t]. *)
  Definition t : Mod.t := SMod.to_mod ∅ smod.
  Check t.
End ConstModule. End ConstModule.

(** A client module supplies the program entry point.  Its body calls the
    exported service function and returns the result. *)

Module MainModule. Section MainModule.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (** This client owns no private state, so its scope list is empty. *)
  Definition scopes : list string := [].

  (** The header determines the argument and result types of [ccallU].
      Operationally, [ccallU] emits a named [Call] event and checks the
      dynamically typed reply. *)
  Check (ccallU ConstHdr.get : () -> itree crisE Z).

  Definition main : Any.t -> itree crisE Any.t :=
    fun _ =>
      n <- ccallU ConstHdr.get tt;;
      Ret n↑.

  (** The entry function uses CRIS's [Any.t] program interface. *)
  Check main.

  (** [entry] is the distinguished function name from which
      [LMod.compile] starts the whole program. *)
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

(** Linking assembles both function bodies and their initial states.
    Compilation resolves the call and produces the interaction tree whose
    behaviors are observed by [Beh.of_itree]. *)

Module LinkedProgram. Section LinkedProgram.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (** [★] is CRIS module linking.  It combines compatible function maps,
      scopes, and initial local states. *)
  Definition modules : Mod.t := MainModule.t ★ ConstModule.t.

  (** Linking two [Mod.t] objects produces another [Mod.t]. *)
  Check modules.

  (** [ε] is the empty logical-resource state used to initialize this
      example's linked module. *)
  Definition linked : LMod.t := Mod.to_lmod modules ε.

  (** [Mod.to_lmod] produces the [LMod.t] consumed by [LMod.compile]. *)
  Check linked.

  (** [Mod.to_lmod] translates each [crisE] body to [lmodE], turning [SGet] and
      [SPut] into linked-state operations.  [LMod.compile] then resolves named
      calls and interprets that state. *)
  Check LMod.compile.

  (** [tt↑] supplies the erased unit argument to [entry]. *)
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

    The linked program above contains a client module and a service module.
    Different teams may own those two components.

      application team                 library team
      writes Client                    develops Cell
      calls Cell.set/get               publishes an API and contract
      proves an output property        owns private code and state

    Consider this public Cell interface and contract:

      set : Z -> unit
      get : unit -> Z
      with no intervening set, a get() following set(v) returns v.

    One private implementation keeps a field [current], assigns [v] to it in
    [set(v)], and returns it from [get()].  The application team sees the
    contract.  From that contract it proves that

      Cell.set(42);; x <- Cell.get();; output(x)

    outputs [42].

    A later release may optimize [set], add a cache, or change the state
    representation.  The application proof remains stated against the same
    public contract.  The provider validates a release with one all-client
    replacement theorem, read schematically at the behavior level:

      for every compatible Ctx,
        Beh(CellImpl linked with Ctx)
          is included in
        Beh(CellSpec linked with Ctx).

    [RefinementIntro.v] states this theorem as
    [ctx_refines CellImpl CellSpec], specializes it to one client, and proves
    that the Cell component can be replaced inside a larger linked module.
    It then follows the semantic adequacy layers down to closed-program
    behavior inclusion. *)
