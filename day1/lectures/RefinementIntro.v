From CRIS Require Import CRIS.
From CRIS.lib Require Import BiEnrichedProset.

(** [ModuleIntro.v] ended with a client team and a library team.

    The library publishes [CellSpec]:

      set : Z -> unit
      get : unit -> Z
      with no intervening set, a get() following set(v) returns v.

    The application team uses that contract to prove that

      Cell.set(42);; x <- Cell.get();; output(x)

    outputs [42].  The provider owns [CellImpl], including its algorithm and
    private state.  A new release may optimize or change that implementation
    while keeping the same public contract.

    Modular verification assigns one proof to each team:

      application proof:  Client linked with CellSpec satisfies a property
      library proof:      CellImpl may replace CellSpec in every context

    Their composition justifies the same property for [Client] linked with the
    deployed implementation.

    We begin with that replacement theorem itself.  [CellImpl] is its target
    and [CellSpec] is its source.  All four modules remain abstract in this
    file; the example studies the statement and use of a replacement theorem. *)

Section CellReplacement.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Variables (CellImpl CellSpec Client ClientSpec : Mod.t).

  (** The provider's theorem has this exact Rocq proposition. *)
  Check (⊢ ctx_refines CellImpl CellSpec).

  (** Contextual refinement can first be used with one particular client.
      The same [Client] module definition is linked on both sides.  The two
      linked programs still have separate executions and runtime states. *)
  Lemma cell_in_one_context :
    ctx_refines CellImpl CellSpec ⊢
    refines (CellImpl ★ Client) (CellSpec ★ Client).
  Proof.
    iIntros "CELL_REF".
    iSpecialize ("CELL_REF" $! Client).
    iExact "CELL_REF".
  Qed.

  Check cell_in_one_context.

  (** The stronger modular statement keeps the linked result open for future
      linking. *)
  Lemma replace_cell_in_client :
    ctx_refines CellImpl CellSpec ⊢
    ctx_refines (CellImpl ★ Client) (CellSpec ★ Client).
  Proof.
    iIntros "CELL_REF".
    jStartProof (ctx_refines_BiProset).
    jIntros "(IMPL & CLIENT)".
    jPoseProof "CELL_REF" with "IMPL" as "SPEC".
    jFrame.
  Qed.

  Check replace_cell_in_client.

  (** The application team may verify [Client] using only [CellSpec] and expose
      a separate abstraction [ClientSpec].  [CellSpec] remains linked on both
      sides of this client-side refinement. *)
  Check (⊢ ctx_refines
    (CellSpec ★ Client)
    (CellSpec ★ ClientSpec)).

  Lemma deploy_client_abstraction :
    ctx_refines CellImpl CellSpec ∗
    ctx_refines (CellSpec ★ Client) (CellSpec ★ ClientSpec) ⊢
    ctx_refines (CellImpl ★ Client) (CellSpec ★ ClientSpec).
  Proof.
    iIntros "[CELL_REF CLIENT_REF]".
    iApply ctxr_trans.
    iSplitR "CLIENT_REF".
    - iApply replace_cell_in_client.
      iExact "CELL_REF".
    - iExact "CLIENT_REF".
  Qed.

  Check deploy_client_abstraction.

  (** We now follow the conclusion to behavior inclusion.

      [ctx_refines] quantifies over a semantic linking context [Ctx : Mod.t].
      Instantiating either contextual-refinement edge with [Ctx := ⌽] and
      simplifying [M ★ ⌽] to [M] yields a concrete module-level refinement. *)
  Print ctx_refines.
  Check (refines
    (CellImpl ★ Client)
    (CellSpec ★ Client)).

  (** [refines] compares two [Mod.t] modules after accounting for
      well-formedness and logical resources. *)
  Check Beh.
  Print refines.

  (** Given target well-formedness and the initial world invariant,
      [refines_adequacy] closes both modules and packages a valid initial
      logical-resource state for the source.  Its [refines_lmod] conclusion
      unfolds to behavior inclusion between the compiled linked programs. *)
  Check refines_adequacy.
End CellReplacement.

(** The semantic bottom layer compares two closed [LMod.t] programs. *)
Check refines_lmod.
Print refines_lmod.

(** The definition says:

      Beh(compile Target) ⊆ Beh(compile Source)

    The following lemma applies that set inclusion to one trace. *)
Lemma refinement_means_behavior_inclusion
    (Target Source : LMod.t) (trace : Tr.t) :
  refines_lmod Target Source ->
  Beh.of_itree (LMod.compile Target tt↑) trace ->
  Beh.of_itree (LMod.compile Source tt↑) trace.
Proof.
  intros Href Htarget.
  apply Href.
  exact Htarget.
Qed.

(** Refinement transfers every property that holds for all source behaviors:

      target behavior -> source behavior -> desired property. *)
Lemma refinement_transfers_universal_properties
    (Target Source : LMod.t) (P : Tr.t -> Prop)
    (REFINE : refines_lmod Target Source)
    (SOURCE_OK :
       forall trace,
         Beh.of_itree (LMod.compile Source tt↑) trace ->
         P trace) :
  forall trace,
    Beh.of_itree (LMod.compile Target tt↑) trace ->
    P trace.
Proof.
  intros trace TARGET_BEHAVIOR.
  apply SOURCE_OK.
  apply REFINE.
  exact TARGET_BEHAVIOR.
Qed.

Section Simulation.
  (** This is the same ambient CRIS infrastructure introduced in
      [ModuleIntro.v]. *)
  Context `{!crisG Γ Σ α β τ _S _I}.

  (** Our next proof goal has the form

        ⊢ ctx_refines Target Source.

      Unfolding [ctx_refines] asks for behavior inclusion after linking every
      compatible context.  A direct proof would choose an arbitrary context,
      analyze each complete target execution, and construct a source execution
      with the same trace.  Calls, re-entry, I/O, and infinite executions make
      that whole-execution argument global.

      A simulation captures the local correspondence instead.  It relates a
      source configuration to a target configuration.  Whenever the target
      advances, the source performs matching steps, exposes the same observable
      interaction, and reaches a related configuration again.  Repeating this
      rule constructs a source behavior for every target behavior.

      Modules add control boundaries to the rule.  The simulation proof handles
      execution while the module has control.  An unresolved [Call] transfers
      control to the linking context, whose execution may include I/O, choices,
      and re-entrant calls.  The simulation therefore needs a relation on the
      two module-local states whenever control crosses this boundary.

      CRIS names this relation [Ist].  Its exact type is

        source local state -> target local state -> iProp Σ.

      The remaining computations determine which state facts [Ist] must retain.
      Stateless examples may use [True].  Representation-changing examples
      relate selected entries or logical representations.

      [Ist] is the control-boundary contract:

        entry of known code      rely on Ist
        before an unknown Call  guarantee Ist
        after that Call         rely on the restored Ist
        synchronized return     guarantee equal results and Ist.

      At an unresolved call, the simulation matches the same function name and
      argument.  It guarantees [Ist] before the context executes.  Both
      continuations resume for one shared return value and every post-state
      pair satisfying [Ist]. *)

  (** [ISim.sim_fun] handles one exported function.  [ISim.t] combines the
      initial-state relation, scope and function-map checks, and every required
      function simulation.  [open] selects the mode in which unresolved
      context-provided calls must be matched across both executions. *)
  Check (ist_type Σ).
  Check open.
  Check ISim.sim_fun.
  Check ISim.t.

  (** Soundness is a theorem of CRIS.  [ISim_ctx] links the same context to both
      modules, relates the context-owned state by equality, and produces a
      closed simulation.  [main_adequacy] uses that construction and closed
      adequacy to obtain behavior inclusion for every context. *)

  (** Keep the two argument orders visible:

        ISim.t ... Source Target ...
        ctx_refines Target Source.

      The simulation follows a source-side and a target-side execution.  The
      refinement conclusion names the replacing target layer first.  [emp%I]
      below states that this wrapper theorem needs no initial logical
      resource. *)

  Lemma simulation_is_enough
      (Source Target : Mod.t) (Ist : ist_type Σ)
      (SIM : ISim.t open Source Target emp%I Ist) :
    ⊢ ctx_refines Target Source.
  Proof.
    eapply main_adequacy.
    exact SIM.
  Qed.

  Check simulation_is_enough.
End Simulation.

(** The proof ladder for the next file is:

      per-function [ISim.sim_fun]
                -> module-level [ISim.t]
                -> [main_adequacy]
                -> [ctx_refines Target Source].

    Next: day1/exercises/Optimizations.v.

    The constant-folding proof follows this ladder one goal at a time.  Its
    state relation is [True].  Later examples introduce private cells, restore
    their relation after updates, and pass that relation through an unknown
    context-provided call. *)
