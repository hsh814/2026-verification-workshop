From CRIS Require Import CRIS.

(** [ModuleIntro.v] ended with a linked module, a closed interaction tree, and
    a proposition about one behavior of that tree.

    We now compare two closed programs.  The target is acceptable when every
    target behavior is already a source behavior.  The argument order remains
    [Target] then [Source]. *)

Check refines_lmod.
Print refines_lmod.

(** The printed definition says:

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

(** Modules are open: a client may call their functions later.  Contextual
    refinement links the same compatible context to both modules before making
    the comparison. *)
Section ContextualRefinement.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Check ctx_refines.
  Print ctx_refines.

  (** CRIS supplies a compositional proof method: establish a simulation
      function by function, assemble a module simulation, and use adequacy once
      at the end. *)
  Check ISim.sim_fun.
  Check ISim.t.
  Check main_adequacy.

  Lemma simulation_is_enough
      (Source Target : Mod.t) (Ist : ist_type Σ)
      (SIM : ISim.t open Source Target emp%I Ist) :
    ⊢ ctx_refines Target Source.
  Proof.
    eapply main_adequacy, SIM.
  Qed.
End ContextualRefinement.

(** Keep the two orders visible:

      simulation:  ISim.t ... Source Target ...
      conclusion:  ctx_refines Target Source

    Next: [Optimizations.v].

    What does a simulation proof look like for actual function bodies?  The
    next file starts with a stateless constant-folding example, where the state
    relation is [True], then introduces private cells and a relation that must
    be restored after every state update. *)
