From CRIS Require Import CRIS Atomic.

(** [RefinementIntro.v] reduced replacement to a simulation judgment:

      ISim.t ... Source Target ...  ->  ctx_refines Target Source

    This file adds one proof idea at a time:

      1. matching immediate returns;
      2. matching an observable I/O event and every possible reply;
      3. following a terminating [ITree.iter] by induction;
      4. carrying a relation across private state updates;
      5. passing that relation through a context-provided call.

    The first three functions share one module with empty local state.  The
    fourth function introduces a state relation, and the fifth uses it at a
    control boundary. *)

(** CRIS stores function bodies behind an [Any.t] interface.
    [cStartTypedFunSim] exposes the typed body and discharges the common
    ill-typed call case. *)
Ltac cStartTypedFunSim x :=
  cStartFunSim;
  cStepsS; cStepsT;
  lazymatch goal with
  | arg : Any.t |- _ =>
      destruct (Any.downcast arg) as [x|];
        cStepsS; [cStepsT|]; ss
  end.

(** Examples 1–3 share one module with empty local state. *)
Module StatelessOptHdr.
  Definition mn := "WorkshopStatelessOptimization".

  Definition fn (method : string) := mn +:+ "." +:+ method.

  Definition fold_constants := fnsig (fn "fold_constants") (fntyp () Z).
  Definition read_simplify := fnsig (fn "read_simplify") (fntyp () Z).
  Definition countdown := fnsig (fn "countdown") (fntyp nat nat).
End StatelessOptHdr.

Module StatelessOptSource. Section StatelessOptSource.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [StatelessOptHdr.mn].

  Definition fold_constants : () -> itree crisE Z :=
    fun _ => Ret ((1 + 2)%Z).

  Definition read_simplify : () -> itree crisE Z :=
    fun _ =>
      x <- trigger (IO (I := Z) "input" tt);;
      Ret (x + 0)%Z.

  Definition countdown : nat -> itree crisE nat :=
    fun n =>
      ITree.iter
        (fun cursor : nat =>
          match cursor with
          | O => Ret (inr O)
          | S cursor' => Ret (inl cursor')
          end)
        n.

  Definition fnsems : fnsemmap :=
    {[fid StatelessOptHdr.fold_constants #
        (msk_scp scopes msk_true,
         (fsp_none,
          cfunU StatelessOptHdr.fold_constants fold_constants));
      fid StatelessOptHdr.read_simplify #
        (msk_scp scopes msk_true,
         (fsp_none,
          cfunU StatelessOptHdr.read_simplify read_simplify));
      fid StatelessOptHdr.countdown #
        (msk_scp scopes msk_true,
         (fsp_none,
          cfunU StatelessOptHdr.countdown countdown))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End StatelessOptSource. End StatelessOptSource.

Module StatelessOptTarget. Section StatelessOptTarget.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [StatelessOptHdr.mn].

  Definition fold_constants : () -> itree crisE Z :=
    fun _ => Ret 3%Z.

  Definition read_simplify : () -> itree crisE Z :=
    fun _ =>
      x <- trigger (IO (I := Z) "input" tt);;
      Ret x.

  Definition countdown : nat -> itree crisE nat :=
    fun _ => Ret O.

  Definition fnsems : fnsemmap :=
    {[fid StatelessOptHdr.fold_constants #
        (msk_scp scopes msk_true,
         (fsp_none,
          cfunU StatelessOptHdr.fold_constants fold_constants));
      fid StatelessOptHdr.read_simplify #
        (msk_scp scopes msk_true,
         (fsp_none,
          cfunU StatelessOptHdr.read_simplify read_simplify));
      fid StatelessOptHdr.countdown #
        (msk_scp scopes msk_true,
         (fsp_none,
          cfunU StatelessOptHdr.countdown countdown))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End StatelessOptTarget. End StatelessOptTarget.

Module StatelessOptProof. Section StatelessOptProof.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Local Definition Source := StatelessOptSource.t.
  Local Definition Target := StatelessOptTarget.t.

  (** Both local states are empty, so every state pair satisfies [Ist]. *)
  Definition Ist : ist_type Σ := fun _ _ => True%I.

  (** Proof outline.

      [cStartTypedFunSim] exposes the two function bodies.  Unfolding those
      bodies leaves two matching returns and the obligation to restore
      [True]. *)
  Lemma simF_fold_constants :
    ISim.sim_fun open Source Target Ist
      (fid StatelessOptHdr.fold_constants).
  Proof using.
    cStartTypedFunSim u.
    unfold StatelessOptSource.fold_constants,
      StatelessOptTarget.fold_constants.
    (** PROOF OUTLINE:

        1. [cStep] matches the two returns.
        2. The resulting [ist_with_eq] asks for equal return values and [Ist].
        3. [iSplit] separates those two obligations.

        Replace [Admitted] with the demonstrated proof and [Qed]. *)
  Admitted.

  (** Example 2: the optimization happens after an observable input.

      [cStep as reply] matches the two identical I/O events.  The continuation
      proof receives one arbitrary reply chosen by the environment. *)
  Lemma simF_read_simplify :
    ISim.sim_fun open Source Target Ist
      (fid StatelessOptHdr.read_simplify).
  Proof using.
    cStartTypedFunSim u.
    unfold StatelessOptSource.read_simplify,
      StatelessOptTarget.read_simplify.
    cStep as reply.
    cStep. iSplit; [replace (reply + 0)%Z with reply by lia; done | done].
  Qed.

  (** Example 3: a terminating countdown loop has the same result as
      returning zero immediately.

      The loop cursor decreases from [S n] to [n].  [iInduction] follows that
      cursor.  [aUnfoldS] unfolds one iterator layer; the successor case
      exposes a [Tau] and the smaller iterator. *)
  Lemma simF_countdown :
    ISim.sim_fun open Source Target Ist (fid StatelessOptHdr.countdown).
  Proof using.
    cStartTypedFunSim n.
    unfold StatelessOptSource.countdown, StatelessOptTarget.countdown.
    iInduction n as [|n] "IH"; aUnfoldS.
    (** STOP 1: two goals are now visible.

        - Base case: [cStep] matches the returns; [iSplit] proves return
          equality and [Ist].
        - Successor case: [cStepS] takes the source-only silent step;
          [iApply ("IH" with "IST")] applies the induction hypothesis and
          supplies the current relation. *)
  Admitted.

  Lemma sim : ISim.t open Source Target emp%I Ist.
  Proof using.
    cStartModSim.
    (** Discharge source-map well-formedness, then register all three exported
        function simulations.  The empty initial states satisfy [Ist = True]. *)
    all: try solve [mod_tac].
    - apply simF_fold_constants.
    - apply simF_read_simplify.
    - apply simF_countdown.
  Qed.

  Lemma ctxr : ⊢ ctx_refines Target Source.
  Proof using. eapply main_adequacy, sim. Qed.
End StatelessOptProof. End StatelessOptProof.

(** Example 4: store-to-load forwarding with matching local cells.

    The source stores [x], reads the cell, and returns the read value.  The
    target stores [x] and forwards [x] directly to the return.  Both writes are
    internal module steps.

    The [callback_read] functions below are the callback example previewed in
    [RefinementIntro.v].  They carry the same relation across a call to code
    supplied by an unknown linking context. *)
Module CallbackHdr.
  Definition mn := "WorkshopCallback".

  Definition touch :=
    fnsig (mn +:+ ".touch") (fntyp () ()).
End CallbackHdr.

Module StateOptHdr.
  Definition mn := "WorkshopStateOptimization".

  Definition fn (method : string) := mn +:+ "." +:+ method.

  Definition store_load := fnsig (fn "store_load") (fntyp Z Z).
  Definition callback_read := fnsig (fn "callback_read") (fntyp Z Z).
End StateOptHdr.

Module StateOptSource. Section StateOptSource.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [StateOptHdr.mn].
  Definition cell := StateOptHdr.mn ↯ "cell".

  Definition store_load : Z -> itree crisE Z :=
    fun x =>
      cput cell x;;;
      y <- cgetU cell;;
      Ret y.

  Definition callback_read : Z -> itree crisE Z :=
    fun x =>
      cput cell x;;;
      ccallU CallbackHdr.touch tt;;;
      y <- cgetU cell;;
      Ret (y + 0)%Z.

  Definition fnsems : fnsemmap :=
    {[fid StateOptHdr.store_load #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU StateOptHdr.store_load store_load));
      fid StateOptHdr.callback_read #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU StateOptHdr.callback_read callback_read))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[cell # (0 : Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End StateOptSource. End StateOptSource.

Module StateOptTarget. Section StateOptTarget.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [StateOptHdr.mn].
  Definition cell := StateOptHdr.mn ↯ "cell".

  Definition store_load : Z -> itree crisE Z :=
    fun x =>
      cput cell x;;;
      Ret x.

  Definition callback_read : Z -> itree crisE Z :=
    fun x =>
      cput cell x;;;
      ccallU CallbackHdr.touch tt;;;
      y <- cgetU cell;;
      Ret y.

  Definition fnsems : fnsemmap :=
    {[fid StateOptHdr.store_load #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU StateOptHdr.store_load store_load));
      fid StateOptHdr.callback_read #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU StateOptHdr.callback_read callback_read))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[cell # (0 : Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End StateOptTarget. End StateOptTarget.

(** [CallbackHdr.touch] has no implementation in either module above.
    Contextual refinement covers every compatible implementation.  This
    concrete context demonstrates a re-entrant callback: while
    [callback_read] is suspended, [touch] calls [store_load 7] and changes the
    cell through the module's exported interface. *)
Module ReenteringContext. Section ReenteringContext.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [CallbackHdr.mn].

  Definition touch : () -> itree crisE () :=
    fun _ =>
      ccallU StateOptHdr.store_load 7%Z;;;
      Ret tt.

  Definition fnsems : fnsemmap :=
    {[fid CallbackHdr.touch #
        (msk_scp scopes msk_true,
         (fsp_none, cfunU CallbackHdr.touch touch))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End ReenteringContext. End ReenteringContext.

Module StateOptProof. Section StateOptProof.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Local Definition Source := StateOptSource.t.
  Local Definition Target := StateOptTarget.t.

  (** The source and target cells always contain the same integer. *)
  Definition Ist : ist_type Σ :=
    fun st_src st_tgt =>
      (∃ x : Z,
        ⌜st_src = {[StateOptSource.cell # x↑]} /\
         st_tgt = {[StateOptTarget.cell # x↑]}⌝)%I.

  (** The proof-mode commands follow the connectives in [Ist].

      - [iDestruct "IST" as (old) "%"] opens the existential and moves its
        embedded Rocq fact into the pure context.
      - [iExists x] chooses a witness when proving an existential.
      - [iSplit] separates a conjunction or separating conjunction goal. *)

  (** Proof outline.

      Opening [IST] yields the old cell value.  Both stores establish the
      input [x] as the new relation witness. *)
  Lemma simF_store_load :
    ISim.sim_fun open Source Target Ist (fid StateOptHdr.store_load).
  Proof using.
    cStartTypedFunSim x.
    unfold StateOptSource.store_load, StateOptTarget.store_load.
    iDestruct "IST" as (old) "%". destruct H as [-> ->].
    cStepsS. cStepsT. cStep.
    iSplit; [eauto |].
    (** STOP 2: the remaining goal is the post-state relation.  Use
        [iExists x] to choose the value written by both modules. *)
  Admitted.

  (** Example 5: carry [Ist] through an unknown call.

      Both modules first restore [Ist] with witness [x].  [cCall] hands that
      relation to the context.  It resumes with an arbitrary return value and
      arbitrary post-call states satisfying [Ist].  Reading those states then
      produces equal logical values.

      The [Any.downcast] case split is the runtime return-type check inserted
      by [ccallU].  It is provided typed-call infrastructure. *)
  Lemma simF_callback_read :
    ISim.sim_fun open Source Target Ist (fid StateOptHdr.callback_read).
  Proof using.
    cStartTypedFunSim x.
    unfold StateOptSource.callback_read, StateOptTarget.callback_read.
    iDestruct "IST" as (old) "%". destruct H as [-> ->].
    cStepsS. cStepsT.

    (** Guarantee the relation before control enters unknown context code. *)
    iAssert
      (Ist {[StateOptSource.cell # x↑]} {[StateOptTarget.cell # x↑]})
      as "IST".
    { iExists x. done. }

    cCall "IST" as (ret st_src st_tgt) "IST".
    destruct Any.downcast as [u|].
    - (** Rely on the relation returned with the arbitrary post-call states. *)
      iDestruct "IST" as (after) "%". destruct H as [-> ->].
      cStepsS. cStepsT. cStep.
      iSplit;
        [replace (after + 0)%Z with after by lia; done |].
      iExists after. done.
    - cStepsS. ss.
  Qed.

  Lemma sim : ISim.t open Source Target emp%I Ist.
  Proof using.
    cStartModSim.
    - iIntros "_". iExists 0. done.
    - apply simF_store_load.
    - apply simF_callback_read.
  Qed.

  Lemma ctxr : ⊢ ctx_refines Target Source.
  Proof using. eapply main_adequacy, sim. Qed.

  (** Specializing [ctxr] shows that the re-entrant callback above is one of
      the contexts covered by the open simulation. *)
  Lemma reentering_context_example :
    ⊢ refines
        (Target ★ ReenteringContext.t)
        (Source ★ ReenteringContext.t).
  Proof using.
    iPoseProof ctxr as "REF".
    iSpecialize ("REF" $! ReenteringContext.t).
    iExact "REF".
  Qed.
End StateOptProof. End StateOptProof.

(** Next: [KVSortedList.v].

    The examples above introduced I/O matching, iterator induction, a relation
    between equal-shaped states, and an unknown context call.  A data-structure
    refinement combines these ideas with different state representations.  The
    next file relates an abstract map to a sorted mathematical list, and its
    [get] proof follows a list suffix through [ITree.iter]. *)
