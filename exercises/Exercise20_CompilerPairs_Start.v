From CRIS Require Import CRIS.
From Workshop Require Import CompilerPairs.

Set Implicit Arguments.

Local Open Scope Z_scope.

Module CompilerPairsExercises. Section Exercises.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (** The target's scratch value is compiler-private.  At a function boundary
      we require only that the slot exists with the expected type. *)
  Definition ExerciseIst : ist_type Σ :=
    fun st_src st_tgt =>
      (⌜st_src = ∅⌝ ∧
       ∃ n : Z, ⌜st_tgt = {[CompilerTarget.tmp # n↑]}⌝)%I.

  Local Definition Source := CompilerSource.t.
  Local Definition Target := CompilerTarget.t.

  (** Exercise 3.  Simulate the target-only [SPut]/[SGet] lowering steps and
      restore [ExerciseIst] with the updated scratch value. *)
  Lemma exercise_simF_scratch :
    ISim.sim_fun open Source Target ExerciseIst (fid CompilerHdr.scratch).
  Proof using.
    cStartFunSim. unfold CompilerSource.scratch, CompilerTarget.scratch.
    iDestruct "IST" as "(-> & %old & ->)".
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    (* TODO: execute the target local-state steps, match [Ret 42], and rebuild
       the invariant with the new scratch value as witness. *)
  Abort.

  (** Exercise 4.  First consume the same target-only local-state steps.  The
      next [cStep] must match equal observable [IO "print" [42]] requests and
      continue for every environment response. *)
  Lemma exercise_simF_print_scratch :
    ISim.sim_fun open Source Target ExerciseIst
      (fid CompilerHdr.print_scratch).
  Proof using.
    cStartFunSim.
    unfold CompilerSource.print_scratch, CompilerTarget.print_scratch.
    iDestruct "IST" as "(-> & %old & ->)".
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    (* TODO: target local state, matching I/O, matching return, invariant. *)
  Abort.

  (** Exercise 5.  This small pure fact is the observable mismatch in
      [BadIOPair].  No amount of silent stuttering can turn one request into
      the other. *)
  Lemma exercise_bad_io_payloads_differ :
    ([42] : list Z) <> [43].
  Proof.
    (* TODO: [discriminate]. *)
  Abort.
End Exercises. End CompilerPairsExercises.
