From CRIS Require Import CRIS.
From Workshop Require Import SimulationCases.

Set Implicit Arguments.

Module SimulationCasesExercises. Section Exercises.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition ExerciseIst : ist_type Σ :=
    fun st_src st_tgt => ⌜st_src = ∅ /\ st_tgt = ∅⌝%I.

  Local Definition Source := CasesSource.t.
  Local Definition Target := CasesTarget.t.

  (** Exercise 1.  The source immediately returns [42], while the target takes
      two silent [Tau] steps first.  The setup below has already decoded the
      unit argument.  Advance the target and match the two returns. *)
  Lemma exercise_simF_ret_tau :
    ISim.sim_fun open Source Target ExerciseIst (fid CasesHdr.ret_tau).
  Proof using.
    cStartFunSim. unfold CasesSource.ret_tau, CasesTarget.ret_tau.
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    (* TODO: use a target-side step, then close the matching return case. *)
  Abort.

  (** Exercise 2.  The source specification permits [0] or [1], while the
      target implementation deterministically returns [0].  Pick the source
      [Choose] witness that explains the target behavior. *)
  Lemma exercise_simF_choose_zero :
    ISim.sim_fun open Source Target ExerciseIst (fid CasesHdr.choose_zero).
  Proof using.
    cStartFunSim. unfold CasesSource.choose_zero, CasesTarget.choose_zero.
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    (* TODO: force the source choice with [true], then match the returns. *)
  Abort.

  (** Before continuing, use the handout to say which side chooses a witness
      for source/target [Take], and why equal [IO] requests move in lockstep.
      The compiler-pair exercise makes the [IO] case concrete. *)
End Exercises. End SimulationCasesExercises.
