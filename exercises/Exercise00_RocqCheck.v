From CRIS Require Import CRIS.
From Workshop Require Import SimulationCases.

Set Implicit Arguments.

Local Open Scope Z_scope.

(** If this file opens without an import error, Rocq can see both CRIS and the
    workshop theories.  The following commands should display their types. *)
Check itree.
Check Choose.
Check IO.
Check CasesSource.ret_tau.
Check CasesTarget.ret_tau.

Example rocq_check_completed_example : (1 + 1 = 2)%Z.
Proof. reflexivity. Qed.

(** Exercise 0.  Replace [Abort] with a one-tactic proof and finish with
    [Qed].  This is only an editor/toolchain check. *)
Lemma rocq_check_first_exercise : (40 + 2 = 42)%Z.
Proof.
  (* TODO: [reflexivity]. *)
Abort.
