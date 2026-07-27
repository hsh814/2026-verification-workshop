From CRIS Require Import CRIS.

(** A behavior is an observable trace of an interaction tree.

    The [Check] commands expose the relevant types.  The complete proofs
    certify the example behaviors.

    A proposition [Beh.of_itree program trace] says that [trace] is one
    behavior of [program].  It is a membership statement.  Several such
    propositions may hold for the same program. *)

Print Tr.t.
Print Beh.t.
Check Beh.of_itree.
Check Tr.spin.

(** [Tr.spin] is the observable trace of infinite silent execution.  The
    examples below focus on finite termination, nondeterminism, and I/O; the
    trace type already has a constructor for divergence. *)

(** Returning a value produces a terminating trace. *)

Definition return_42 : itree coreE Any.t :=
  Ret (42%Z)↑.

Check return_42.
Check (Beh.of_itree return_42).
Check (Tr.done (42%Z)↑).

Lemma return_42_terminates :
  Beh.of_itree return_42 (Tr.done (42%Z)↑).
Proof.
  unfold return_42.
  pstep. constructor. apply Beh.sb_final.
Qed.

Check return_42_terminates.

(** A silent [tau] step does not appear in the trace. *)

Definition silent_return_42 : itree coreE Any.t :=
  tau;; return_42.

Lemma silent_return_42_terminates :
  Beh.of_itree silent_return_42 (Tr.done (42%Z)↑).
Proof.
  unfold silent_return_42, return_42.
  pstep. constructor. apply Beh.sb_tau.
  constructor. apply Beh.sb_final.
Qed.

Check silent_return_42_terminates.

(** Nondeterminism gives one program more than one behavior. *)

Definition choose_bit : itree coreE Any.t :=
  'b : bool <- trigger (Choose bool);;
  Ret ((if b then 1%Z else 0%Z)↑).

Lemma choose_bit_can_return_zero :
  Beh.of_itree choose_bit (Tr.done (0%Z)↑).
Proof.
  unfold choose_bit.
  pstep. constructor. apply Beh.sb_choose.
  exists false.
  constructor. apply Beh.sb_final.
Qed.

Lemma choose_bit_can_return_one :
  Beh.of_itree choose_bit (Tr.done (1%Z)↑).
Proof.
  unfold choose_bit.
  pstep. constructor. apply Beh.sb_choose.
  exists true.
  constructor. apply Beh.sb_final.
Qed.

Check choose_bit_can_return_zero.
Check choose_bit_can_return_one.

(** An I/O behavior records the request, the response, and what happens next. *)

Definition echo_once : itree coreE Any.t :=
  'answer : Z <- trigger (@IO Z Z "echo" 7%Z);;
  Ret answer↑.

Definition echo_reply_9 : Tr.t :=
  Tr.interact (obs_io "echo" 7%Z 9%Z) (Tr.done (9%Z)↑).

Check echo_once.
Check echo_reply_9.

Lemma echo_once_reply_9 :
  Beh.of_itree echo_once echo_reply_9.
Proof.
  unfold echo_once, echo_reply_9.
  pstep. constructor. apply Beh.sb_interact.
  left. pstep. constructor. apply Beh.sb_final.
Qed.

(** The environment may also leave the request unanswered. *)
Lemma echo_once_may_hang :
  Beh.of_itree echo_once (Tr.hang (obs_hang "echo" 7%Z)).
Proof.
  unfold echo_once.
  pstep. constructor. apply Beh.sb_hang.
Qed.

Check echo_once_reply_9.
Check echo_once_may_hang.

(** Next: [ModuleIntro.v].

    [Beh.of_itree] observes a closed tree of type [itree coreE Any.t].  Programs
    are usually written as several modules whose function bodies may call one
    another and access private state.  [ModuleIntro.v] constructs the closed
    interaction tree passed to [Beh.of_itree]. *)
