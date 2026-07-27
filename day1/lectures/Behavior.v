From CRIS Require Import CRIS.

(** A behavior is an observable trace of an interaction tree.

    [Check] reports the type of an expression.  [Print] displays the
    constructors or definition of a named object.  The complete proofs certify
    the example behaviors.

    A proposition [Beh.of_itree program trace] says that [trace] is one
    behavior of [program].  It is a membership statement.  Several such
    propositions may hold for the same program. *)

Print Beh.t.
Check Beh.of_itree.

(** A compiled whole program has event signature [coreE] and returns a value
    through CRIS's dynamically typed [Any.t] interface.  The notation [v↑]
    injects a typed Rocq value [v] into [Any.t]. *)

Check ((42%Z)↑ : Any.t).

(** Returning a value produces a terminating trace. *)

Definition return_42 : itree coreE Any.t :=
  Ret (42%Z)↑.

Check return_42.
Check (Beh.of_itree return_42).
Check (Tr.done (42%Z)↑).

Lemma return_42_terminates :
  Beh.of_itree return_42 (Tr.done (42%Z)↑).
Proof.
  (** [pstep] opens one layer of the coinductive behavior relation.
      [Beh.sb_final] is the semantic rule for [Ret]. *)
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

(** Nondeterminism gives one program more than one behavior.  A proof of one
    behavior chooses the corresponding continuation witness. *)

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
  'answer : Z <- trigger (IO (I := Z) "echo" 7%Z);;
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
  (** [left] selects the recursive continuation case of the coinductive trace
      relation after recording the I/O event. *)
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

(** Review the trace shapes after seeing termination, nondeterminism, and I/O.
    [Tr.spin] is the observable trace of infinite silent execution. *)
Print Tr.t.
Check Tr.spin.

(** [coreE] is the residual effect signature of a compiled whole program.
    [Choose] and [Take] determine which continuations contribute behaviors;
    [IO] contributes observable trace events.  The examples above used
    [Choose] and [IO].  CRIS specifications use [Take] in later layers. *)
Print coreE.

(** [coreE] contains nondeterministic choice and I/O.  Named function calls and
    module-local state operations have already been interpreted by the time a
    program has type [itree coreE Any.t].

    Defining a whole program directly at this layer presents one monolithic
    computation.  Named client/service boundaries and private module states
    have already disappeared, which prevents linking a client against a
    different implementation. *)

(** Next: [ModuleIntro.v].

    CRIS keeps a module-construction layer for two purposes.  Named components
    support separate implementation, linking, and contextual verification.
    Module-owned initial states give state operations a concrete interpretation
    when the components are linked and compiled.

    At this layer, each named function body is an [itree crisE] fragment that
    may call another function and access its module-local state.
    [ModuleIntro.v] packages the fragments into modules, links them, and
    compiles the result into the [itree coreE Any.t] passed to [Beh.of_itree]. *)
