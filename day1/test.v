(* Inductive nat : Type :=
    | O
    | S (n : nat).

Check (O: nat).
Check (S O: nat).

Set Printing All.
Check 3. *)

Definition minustwo (n : nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

Compute (minustwo 4).

Fixpoint sum (n: nat) : nat :=
    match n with
    | O => O
    | S n' => n + sum n'
    end.

Compute (sum 100).

Check minustwo : nat -> nat.
Check sum : nat -> nat.
(* nat -> nat: uncountable!!! *)

Definition g (f: nat -> nat) : nat :=
    f 42.

Compute (g minustwo).

(* Dependent function: different input -> different output type *)
(* Check foo: forall (n: nat), vector nat n. *)

Require Import Lia.
(* Theorem: alias of Definition *)
Theorem sum_correct : 
    forall n: nat, 2 * (sum n) = n * (n + 1).
Proof.
    intros. induction n.
    - (* base case *) simpl. reflexivity.
    - simpl. nia.
Qed.

Print sum_correct.

(* CoInductive: almost same as Inductive, accept infinite *)
CoInductive even : nat -> Prop :=
    | even_O : even O
    | even_SS : forall n, even n -> even (S (S n)).


