(** Rocq 입문 연습 — 하나씩 풀어보세요.

    각 문제 아래에 [Admitted.]를 지우고 [Proof. ... Qed.]를 채우면 됩니다.
    답은 아래쪽에 있습니다. *)

(** === 1. constructor ===
    [nat]은 귀납적 타입입니다:
      Inductive nat : Set := O | S (n : nat).

    [le]는 [nat] 간의 순서 관계입니다:
      Inductive le (n : nat) : nat -> Prop :=
        | le_n : n <= n
        | le_S : n <= m -> n <= S m.
*)

Lemma zero_le_zero : 0 <= 0.
Proof.
(* 힌트: goal 모양에 맞는 생성자를 고르세요 *)
    constructor.
Qed.
Check le_S.

Lemma zero_le_two : 0 <= 2.
Proof.
(* 힌트: 0 <= 2 를 만들려면 le_S를 몇 번 써야 할까요? *)
    apply le_S. apply le_S. constructor.
Qed.

(** === 2. intro / intros === *)

Lemma forall_intro_example : forall n : nat, n = n.
Proof.
(* 힌트: forall n, ... 은 intro n 부터 *)
    intros n. reflexivity.
Qed.

Lemma forall_two : forall a b : nat, a + b = a + b.
Proof.
  intros a b. reflexivity.
Qed.

(** === 3. reflexivity / symmetry === *)

Lemma one_plus_one : 1 + 1 = 2.
Proof.
  simpl. reflexivity.
Qed.

Lemma true_eq_true : true = true.
Proof.
  reflexivity.
Qed.

(** === 4. split (∧) === *)

Lemma and_intro : 1 = 1 /\ 2 = 2.
Proof.
  split . reflexivity. reflexivity.
Qed.

(** === 5. destruct (경우 분기) === *)

Lemma zero_or_succ (n : nat) : n = 0 \/ exists m, n = S m.
Proof.
(* destruct n으로 경우를 나눠보세요 *)
  destruct n as [ | n'].
  - left. reflexivity.
  - right. exists n'. reflexivity.
Qed.

(** === 6. apply === *)
Require Import Arith.
Lemma add_comm_example : forall n m : nat, n + m = m + n.
Proof.
  (* 힌트: 기존에 증명된 Nat.add_comm을 apply 하면 됩니다 *)
  intros n m. apply Nat.add_comm.
Qed.

(** === 7. induction === *)

Lemma plus_n_0 : forall n : nat, n + 0 = n.
Proof.
(* induction n as [|n IH]로 시작 *)
  induction n as [| n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma plus_n_Sm : forall n m : nat, n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [| n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** === 8. unfold === *)

Definition double (n : nat) := n + n.

Lemma double_0 : double 0 = 0.
Proof.
(* unfold double 하고 reflexivity *)
  unfold double. reflexivity.
Qed.

(** === 9. rewrite === *)

Lemma rewrite_example : forall a b : nat, a = b -> a + 1 = b + 1.
Proof.
  intros a b H.
  (* H: a = b 를 rewrite *)
  rewrite H. reflexivity.
Qed.

(** === 10. 종합 === *)

Definition triple (n : nat) := n + n + n.

Lemma triple_plus_one : forall n : nat, triple n + 1 = n + n + n + 1.
Proof.
  intro n. unfold triple.
  (* 이제 goal은 n + n + n + 1 = n + n + n + 1 *)
  reflexivity.
Qed.

(** ============================================================
    연습문제 답
    ============================================================ *)

Module Answers.

Lemma zero_le_zero : 0 <= 0.
Proof. constructor. Qed.

Lemma zero_le_two : 0 <= 2.
Proof.
  apply le_S. apply le_S. constructor.
Qed.

Lemma forall_intro_example : forall n : nat, n = n.
Proof. intro n. reflexivity. Qed.

Lemma forall_two : forall a b : nat, a + b = a + b.
Proof. intros a b. reflexivity. Qed.

Lemma one_plus_one : 1 + 1 = 2.
Proof. reflexivity. Qed.

Lemma true_eq_true : true = true.
Proof. reflexivity. Qed.

Lemma and_intro : 1 = 1 /\ 2 = 2.
Proof. split; reflexivity. Qed.

Lemma zero_or_succ (n : nat) : n = 0 \/ exists m, n = S m.
Proof.
  destruct n as [| n'].
  - left. reflexivity.
  - right. exists n'. reflexivity.
Qed.

Lemma add_comm_example : forall n m : nat, n + m = m + n.
Proof.
  intros n m. apply Nat.add_comm.
Qed.

Lemma plus_n_0 : forall n : nat, n + 0 = n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma plus_n_Sm : forall n m : nat, n + S m = S (n + m).
Proof.
  induction n as [| n IH]; intros m.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma double_0 : double 0 = 0.
Proof.
  unfold double. reflexivity.
Qed.

Lemma rewrite_example : forall a b : nat, a = b -> a + 1 = b + 1.
Proof.
  intros a b H. rewrite H. reflexivity.
Qed.

Lemma triple_plus_one : forall n : nat, triple n + 1 = n + n + n + 1.
Proof.
  intro n. unfold triple. reflexivity.
Qed.

End Answers.
