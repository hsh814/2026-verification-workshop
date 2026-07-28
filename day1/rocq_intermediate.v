(** Rocq 중급 연습 — 전략을 스스로 생각해보세요. *)

(** === 1. 함수와 map === *)

Definition map_opt {A B : Type} (f : A -> B) (x : option A) : option B :=
  match x with
  | None => None
  | Some a => Some (f a)
  end.

Lemma map_opt_id : forall {A : Type} (x : option A),
  map_opt (fun a => a) x = x.
Proof.
  intros A x.
  destruct x.
  - reflexivity.
  - reflexivity.
Qed.

Lemma map_opt_comp : forall {A B C : Type} (f : A -> B) (g : B -> C) (x : option A),
  map_opt g (map_opt f x) = map_opt (fun a => g (f a)) x.
Proof.
  intros A B C f g x.
  destruct x.
  - reflexivity.
  - reflexivity.
Qed.

(** === 2. 리스트 기초 === *)

Require Import List.
Import ListNotations.

Fixpoint list_sum (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => x + list_sum xs'
  end.

Require Import Lia.
Lemma list_sum_app : forall xs ys : list nat,
  list_sum (xs ++ ys) = list_sum xs + list_sum ys.
Proof.
  intros xs ys.
  induction xs as [| x xs' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.


(** === 3. 리스트 뒤집기 === *)

Fixpoint rev_acc {A : Type} (acc : list A) (xs : list A) : list A :=
  match xs with
  | [] => acc
  | x :: xs' => rev_acc (x :: acc) xs'
  end.

Definition rev' {A : Type} (xs : list A) : list A :=
  rev_acc [] xs.

Lemma rev_acc_correct : forall {A : Type} (xs acc : list A),
  rev_acc acc xs = rev xs ++ acc.
Proof.
  induction xs as [| x xs' IH]; intros acc.
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma rev'_correct : forall {A : Type} (xs : list A),
  rev' xs = rev xs.
Proof.
  (* 힌트: rev_acc에 대한 일반화된 lemma를 먼저 증명하세요 *)
  intros A xs.
  unfold rev'. rewrite rev_acc_correct. apply app_nil_r.
  
Qed.

(** === 4. 키-값 맵 ===
    KVSortedList의 state_rel과 같은 패턴입니다. *)
Require Import ZArith.
Definition map_key := Z.
Definition map_val := Z.
Definition amap := map_key -> option map_val.

Definition empty_map : amap := fun _ => None.

Definition map_put (m : amap) (k : map_key) (v : map_val) : amap :=
  fun q => if Z.eq_dec q k then Some v else m q.

Lemma map_put_get_same : forall (m : amap) (k : map_key) (v : map_val),
  map_put m k v k = Some v.
Proof.
  intros m k v. unfold map_put.
  destruct (Z.eq_dec k k); [reflexivity | contradiction].
Qed.

Lemma map_put_get_diff : forall (m : amap) (k q : map_key) (v : map_val),
  q <> k -> map_put m k v q = m q.
Proof.
  intros m k q v Hneq. unfold map_put.
  destruct (Z.eq_dec q k) as [Heq|_]; [exfalso; apply Hneq; exact Heq | reflexivity].
Qed.

(** === 5. 연결 리스트 스택 === *)

Inductive stack (A : Type) : Type :=
  | empty : stack A
  | push : A -> stack A -> stack A.
Arguments empty {A}.
Arguments push {A} _ _.

Fixpoint stack_pop {A : Type} (s : stack A) : option (A * stack A) :=
  match s with
  | empty => None
  | push x rest => Some (x, rest)
  end.

Lemma pop_after_push : forall {A : Type} (x : A) (s : stack A),
  stack_pop (push x s) = Some (x, s).
Proof.
  intros A x s.
  simpl. reflexivity.
Qed. 

(** === 6. sorted_keys 연습 ===
    KVSortedList의 sorted_keys를 단순화한 버전입니다. *)

Require Import Sorting.Sorted.

Definition entries := list (Z * Z).

Definition key_lt (x y : Z * Z) : Prop := (fst x < fst y)%Z.

Definition sorted_keys (xs : entries) : Prop := StronglySorted key_lt xs.

Lemma sorted_nil : sorted_keys [].
Proof.
  unfold sorted_keys. constructor.
Qed.

Lemma sorted_singleton (k v : Z) : sorted_keys [(k, v)].
Proof.
  unfold sorted_keys. constructor.
  - constructor.
  - constructor.
Qed.

(** === 7. list_get === *)

Fixpoint list_get (q : Z) (xs : entries) : option Z :=
  match xs with
  | [] => None
  | (k, v) :: tl =>
      match Z.compare q k with
      | Lt => None
      | Eq => Some v
      | Gt => list_get q tl
      end
  end.

Lemma list_get_empty : forall q : Z, list_get q [] = None.
Proof.
  intros q.
  simpl. reflexivity.
Qed. 

Lemma list_get_head_eq : forall (q v : Z) (tl : entries),
  list_get q ((q, v) :: tl) = Some v.
Proof.
  intros q v tl. simpl.
  rewrite Z.compare_refl.
  reflexivity.
Qed.

(** ============================================================
    답
    ============================================================ *)

Module Answers.

Lemma map_opt_id : forall {A : Type} (x : option A),
  map_opt (fun a => a) x = x.
Proof.
  destruct x; [reflexivity | reflexivity].
Qed.

Lemma map_opt_comp : forall {A B C : Type} (f : A -> B) (g : B -> C) (x : option A),
  map_opt g (map_opt f x) = map_opt (fun a => g (f a)) x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma list_sum_app : forall xs ys : list nat,
  list_sum (xs ++ ys) = list_sum xs + list_sum ys.
Proof.
  induction xs as [| x xs IH]; intros ys.
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma rev_acc_correct : forall {A : Type} (xs acc : list A),
  rev_acc acc xs = rev xs ++ acc.
Proof.
  induction xs as [| x xs IH]; intros acc.
  - reflexivity.
  - simpl. rewrite IH. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma rev'_correct : forall {A : Type} (xs : list A),
  rev' xs = rev xs.
Proof.
  intro xs. unfold rev'. rewrite rev_acc_correct. apply app_nil_r.
Qed.

Lemma pop_after_push : forall {A : Type} (x : A) (s : stack A),
  stack_pop (push x s) = Some (x, s).
Proof.
  reflexivity.
Qed.

Lemma sorted_nil : sorted_keys [].
Proof.
  unfold sorted_keys. constructor.
Qed.

Lemma sorted_singleton (k v : Z) : sorted_keys [(k, v)].
Proof.
  unfold sorted_keys. constructor.
  - constructor.
  - constructor.
Qed.

Lemma list_get_empty : forall q : Z, list_get q [] = None.
Proof.
  reflexivity.
Qed.

End Answers.
