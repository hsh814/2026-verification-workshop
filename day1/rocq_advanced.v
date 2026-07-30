(** Rocq 고급 연습 — CRIS에 한 걸음 더 *)

(** === 1. 간단한 표현식 평가기 === *)
Require Import ZArith.

Inductive expr : Type :=
  | EInt (n : Z)
  | EAdd (e1 e2 : expr)
  | EMul (e1 e2 : expr).

Fixpoint eval (e : expr) : Z :=
  match e with
  | EInt n => n
  | EAdd e1 e2 => eval e1 + eval e2
  | EMul e1 e2 => eval e1 * eval e2
  end.

(** 최적화: 0을 더하거나 1을 곱하는 경우 제거 *)

Fixpoint optimize (e : expr) : expr :=
  match e with
  | EInt n => EInt n
  | EAdd (EInt 0) e2 => optimize e2
  | EAdd e1 (EInt 0) => optimize e1
  | EAdd e1 e2 => EAdd (optimize e1) (optimize e2)
  | EMul (EInt 1) e2 => optimize e2
  | EMul e1 (EInt 1) => optimize e1
  | EMul e1 e2 => EMul (optimize e1) (optimize e2)
  end.

Require Import Lia.
Theorem optimize_correct : forall e, eval (optimize e) = eval e.
Proof.
  induction e as [n | e1 e2 IH1 IH2 | e1 e2 IH1 IH2]; simpl.
  - reflexivity.
  - destruct e1, e2; simpl in *;
      Show.
      try rewrite IH1;
      try rewrite IH2;
      repeat match goal with z : Z |- _ => destruct z end;
      simpl; lia.
  - destruct e1, e2; simpl in *;
      try rewrite IH1;
      try rewrite IH2;
      repeat match goal with z : Z |- _ => destruct z end;
      simpl; lia.
Qed.

(** === 2. 상태를 가진 계산 (State-passing) === *)

Definition state := Z.
Definition result (A : Type) := state -> A * state.

Definition ret {A : Type} (x : A) : result A :=
  fun s => (x, s).

Definition bind {A B : Type} (m : result A) (f : A -> result B) : result B :=
  fun s =>
    let '(x, s') := m s in f x s'.

Definition get : result state := fun s => (s, s).
Definition put (s' : state) : result unit := fun _ => (tt, s').

Lemma bind_ret_l : forall {A B : Type} (x : A) (f : A -> result B) s,
  bind (ret x) f s = f x s.
Proof.
Admitted.

Lemma bind_ret_r : forall {A : Type} (m : result A) s,
  bind m ret s = m s.
Proof.
Admitted.

(** === 3. state relation (CRIS Ist의 맛보기) === *)

Definition state_rel (actual : Z) (stored : Z) : Prop := actual = stored.

(** 두 개의 state을 가진 프로그램
    - Source: state == actual
    - Target: state == stored (같은 값이어야 함) *)

Definition source_prog (x : Z) : result Z :=
  fun _ => (* 실제 계산 *)
    let r := x + 1 in
    (r, r).

Definition target_prog (x : Z) : result Z :=
  fun s0 =>
    let r := x + 1 in
    let s1 := r in  (* 저장 *)
    (r, s1).

Lemma simulate_add_one : forall (x : Z) (s_src s_tgt : Z),
  state_rel s_src s_tgt ->
  let r_src := source_prog x s_src in
  let r_tgt := target_prog x s_tgt in
  fst r_src = fst r_tgt /\ state_rel (snd r_src) (snd r_tgt).
Proof.
Admitted.

(** === 4. 귀납적 명제 — 작은 언어의 의미론 *)

Inductive id : Type := Id : Z -> id.

Inductive command : Type :=
  | CSet (x : id) (n : Z)
  | CSeq (c1 c2 : command)
  | CAssert (e : Z)  (* 실행 중 e가 0이 아니면 계속, 아니면 멈춤 *).

Definition store := id -> Z.

Inductive ceval : command -> store -> store -> Prop :=
  | E_Set x n s : ceval (CSet x n) s (fun y => if Z.eq_dec y x then n else s y)
  | E_Seq c1 c2 s s' s'' : ceval c1 s s' -> ceval c2 s' s'' -> ceval (CSeq c1 c2) s s''
  | E_Assert_Z e s : s e <> 0%Z -> ceval (CAssert e) s s
  | E_Assert_NZ e s : s e = 0%Z -> ceval (CAssert e) s s. (* 아무 일도? *)

Lemma ceval_deterministic : forall c s s1 s2,
  ceval c s s1 -> ceval c s s2 -> s1 = s2.
Proof.
Admitted.

(** === 5. 리스트로 구현한 맵 vs 함수로 구현한 맵 (KVSortedList 축소판) === *)

Definition key := Z.
Definition val := Z.

(** 구현 A: 함수 *)
Definition map_fun := key -> option val.

Definition empty_fun : map_fun := fun _ => None.
Definition get_fun (m : map_fun) (k : key) := m k.
Definition put_fun (m : map_fun) (k : key) (v : val) : map_fun :=
  fun q => if Z.eq_dec q k then Some v else m q.

(** 구현 B: 리스트 *)
Definition map_list := list (key * val).

Fixpoint get_list (xs : map_list) (k : key) : option val :=
  match xs with
  | [] => None
  | (k', v) :: tl => if Z.eq_dec k k' then Some v else get_list tl k
  end.

Fixpoint put_list (xs : map_list) (k : key) (v : val) : map_list :=
  match xs with
  | [] => [(k, v)]
  | (k', v') :: tl =>
      if Z.eq_dec k k'
      then (k, v) :: tl
      else (k', v') :: put_list tl k v
  end.

(** representation relation *)
Definition map_rel (m : map_fun) (xs : map_list) : Prop :=
  forall k, get_fun m k = get_list xs k.

Lemma map_rel_empty : map_rel empty_fun [].
Proof.
  intro k. unfold empty_fun, get_fun, get_list. reflexivity.
Qed.

Lemma map_rel_put : forall (m : map_fun) (xs : map_list) (k : key) (v : val),
  map_rel m xs -> map_rel (put_fun m k v) (put_list xs k v).
Proof.
Admitted.

(** === 6. 간단한 Contextual Refinement ===
    "추상 스택"과 "리스트 스택"의 관계 *)

Inductive stack_abs : Type :=
  | Empty
  | Push (x : Z) (s : stack_abs).

Fixpoint height (s : stack_abs) : nat :=
  match s with
  | Empty => 0
  | Push _ s' => 1 + height s'
  end.

Inductive stack_list :=
  | SNil
  | SCons (x : Z) (tl : stack_list).

Fixpoint list_height (s : stack_list) : nat :=
  match s with
  | SNil => 0
  | SCons _ tl => 1 + list_height tl
  end.

(** 두 표현이 "같은 높이"를 가진다는 관계 *)
Definition height_rel (s : stack_abs) (l : stack_list) : Prop :=
  height s = list_height l.

Lemma height_rel_empty : height_rel Empty SNil.
Proof.
Admitted.

Lemma height_rel_push : forall (x : Z) (s : stack_abs) (l : stack_list),
  height_rel s l -> height_rel (Push x s) (SCons x l).
Proof.
Admitted.

(** ============================================================
    답
    ============================================================ *)

Module Answers.

Theorem optimize_correct : forall e, eval (optimize e) = eval e.
Proof.
  induction e as [n | e1 IH1 e2 IH2 | e1 IH1 e2 IH2]; simpl.
  - reflexivity.
  - destruct e1; destruct e2; simpl; try rewrite IH1; try rewrite IH2; lia.
  - destruct e1; destruct e2; simpl; try rewrite IH1; try rewrite IH2; lia.
Qed.

Lemma bind_ret_l : forall {A B : Type} (x : A) (f : A -> result B) s,
  bind (ret x) f s = f x s.
Proof.
  reflexivity.
Qed.

Lemma bind_ret_r : forall {A : Type} (m : result A) s,
  bind m ret s = m s.
Proof.
  unfold bind, ret. destruct (m s). reflexivity.
Qed.

Lemma simulate_add_one : forall (x : Z) (s_src s_tgt : Z),
  state_rel s_src s_tgt ->
  let r_src := source_prog x s_src in
  let r_tgt := target_prog x s_tgt in
  fst r_src = fst r_tgt /\ state_rel (snd r_src) (snd r_tgt).
Proof.
  intros x s_src s_tgt Hrel.
  unfold state_rel in Hrel. subst s_tgt.
  unfold source_prog, target_prog. simpl. split; reflexivity.
Qed.

Lemma ceval_deterministic : forall c s s1 s2,
  ceval c s s1 -> ceval c s s2 -> s1 = s2.
Proof.
  intros c s s1 s2 H1 H2.
  revert s2 H2.
  induction H1 as [x n s | c1 c2 s s' s'' H1 IH1 H2 IH2 | e s H | e s H];
    intros s2 H2; inversion H2; subst; try reflexivity.
  - f_equal. apply IH1 with s'. exact H6.
  - f_equal. apply IH2. exact H8.
Qed.

Lemma map_rel_put : forall (m : map_fun) (xs : map_list) (k : key) (v : val),
  map_rel m xs -> map_rel (put_fun m k v) (put_list xs k v).
Proof.
  intros m xs k v Hrel. unfold map_rel in *.
  intro q. specialize (Hrel q). unfold put_fun, get_fun, get_list.
  induction xs as [|[k' v'] tl IH]; simpl.
  - destruct (Z.eq_dec q k); reflexivity.
  - destruct (Z.eq_dec k k').
    + subst k'. destruct (Z.eq_dec q k); reflexivity.
    + destruct (Z.eq_dec q k'); [reflexivity |]. simpl. apply IH.
Qed.

Lemma height_rel_empty : height_rel Empty SNil.
Proof.
  unfold height_rel. reflexivity.
Qed.

Lemma height_rel_push : forall (x : Z) (s : stack_abs) (l : stack_list),
  height_rel s l -> height_rel (Push x s) (SCons x l).
Proof.
  intros x s l H. unfold height_rel in *. simpl. rewrite H. reflexivity.
Qed.

End Answers.
