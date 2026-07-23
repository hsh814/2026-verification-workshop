(** * Prime-related Definitions *)

(** Students don't have to understand the file fully,
    but should get used to how to use them for solving exercises. *)

From Stdlib Require Import Arith Bool Factorial Lia List.
From Stdlib Require Import Logic.ConstructiveEpsilon.
From Stdlib Require Import Logic.Classical_Prop.

Import ListNotations.

(** A deliberately small mathematical interface for the exercise.

    [is_prime p] is executable: it checks every possible proper divisor.
    [next_prime n] is a terminating linear search whose termination proof is
    supplied by Euclid's argument below.  Consequently [nth_prime] is both a
    genuine mathematical definition and close to the implementation students
    have to verify.  Indexing is zero based: [nth_prime 0 = 2]. *)

Definition primeb (p : nat) : bool :=
  (2 <=? p) &&
  forallb
    (fun d => negb (Nat.eqb (p mod d) 0))
    (seq 2 (p - 2)).

Definition is_prime (p : nat) : Prop := primeb p = true.

Lemma primeb_spec p :
  is_prime p <->
  2 <= p /\ forall d, 2 <= d < p -> ~ Nat.divide d p.
Proof.
  unfold is_prime, primeb.
  rewrite Bool.andb_true_iff, Nat.leb_le.
  split.
  - intros [LE ALL]. split.
    + exact LE.
    + intros d RANGE DIV.
    apply forallb_forall with (x := d) in ALL.
    2: { apply in_seq; lia. }
    rewrite Bool.negb_true_iff, Nat.eqb_neq in ALL.
    apply ALL, Nat.Lcm0.mod_divide.
    exact DIV.
  - intros [LE NODIV]. split.
    + exact LE.
    + apply forallb_forall. intros d IN.
    apply in_seq in IN.
    rewrite Bool.negb_true_iff, Nat.eqb_neq.
    intros MOD.
    apply (NODIV d).
    * lia.
    * apply Nat.Lcm0.mod_divide. exact MOD.
Qed.

(* Compute primeb 101. *)

Lemma prime_two : is_prime 2.
Proof. reflexivity. Qed.

Lemma prime_ge_two p : is_prime p -> 2 <= p.
Proof. intros PRIME. apply primeb_spec in PRIME. tauto. Qed.

Lemma prime_or_factor n :
  2 <= n ->
  is_prime n \/ exists d, 2 <= d < n /\ Nat.divide d n.
Proof.
  intros LE. destruct (bool_dec (primeb n) true) as [PRIME | NPRIME].
  - left. exact PRIME.
  - right. apply NNPP. intros NO_FACTOR. apply NPRIME, primeb_spec.
    split.
    + exact LE.
    + intros d RANGE DIV.
    apply NO_FACTOR. exists d. auto.
Qed.

Lemma prime_divisor n :
  2 <= n -> exists p, is_prime p /\ Nat.divide p n.
Proof.
  induction n using (well_founded_induction lt_wf).
  intros LE. destruct (prime_or_factor n LE) as [PRIME | [d [RANGE DIV]]].
  - exists n. split.
    + exact PRIME.
    + apply Nat.divide_refl.
  - destruct (H d) as [p [PRIME PDIV]]; try lia.
    exists p. split.
    + exact PRIME.
    + eapply Nat.divide_trans; eauto.
Qed.

Lemma divides_factorial d n :
  1 <= d -> d <= n -> Nat.divide d (fact n).
Proof.
  intros POS. induction n as [|n IH]; intros LE.
  - lia.
  - destruct (Nat.eq_dec d (S n)) as [-> | NE].
    + exists (fact n). simpl. lia.
    + destruct (IH ltac:(lia)) as [q EQ].
      exists (S n * q). simpl. nia.
Qed.

Lemma prime_after_exists k :
  exists p, k < p /\ is_prime p.
Proof.
  set (big := S (fact (S k))).
  assert (BIG : 2 <= big).
  { unfold big. pose proof (lt_O_fact (S k)). lia. }
  destruct (prime_divisor big BIG) as [p [PRIME PDIV]].
  exists p. split.
  - apply Nat.nle_gt. intros PLE.
    assert (PFACT : Nat.divide p (fact (S k))).
    { apply divides_factorial.
      - apply prime_ge_two in PRIME. lia.
      - lia. }
    assert (PONE : Nat.divide p (big - fact (S k))).
    { eapply Nat.divide_sub_r; eauto. }
    unfold big in PONE.
    replace (S (fact (S k)) - fact (S k)) with 1 in PONE by lia.
    apply Nat.divide_1_r in PONE.
    pose proof (prime_ge_two p PRIME). lia.
  - exact PRIME.
Qed.

Lemma prime_after_dec k p :
  {k < p /\ is_prime p} + {~ (k < p /\ is_prime p)}.
Proof.
  unfold is_prime.
  destruct (lt_dec k p), (bool_dec (primeb p) true);
    firstorder.
Defined.

Definition next_prime_witness (k : nat) :
  {p : nat |
    (k < p /\ is_prime p) /\
    forall q, k < q /\ is_prime q -> p <= q} :=
  @epsilon_smallest_direct
    (fun p => k < p /\ is_prime p)
    (prime_after_dec k)
    (prime_after_exists k).

Definition next_prime (k : nat) : nat :=
  proj1_sig (next_prime_witness k).

Lemma next_prime_spec k : k < next_prime k /\ is_prime (next_prime k).
Proof. exact (proj1 (proj2_sig (next_prime_witness k))). Qed.

Lemma next_prime_min k p :
  k < p -> is_prime p -> next_prime k <= p.
Proof.
  intros LT PRIME.
  exact (proj2 (proj2_sig (next_prime_witness k)) p (conj LT PRIME)).
Qed.

Lemma no_prime_between k p :
  k < p < next_prime k -> ~ is_prime p.
Proof.
  intros [LT BELOW] PRIME.
  pose proof (next_prime_min k p LT PRIME). lia.
Qed.

Fixpoint nth_prime (n : nat) : nat :=
  match n with
  | 0 => next_prime 1
  | S n' => next_prime (nth_prime n')
  end.

Lemma nth_prime_is_prime n : is_prime (nth_prime n).
Proof.
  destruct n; apply next_prime_spec.
Qed.

Lemma nth_prime_strict n : nth_prime n < nth_prime (S n).
Proof. simpl. apply next_prime_spec. Qed.

Lemma nth_prime_zero : nth_prime 0 = 2.
Proof.
  simpl. pose proof (next_prime_spec 1) as [LT PRIME].
  pose proof (next_prime_min 1 2 ltac:(lia) prime_two). lia.
Qed.

(** The linked list stores newest elements at its head. *)
Fixpoint first_primes_desc (count : nat) : list nat :=
  match count with
  | 0 => []
  | S count' => nth_prime count' :: first_primes_desc count'
  end.

Lemma first_primes_desc_length count :
  length (first_primes_desc count) = count.
Proof. induction count; simpl; lia. Qed.
