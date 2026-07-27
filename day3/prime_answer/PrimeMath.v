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
(** The implementation is between two consecutive primes.  The special
    case at zero makes the initial loop state [(2, 0)] immediate. *)
Definition candidate_window (count candidate : nat) : Prop :=
  match count with
  | 0 => candidate = 2
  | S previous =>
      nth_prime previous < candidate <= nth_prime count
  end.

Definition has_divisorb (candidate : nat) (values : list nat) : bool :=
  existsb (fun divisor => Nat.eqb (candidate mod divisor) 0) values.

Lemma has_divisorb_true candidate values :
  has_divisorb candidate values = true <->
    exists divisor,
      In divisor values /\ candidate mod divisor = 0.
Proof.
  unfold has_divisorb. induction values as [|value values IH]; simpl.
  - split.
    + discriminate.
    + intros HAS. destruct HAS as (divisor & IN & DIVIDES).
      inversion IN.
  - rewrite Bool.orb_true_iff, Nat.eqb_eq, IH.
    split.
    + intros [DIVIDES | [divisor [IN DIVIDES]]].
      * exists value. auto.
      * exists divisor. auto.
    + intros [divisor [[<- | IN] DIVIDES]].
      * auto.
      * right. exists divisor. auto.
Qed.

Lemma has_divisorb_false candidate values :
  has_divisorb candidate values = false <->
    forall divisor,
      In divisor values -> candidate mod divisor <> 0.
Proof.
  rewrite <- Bool.not_true_iff_false, has_divisorb_true.
  firstorder.
Qed.

Lemma first_primes_desc_prime count prime :
  In prime (first_primes_desc count) -> is_prime prime.
Proof.
  induction count as [|count IH]; simpl.
  - contradiction.
  - intros [<- | IN].
    + apply nth_prime_is_prime.
    + apply IH. exact IN.
Qed.

Lemma first_primes_desc_le_last count prime :
  In prime (first_primes_desc (S count)) ->
  prime <= nth_prime count.
Proof.
  induction count as [|count IH]; simpl.
  - intros [<- | []]. lia.
  - intros [<- | IN].
    + lia.
    + apply IH in IN. pose proof (nth_prime_strict count).
      change (prime <= nth_prime (S count)). lia.
Qed.

Lemma prime_below_nth_in_desc count prime :
  is_prime prime ->
  prime < nth_prime count ->
  In prime (first_primes_desc count).
Proof.
  intros PRIME. induction count as [|count IH]; intros BELOW.
  - rewrite nth_prime_zero in BELOW.
    pose proof (prime_ge_two prime PRIME). lia.
  - simpl. destruct (Nat.lt_trichotomy prime (nth_prime count))
      as [LT | [EQ | GT]].
    + right. apply IH. exact LT.
    + left. symmetry. exact EQ.
    + pose proof (next_prime_min (nth_prime count) prime GT PRIME).
      simpl in BELOW. lia.
Qed.

Lemma candidate_window_ge_two count candidate :
  candidate_window count candidate -> 2 <= candidate.
Proof.
  destruct count as [|count]; simpl; intros WINDOW.
  - lia.
  - pose proof (nth_prime_is_prime count) as PRIME.
    apply prime_ge_two in PRIME. lia.
Qed.

Lemma candidate_window_le_nth count candidate :
  candidate_window count candidate -> candidate <= nth_prime count.
Proof.
  destruct count as [|count]; intros WINDOW.
  - rewrite WINDOW, nth_prime_zero. lia.
  - exact (proj2 WINDOW).
Qed.

Lemma first_primes_desc_lt_candidate count candidate prime :
  candidate_window count candidate ->
  In prime (first_primes_desc count) ->
  prime < candidate.
Proof.
  destruct count as [|count]; simpl; intros WINDOW IN.
  - contradiction.
  - apply first_primes_desc_le_last in IN. lia.
Qed.

Lemma divisor_found_not_prime count candidate :
  candidate_window count candidate ->
  has_divisorb candidate (first_primes_desc count) = true ->
  ~ is_prime candidate.
Proof.
  intros WINDOW HAS PRIME.
  apply has_divisorb_true in HAS.
  destruct HAS as [divisor [IN MOD]].
  pose proof (first_primes_desc_prime count divisor IN) as DIVISOR_PRIME.
  pose proof
    (first_primes_desc_lt_candidate count candidate divisor WINDOW IN)
    as BELOW.
  apply primeb_spec in PRIME. destruct PRIME as [_ NO_DIVISOR].
  apply (NO_DIVISOR divisor).
  - split.
    + apply prime_ge_two. exact DIVISOR_PRIME.
    + exact BELOW.
  - apply Nat.Lcm0.mod_divide.
    exact MOD.
Qed.

Lemma no_divisor_found_prime count candidate :
  candidate_window count candidate ->
  has_divisorb candidate (first_primes_desc count) = false ->
  is_prime candidate.
Proof.
  intros WINDOW HAS.
  pose proof (candidate_window_ge_two count candidate WINDOW) as GE_TWO.
  destruct (prime_or_factor candidate GE_TWO) as [PRIME | FACTOR].
  - exact PRIME.
  - exfalso. destruct FACTOR as [factor [[FACTOR_GE FACTOR_LT] DIVIDES]].
    destruct (prime_divisor factor FACTOR_GE)
      as [prime [PRIME PRIME_DIVIDES]].
    assert (PRIME_DIVIDES_CANDIDATE : Nat.divide prime candidate).
    { eapply Nat.divide_trans; eauto. }
    assert (PRIME_LT_NTH : prime < nth_prime count).
    { pose proof
        (candidate_window_le_nth count candidate WINDOW) as CANDIDATE_LE.
      pose proof
        (Nat.divide_pos_le prime factor ltac:(lia) PRIME_DIVIDES).
      lia. }
    pose proof
      (prime_below_nth_in_desc count prime PRIME PRIME_LT_NTH) as IN.
    pose proof
      (proj1 (has_divisorb_false candidate (first_primes_desc count)) HAS)
      as NO_MOD.
    specialize (NO_MOD prime IN).
    apply NO_MOD, Nat.Lcm0.mod_divide.
    exact PRIME_DIVIDES_CANDIDATE.
Qed.

Lemma candidate_prime_eq count candidate :
  candidate_window count candidate ->
  is_prime candidate ->
  candidate = nth_prime count.
Proof.
  destruct count as [|count]; intros WINDOW PRIME.
  - rewrite WINDOW, nth_prime_zero. reflexivity.
  - simpl in WINDOW |- *. pose proof
      (next_prime_min (nth_prime count) candidate
        (proj1 WINDOW) PRIME).
    lia.
Qed.

Lemma divisor_found_window_step count candidate :
  candidate_window count candidate ->
  has_divisorb candidate (first_primes_desc count) = true ->
  candidate_window count (S candidate).
Proof.
  destruct count as [|count]; simpl; intros WINDOW HAS.
  - discriminate.
  - pose proof
      (divisor_found_not_prime (S count) candidate WINDOW HAS)
      as NOT_PRIME.
    assert (candidate <> nth_prime (S count)).
    { intros ->. apply NOT_PRIME, nth_prime_is_prime. }
    change (candidate <> next_prime (nth_prime count)) in H.
    lia.
Qed.

Lemma no_divisor_found_window_step count candidate :
  candidate_window count candidate ->
  has_divisorb candidate (first_primes_desc count) = false ->
  candidate_window (S count) (S candidate).
Proof.
  intros WINDOW HAS.
  pose proof (no_divisor_found_prime count candidate WINDOW HAS) as PRIME.
  pose proof (candidate_prime_eq count candidate WINDOW PRIME) as ->.
  simpl. pose proof (nth_prime_strict count).
  change (nth_prime count < next_prime (nth_prime count)) in H.
  lia.
Qed.

Lemma nth_prime_mono lower upper :
  lower <= upper -> nth_prime lower <= nth_prime upper.
Proof.
  intros LE. induction LE.
  - reflexivity.
  - eapply Nat.le_trans.
    + exact IHLE.
    + apply Nat.lt_le_incl, nth_prime_strict.
Qed.

(** A finite variant for the outer implementation loop.  The first term
    counts prime indices still to visit; the second counts candidates left
    before the prime at the current index. *)
Definition search_measure
    (wanted found candidate : nat) : nat :=
  (wanted - found) * S (nth_prime wanted) +
  (nth_prime found - candidate).

Lemma divisor_found_measure_decreases wanted found candidate :
  found <= wanted ->
  candidate_window found candidate ->
  has_divisorb candidate (first_primes_desc found) = true ->
  search_measure wanted found (S candidate) <
  search_measure wanted found candidate.
Proof.
  intros FOUND_LE WINDOW HAS.
  pose proof
    (divisor_found_not_prime found candidate WINDOW HAS) as NOT_PRIME.
  pose proof
    (candidate_window_le_nth found candidate WINDOW) as CANDIDATE_LE.
  assert (candidate < nth_prime found).
  { destruct (Nat.eq_dec candidate (nth_prime found)) as [EQUAL | NE].
    - subst candidate. exfalso. apply NOT_PRIME, nth_prime_is_prime.
    - lia. }
  unfold search_measure. lia.
Qed.

Lemma no_divisor_found_measure_decreases wanted found candidate :
  found < wanted ->
  candidate_window found candidate ->
  has_divisorb candidate (first_primes_desc found) = false ->
  search_measure wanted (S found) (S candidate) <
  search_measure wanted found candidate.
Proof.
  intros FOUND_LT WINDOW HAS.
  pose proof (no_divisor_found_prime found candidate WINDOW HAS) as PRIME.
  pose proof (candidate_prime_eq found candidate WINDOW PRIME) as CANDIDATE.
  pose proof (nth_prime_mono (S found) wanted ltac:(lia)) as PRIME_LE.
  unfold search_measure. subst candidate.
  assert (wanted - found = S (wanted - S found)) by lia.
  nia.
Qed.
