(** Ghost state for a monotonically increasing nat, wrapping the [mono_natR]
RA. Provides an authoritative proposition [mono_nat_auth_own γ q n] for the
underlying number [n] and a persistent proposition [mono_nat_lb_own γ m]
witnessing that the authoritative nat is at least [m].

The key rules are [mono_nat_lb_own_valid], which asserts that an auth at [n]
and a lower-bound at [m] imply that [m ≤ n], and [mono_nat_own_update], which
allows one to increase the auth element. At any time the auth nat can be
"snapshotted" with [mono_nat_lb_own_get] to produce a persistent lower-bound
proposition. *)
From iris.proofmode Require Import proofmode.
From iris.algebra.lib Require Import mono_nat.
From iris.bi.lib Require Import fractional.
From CRIS.iris_system Require Export own.
From iris.prelude Require Import options.

Class mono_natG (Σ : GRA) :=
  MonoNatG { #[local] mono_natG_inG :: inG mono_natR Σ; }.

Definition mono_natΣ : GRA := #[ mono_natR ].
Global Instance subG_mono_natΣ Σ : subG mono_natΣ Σ → mono_natG Σ.
Proof. solve_inG. Qed.

Global Opaque mono_natΣ.

Local Definition mono_nat_auth_own_def `{!mono_natG Σ}
    (γ : gname) (q : Qp) (n : nat) : iProp Σ :=
  own γ (●MN{#q} n).
Local Definition mono_nat_auth_own_aux : seal (@mono_nat_auth_own_def).
Proof. by eexists. Qed.
Definition mono_nat_auth_own := mono_nat_auth_own_aux.(unseal).
Local Definition mono_nat_auth_own_unseal :
  @mono_nat_auth_own = @mono_nat_auth_own_def :=
  mono_nat_auth_own_aux.(seal_eq).
Global Arguments mono_nat_auth_own {Σ _} γ q n.

Local Definition mono_nat_lb_own_def `{!mono_natG Σ}
    (γ : gname) (n : nat) : iProp Σ :=
  own γ (◯MN n).
Local Definition mono_nat_lb_own_aux : seal (@mono_nat_lb_own_def).
Proof. by eexists. Qed.
Definition mono_nat_lb_own := mono_nat_lb_own_aux.(unseal).
Local Definition mono_nat_lb_own_unseal :
  @mono_nat_lb_own = @mono_nat_lb_own_def :=
  mono_nat_lb_own_aux.(seal_eq).
Global Arguments mono_nat_lb_own {Σ _} γ n.

Local Ltac unseal := rewrite
  ?mono_nat_auth_own_unseal /mono_nat_auth_own_def
  ?mono_nat_lb_own_unseal /mono_nat_lb_own_def.

Section mono_nat.
  Context `{!mono_natG Σ}.
  Implicit Types (n m : nat).

  Global Instance mono_nat_auth_own_timeless γ q n :
    Timeless (mono_nat_auth_own γ q n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_nat_lb_own_timeless γ n :
    Timeless (mono_nat_lb_own γ n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_nat_lb_own_persistent γ n :
    Persistent (mono_nat_lb_own γ n).
  Proof. unseal. apply _. Qed.

  Global Instance mono_nat_auth_own_fractional γ n :
    Fractional (λ q, mono_nat_auth_own γ q n).
  Proof.
    unseal. intros p q.
    rewrite -own_op -mono_nat_auth_dfrac_op //.
  Qed.
  Global Instance mono_nat_auth_own_as_fractional γ q n :
    AsFractional
      (mono_nat_auth_own γ q n) (λ q, mono_nat_auth_own γ q n) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma mono_nat_auth_own_agree γ q1 q2 n1 n2 :
    mono_nat_auth_own γ q1 n1 -∗
    mono_nat_auth_own γ q2 n2 -∗
    ⌜(q1 + q2 ≤ 1)%Qp ∧ n1 = n2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iCombine "H1 H2" gives %?%mono_nat_auth_dfrac_op_valid; done.
  Qed.
  Lemma mono_nat_auth_own_exclusive γ n1 n2 :
    mono_nat_auth_own γ 1 n1 -∗
    mono_nat_auth_own γ 1 n2 -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (mono_nat_auth_own_agree with "H1 H2") as %[[] _].
  Qed.

  Lemma mono_nat_lb_own_valid γ q n m :
    mono_nat_auth_own γ q n -∗
    mono_nat_lb_own γ m -∗
    ⌜(q ≤ 1)%Qp ∧ m ≤ n⌝.
  Proof.
    unseal. iIntros "Hauth Hlb".
    iCombine "Hauth Hlb" gives %Hvalid%mono_nat_both_dfrac_valid.
    auto.
  Qed.

  (** The conclusion of this lemma is persistent; the proof mode preserves
  [mono_nat_auth_own] when the conclusion is introduced into the persistent
  context. *)
  Lemma mono_nat_lb_own_get γ q n :
    mono_nat_auth_own γ q n -∗ mono_nat_lb_own γ n.
  Proof. unseal. iApply own_mono. apply mono_nat_included. Qed.

  Lemma mono_nat_lb_own_le {γ n} n' :
    n' ≤ n →
    mono_nat_lb_own γ n -∗ mono_nat_lb_own γ n'.
  Proof.
    unseal. intros.
    iApply own_mono. by apply mono_nat_lb_mono.
  Qed.

  (** CRIS allocation uses [o=>], which carries the allocation authority. *)
  Lemma mono_nat_own_alloc n :
    ⊢ o=> ∃ γ, mono_nat_auth_own γ 1 n ∗ mono_nat_lb_own γ n.
  Proof.
    unseal. setoid_rewrite <- own_op.
    by apply own_alloc, mono_nat_both_valid.
  Qed.

  Lemma mono_nat_own_update {γ n} n' :
    n ≤ n' →
    mono_nat_auth_own γ 1 n ==∗
      mono_nat_auth_own γ 1 n' ∗ mono_nat_lb_own γ n'.
  Proof.
    iIntros (?) "Hauth".
    iAssert (mono_nat_auth_own γ 1 n') with "[> Hauth]" as "Hauth".
    { unseal. iApply (own_update with "Hauth").
      by apply mono_nat_update. }
    iModIntro. iSplit; [done|].
    by iApply mono_nat_lb_own_get.
  Qed.
End mono_nat.

(** Iris also provides [mono_nat_own_alloc_strong] and
[mono_nat_lb_own_0]. CRIS currently has no counterparts of
[own_alloc_strong] and [own_unit], respectively, so those two rules cannot be
ported without changing CRIS's ownership model. *)

From CRIS.iris_system Require Import sProp.

Global Instance subG_mono_natΓ {Γ : HRA} :
  subG mono_natΣ Γ → mono_natG Γ.
Proof. solve_inG. Qed.

Global Instance subHG_mono_nat {Γ Σ} :
  subHG Γ Σ → mono_natG Γ → mono_natG Σ.
Proof. intros ? []. constructor. apply _. Defined.

(* Ideally automatic, but unification of [HRA] and [GRA] is problematic. *)
Local Instance inGΓ_mono_nat {Γ : HRA} :
  mono_natG Γ → inG mono_natR Γ.
Proof. intros [Hin]. exact Hin. Defined.

Section syn_mono_nat.
  Context `{!subHG Γ Σ, !STτ.t τ, !SL.synG Γ τ α,
    semG0 : !SL.semG Γ τ α Σ β}.
  Context `{MN : !mono_natG Γ}.
  Implicit Types (γ : gname) (n : nat).

  Definition syn_mono_nat_auth_own {k} γ (q : Qp) n : GTerm.t k :=
    sown γ (●MN{#q} n).

  Definition syn_mono_nat_lb_own {k} γ n : GTerm.t k :=
    sown γ (◯MN n).

  Global Instance mono_nat_auth_own_red k γ q n :
    SLRed k
      (syn_mono_nat_auth_own γ q n)
      (mono_nat_auth_own γ q n).
  Proof using semG0.
    rewrite mono_nat_auth_own_unseal.
    solve_sl_red. by destruct MN.
  Qed.

  Global Instance mono_nat_lb_own_red k γ n :
    SLRed k (syn_mono_nat_lb_own γ n) (mono_nat_lb_own γ n).
  Proof using semG0.
    rewrite mono_nat_lb_own_unseal.
    solve_sl_red. by destruct MN.
  Qed.
End syn_mono_nat.
