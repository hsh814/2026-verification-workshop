(** * Fractional-Permission Separation-Logic Specification of Memory *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From iris.bi.lib Require Import fractional.
From lib Require Import mono_nat.
From refcell.frac_mem_answer Require Export FracMemHeader.

(** [ghost_map] records the contents of every allocated cell.  Its element
    resource already combines discardable fractions with agreement on the
    stored value.  [mono_nat] records the access count. *)
Class frac_memGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] frac_mem_mapG :: ghost_mapG Γ loc memval;
  #[local] frac_mem_countG :: mono_natG Γ;
}.

Class frac_memGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] frac_memGS_pre :: frac_memGpreS;
  frac_mem_map_name : gname;
  frac_mem_count_name : gname;
}.

Definition frac_memΓ : HRA :=
  ##[ghost_mapΣ loc memval; mono_natΣ].

Global Instance subG_frac_memGpreS
    `{!crisG Γ Σ α β τ _S _I} :
  subG frac_memΓ Γ → frac_memGpreS.
Proof. solve_inG. Defined.

Local Existing Instances
  frac_memGS_pre frac_mem_mapG frac_mem_countG.

Global Instance frac_mem_mapGS
    `{!crisG Γ Σ α β τ _S _I, !frac_memGS} :
  ghost_mapG Σ loc memval :=
  @subHG_ghost_map loc loc_eq_dec loc_countable memval Γ Σ
    (subG_subHG Γ Σ _S) frac_mem_mapG.

Global Instance frac_mem_countGS
    `{!crisG Γ Σ α β τ _S _I, !frac_memGS} :
  mono_natG Σ :=
  @subHG_mono_nat Γ Σ (subG_subHG Γ Σ _S) frac_mem_countG.

Section resources.
  Context `{!crisG Γ Σ α β τ _S _I, !frac_memGS}.

  (** Fractional ownership of cell [l] containing [v].  Fractions are
      positive rationals; validity of the ghost resource enforces that the
      total ownership of one cell is at most one. *)
  Definition pointsto (l : loc) (q : Qp) (v : memval) : iProp Σ :=
    ghost_map_elem frac_mem_map_name l (DfracOwn q) v.

  Global Instance pointsto_fractional l v :
    Fractional (λ q, pointsto l q v).
  Proof. rewrite /pointsto. apply _. Qed.

  Global Instance pointsto_as_fractional l q v :
    AsFractional (pointsto l q v) (λ q, pointsto l q v) q.
  Proof. split; [done|apply _]. Qed.

  (** This equivalence is both the split and merge rule. *)
  Lemma pointsto_split_merge l v q1 q2 :
    pointsto l (q1 + q2)%Qp v ⊣⊢
      pointsto l q1 v ∗ pointsto l q2 v.
  Proof. exact (fractional q1 q2). Qed.

  (** Same-location shares agree on the value, and their combined fraction is
      valid. *)
  Lemma pointsto_agree_valid l q1 q2 v1 v2 :
    pointsto l q1 v1 -∗
    pointsto l q2 v2 -∗
    ⌜v1 = v2 ∧ (q1 + q2 ≤ 1)%Qp⌝.
  Proof.
    rewrite /pointsto. iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2")
      as %[Hvalid Hagree].
    rewrite dfrac_op_own dfrac_valid_own in Hvalid.
    iPureIntro. split; done.
  Qed.

  Definition count_snapshot (n : nat) : iProp Σ :=
    mono_nat_lb_own frac_mem_count_name n.

  Global Instance count_snapshot_persistent n :
    Persistent (count_snapshot n).
  Proof. apply _. Qed.
End resources.

Reserved Notation "l '↦{' q '}' v"
  (at level 20, q at level 1, format "l  ↦{ q }  v").
Reserved Notation "l ↦ v"
  (at level 20, format "l  ↦  v").

Notation "l ↦{ q } v" := (pointsto l q v) : bi_scope.
Notation "l ↦ v" := (pointsto l 1 v) : bi_scope.

Module FracMemA. Section FracMemA.
  Context `{!crisG Γ Σ α β τ _S _I, !frac_memGS}.

  Definition alloc_spec : fspec :=
    fspec_simple
      (λ _ : unit,
        ((λ arg, ⌜arg = tt↑⌝),
         (λ ret, ∃ l, ⌜ret = l↑⌝ ∗ l ↦ Vundef)))%I.

  Definition load_spec : fspec :=
    fspec_simple
      (λ '(l, q, v),
        ((λ arg, ⌜arg = l↑⌝ ∗ l ↦{q} v),
         (λ ret, ⌜ret = v↑⌝ ∗ l ↦{q} v)))%I.

  Definition store_spec : fspec :=
    fspec_simple
      (λ '(l, old, new),
        ((λ arg, ⌜arg = (l, new)↑⌝ ∗ l ↦ old),
         (λ ret, ⌜ret = tt↑⌝ ∗ l ↦ new)))%I.

  Definition get_cnt_spec : fspec :=
    fspec_simple
      (λ lower,
        ((λ arg, ⌜arg = tt↑⌝ ∗ count_snapshot lower),
         (λ ret,
            ∃ current,
              ⌜ret = current↑ ∧ lower ≤ current⌝ ∗
              count_snapshot current)))%I.

  Definition sp : specmap :=
    {[fid FracMemHdr.alloc @ alloc_spec;
      fid FracMemHdr.load @ load_spec;
      fid FracMemHdr.store @ store_spec;
      fid FracMemHdr.get_cnt @ get_cnt_spec]}.

  Definition scopes : list string := ["FracMem"].

  Definition fnsems : fnsemmap :=
    {[fid FracMemHdr.alloc #
        (msk_scp scopes msk_true,
          (fsp_some alloc_spec, fbody_trivial));
      fid FracMemHdr.load #
        (msk_scp scopes msk_true,
          (fsp_some load_spec, fbody_trivial));
      fid FracMemHdr.store #
        (msk_scp scopes msk_true,
          (fsp_some store_spec, fbody_trivial));
      fid FracMemHdr.get_cnt #
        (msk_scp scopes msk_true,
          (fsp_some get_cnt_spec, fbody_trivial))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition auth_init : iProp Σ :=
    (ghost_map_auth frac_mem_map_name 1 (∅ : gmap loc memval) ∗
     mono_nat_auth_own frac_mem_count_name 1 0)%I.

  Definition frag_init : iProp Σ := count_snapshot 0.
  Definition init_cond : iProp Σ := (frag_init ∗ auth_init)%I.

  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End FracMemA. End FracMemA.

Lemma frac_mem_alloc
    `{!crisG Γ Σ α β τ _S _I, !frac_memGpreS} :
  ⊢ o=> ∃ (_ : frac_memGS), FracMemA.init_cond.
Proof.
  iMod (ghost_map_alloc_empty (K := loc) (V := memval))
    as (γm) "MAP".
  iMod (mono_nat_own_alloc 0) as (γc) "[COUNT SNAP]".
  pose (Hmem := {|
    frac_memGS_pre := _;
    frac_mem_map_name := γm;
    frac_mem_count_name := γc
  |}).
  iExists Hmem. rewrite /FracMemA.init_cond /FracMemA.frag_init
    /FracMemA.auth_init /count_snapshot. iModIntro. cbn.
  iCombine "MAP COUNT" as "AUTH".
  iCombine "SNAP AUTH" as "INIT".
  iExact "INIT".
Qed.
