(** * Exercise 2: Fractional Points-to Resources

    The operation specifications below are supplied.  Complete the resource
    definition and its elementary fractional laws, then allocate the initial
    ghost state.  Use [ghost_map] and [mono_nat] only through their high-level
    APIs; do not unfold them into direct [own] expressions. *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From iris.bi.lib Require Import fractional.
From lib Require Import mono_nat.
From refcell.frac_mem Require Export FracMemHeader.

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
  subG frac_memΓ Γ -> frac_memGpreS.
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

  (** TODO 2(a): represent fraction [q] of cell [l] with
      [ghost_map_elem], [DfracOwn q], and [frac_mem_map_name]. *)
  Definition pointsto (l : loc) (q : Qp) (v : memval) : iProp Σ.
  Admitted.

  (** TODO 2(b): register the standard proof-mode split/merge instances. *)
  Global Instance pointsto_fractional l v :
    Fractional (fun q => pointsto l q v).
  Admitted.

  Global Instance pointsto_as_fractional l q v :
    AsFractional (pointsto l q v) (fun q => pointsto l q v) q.
  Admitted.

  (** TODO 2(c): state the split and merge rule explicitly. *)
  Lemma pointsto_split_merge l v q1 q2 :
    pointsto l (q1 + q2)%Qp v ⊣⊢
      pointsto l q1 v ∗ pointsto l q2 v.
  Admitted.

  (** TODO 2(d): two shares at one location agree on their value and their
      fractions cannot add up to more than one. *)
  Lemma pointsto_agree_valid l q1 q2 v1 v2 :
    pointsto l q1 v1 -∗
    pointsto l q2 v2 -∗
    ⌜v1 = v2 ∧ (q1 + q2 ≤ 1)%Qp⌝.
  Admitted.

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

  (** The specifications are part of the exercise statement.  Notice that
      only [load] quantifies over an arbitrary fraction. *)
  Definition alloc_spec : fspec :=
    fspec_simple
      (fun _ : unit =>
        ((fun arg => ⌜arg = tt↑⌝),
         (fun ret => ∃ l, ⌜ret = l↑⌝ ∗ l ↦ Vundef)))%I.

  Definition load_spec : fspec :=
    fspec_simple
      (fun '(l, q, v) =>
        ((fun arg => ⌜arg = l↑⌝ ∗ l ↦{q} v),
         (fun ret => ⌜ret = v↑⌝ ∗ l ↦{q} v)))%I.

  Definition store_spec : fspec :=
    fspec_simple
      (fun '(l, old, new) =>
        ((fun arg => ⌜arg = (l, new)↑⌝ ∗ l ↦ old),
         (fun ret => ⌜ret = tt↑⌝ ∗ l ↦ new)))%I.

  Definition get_cnt_spec : fspec :=
    fspec_simple
      (fun lower =>
        ((fun arg => ⌜arg = tt↑⌝ ∗ count_snapshot lower),
         (fun ret =>
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
    (ghost_map_auth frac_mem_map_name 1
       (∅ : gmap loc memval) ∗
     mono_nat_auth_own frac_mem_count_name 1 0)%I.

  Definition frag_init : iProp Σ := count_snapshot 0.
  Definition init_cond : iProp Σ := (frag_init ∗ auth_init)%I.

  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End FracMemA. End FracMemA.

(** TODO 2(e): allocate the empty authoritative memory map and the counter,
    package their names in [frac_memGS], and return the initial snapshot. *)
Lemma frac_mem_alloc
    `{!crisG Γ Σ α β τ _S _I, !frac_memGpreS} :
  ⊢ o=> ∃ (_ : frac_memGS), FracMemA.init_cond.
Admitted.
