(** * Separation-Logic Specification of Memory *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From lib Require Import mono_nat.
From mem_answer Require Export MemHeader.

(** [ghost_map] records the contents of every allocated cell.  [mono_nat]
    records the monotonically increasing number of loads and stores. *)
Class memGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] mem_mapG :: ghost_mapG Γ loc memval;
  #[local] mem_countG :: mono_natG Γ;
}.

Class memGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] memGS_pre :: memGpreS;
  mem_map_name : gname;
  mem_count_name : gname;
}.

Definition memΓ : HRA :=
  ##[ghost_mapΣ loc memval; mono_natΣ].

Global Instance subG_memGpreS
    `{!crisG Γ Σ α β τ _S _I} :
  subG memΓ Γ → memGpreS.
Proof. solve_inG. Defined.

Local Existing Instances memGS_pre mem_mapG mem_countG.

Global Instance mem_mapGS
    `{!crisG Γ Σ α β τ _S _I, !memGS} :
  ghost_mapG Σ loc memval :=
  @subHG_ghost_map loc loc_eq_dec loc_countable memval Γ Σ
    (subG_subHG Γ Σ _S) mem_mapG.

Global Instance mem_countGS
    `{!crisG Γ Σ α β τ _S _I, !memGS} :
  mono_natG Σ :=
  @subHG_mono_nat Γ Σ (subG_subHG Γ Σ _S) mem_countG.

Section resources.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  (** Exclusive ownership of one logical memory cell. *)
  Definition pointsto (l : loc) (v : memval) : iProp Σ :=
    ghost_map_elem mem_map_name l (DfracOwn 1) v.

  (** A persistent observation that the access count was at least [n]. *)
  Definition count_snapshot (n : nat) : iProp Σ :=
    mono_nat_lb_own mem_count_name n.

  Global Instance count_snapshot_persistent n :
    Persistent (count_snapshot n).
  Proof. apply _. Qed.
End resources.

Reserved Notation "l ↦ v" (at level 20, format "l  ↦  v").
Notation "l ↦ v" := (pointsto l v) : bi_scope.

Module MemA. Section MemA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Definition alloc_spec : fspec :=
    fspec_simple
      (λ _ : unit,
        ((λ arg, ⌜arg = tt↑⌝),
         (λ ret, ∃ l, ⌜ret = l↑⌝ ∗ l ↦ Vundef)))%I.

  Definition load_spec : fspec :=
    fspec_simple
      (λ '(l, v),
        ((λ arg, ⌜arg = l↑⌝ ∗ l ↦ v),
         (λ ret, ⌜ret = v↑⌝ ∗ l ↦ v)))%I.

  Definition store_spec : fspec :=
    fspec_simple
      (λ '(l, old, new),
        ((λ arg, ⌜arg = (l, new)↑⌝ ∗ l ↦ old),
         (λ ret, ⌜ret = tt↑⌝ ∗ l ↦ new)))%I.

  (** A caller supplies any persistent earlier snapshot.  The result comes
      with a new snapshot and the pure fact that the count did not decrease. *)
  Definition get_cnt_spec : fspec :=
    fspec_simple
      (λ lower,
        ((λ arg, ⌜arg = tt↑⌝ ∗ count_snapshot lower),
         (λ ret,
            ∃ current,
              ⌜ret = current↑ ∧ lower ≤ current⌝ ∗
              count_snapshot current)))%I.

  Definition sp : specmap :=
    {[fid MemHdr.alloc @ alloc_spec;
      fid MemHdr.load @ load_spec;
      fid MemHdr.store @ store_spec;
      fid MemHdr.get_cnt @ get_cnt_spec]}.

  Definition scopes : list string := ["Mem"].

  Definition fnsems : fnsemmap :=
    {[fid MemHdr.alloc #
        (msk_scp scopes msk_true,
          (fsp_some alloc_spec, fbody_trivial));
      fid MemHdr.load #
        (msk_scp scopes msk_true,
          (fsp_some load_spec, fbody_trivial));
      fid MemHdr.store #
        (msk_scp scopes msk_true,
          (fsp_some store_spec, fbody_trivial));
      fid MemHdr.get_cnt #
        (msk_scp scopes msk_true,
          (fsp_some get_cnt_spec, fbody_trivial))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition auth_init : iProp Σ :=
    (ghost_map_auth mem_map_name 1 (∅ : gmap loc memval) ∗
     mono_nat_auth_own mem_count_name 1 0)%I.

  Definition frag_init : iProp Σ := count_snapshot 0.
  Definition init_cond : iProp Σ := (frag_init ∗ auth_init)%I.

  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End MemA. End MemA.

Lemma mem_alloc
    `{!crisG Γ Σ α β τ _S _I, !memGpreS} :
  ⊢ o=> ∃ (_ : memGS), MemA.init_cond.
Proof.
  iMod (ghost_map_alloc_empty (K := loc) (V := memval))
    as (γm) "MAP".
  iMod (mono_nat_own_alloc 0) as (γc) "[COUNT SNAP]".
  pose (Hmem := {|
    memGS_pre := _;
    mem_map_name := γm;
    mem_count_name := γc
  |}).
  iExists Hmem. rewrite /MemA.init_cond /MemA.frag_init
    /MemA.auth_init /count_snapshot. iModIntro. cbn.
  iCombine "MAP COUNT" as "AUTH".
  iCombine "SNAP AUTH" as "INIT".
  iExact "INIT".
Qed.
