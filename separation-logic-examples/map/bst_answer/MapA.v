(** * Representation-Independent Finite-Map Specification *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From map.bst_answer Require Export MapHeader.

Definition amap : Type := gmap nat nat.

(** One authoritative ghost map records the abstract contents associated with
    every live map handle.  Clients hold one exclusive element fragment per
    handle. *)
Class mapGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] map_modelG :: ghost_mapG Γ loc amap;
}.

Class mapGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] mapGS_pre :: mapGpreS;
  map_name : gname;
}.

Definition mapΓ : HRA := ##[ghost_mapΣ loc amap].

Global Instance subG_mapGpreS
    `{!crisG Γ Σ α β τ _S _I} :
  subG mapΓ Γ → mapGpreS.
Proof. solve_inG. Defined.

Local Existing Instances mapGS_pre map_modelG.

(** Lift the resource from CRIS's discrete ghost signature [Γ] into the
    ambient simulation logic [Σ]. *)
Global Instance map_modelGS
    `{!crisG Γ Σ α β τ _S _I, !mapGS} :
  ghost_mapG Σ loc amap :=
  @subHG_ghost_map loc loc_eq_dec loc_countable amap Γ Σ
    (subG_subHG Γ Σ _S) map_modelG.

Section resources.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS}.

  (** Exclusive ownership of map handle [r] with mathematical contents [m]. *)
  Definition is_map (r : loc) (m : amap) : iProp Σ :=
    ghost_map_elem map_name r (DfracOwn 1) m.
End resources.

Module MapA. Section MapA.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS}.

  Definition new_map_spec : fspec :=
    fspec_simple
      (λ _ : unit,
        ((λ arg, ⌜arg = tt↑⌝),
         (λ ret, ∃ r, ⌜ret = r↑⌝ ∗ is_map r ∅)))%I.

  Definition insert_spec : fspec :=
    fspec_simple
      (λ '(r, m, k, v),
        ((λ arg, ⌜arg = (r, (k, v))↑⌝ ∗ is_map r m),
         (λ ret, ⌜ret = tt↑⌝ ∗ is_map r (<[k := v]> m))))%I.

  Definition delete_spec : fspec :=
    fspec_simple
      (λ '(r, m, k),
        ((λ arg, ⌜arg = (r, k)↑⌝ ∗ is_map r m),
         (λ ret, ⌜ret = tt↑⌝ ∗ is_map r (delete k m))))%I.

  Definition get_spec : fspec :=
    fspec_simple
      (λ '(r, m, k),
        ((λ arg, ⌜arg = (r, k)↑⌝ ∗ is_map r m),
         (λ ret, ⌜ret = (m !! k)↑⌝ ∗ is_map r m)))%I.

  Definition sp : specmap :=
    {[fid MapHdr.new_map @ new_map_spec;
      fid MapHdr.insert @ insert_spec;
      fid MapHdr.delete @ delete_spec;
      fid MapHdr.get @ get_spec]}.

  Definition scopes : list string := ["Map"].

  Definition fnsems : fnsemmap :=
    {[fid MapHdr.new_map #
        (msk_scp scopes msk_true,
          (fsp_some new_map_spec, fbody_trivial));
      fid MapHdr.insert #
        (msk_scp scopes msk_true,
          (fsp_some insert_spec, fbody_trivial));
      fid MapHdr.delete #
        (msk_scp scopes msk_true,
          (fsp_some delete_spec, fbody_trivial));
      fid MapHdr.get #
        (msk_scp scopes msk_true,
          (fsp_some get_spec, fbody_trivial))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition auth_init : iProp Σ :=
    ghost_map_auth map_name 1 (∅ : gmap loc amap).

  Definition init_cond : iProp Σ := auth_init.

  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End MapA. End MapA.

(** Allocate the initially empty authoritative handle registry. *)
Lemma map_alloc
    `{!crisG Γ Σ α β τ _S _I, !mapGpreS} :
  ⊢ o=> ∃ (_ : mapGS), MapA.init_cond.
Proof.
  iMod (ghost_map_alloc_empty (K := loc) (V := amap))
    as (γ) "AUTH".
  pose (Hmap := {|
    mapGS_pre := _;
    map_name := γ
  |}).
  iExists Hmap. rewrite /MapA.init_cond /MapA.auth_init.
  iModIntro. cbn. iExact "AUTH".
Qed.
