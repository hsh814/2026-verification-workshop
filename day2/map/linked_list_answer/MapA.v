(** * Separation-Logic Specification of Maps *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From map.linked_list_answer Require Export MapHeader.

(** The outer ghost map associates every allocated map handle with its
    mathematical finite-map model.  Full element ownership is the public
    abstract predicate [is_map]. *)
Class mapGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] map_modelG :: ghost_mapG Γ loc (gmap nat nat);
}.

Class mapGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] mapGS_pre :: mapGpreS;
  map_model_name : gname;
}.

Definition mapΓ : HRA :=
  ##[ghost_mapΣ loc (gmap nat nat)].

Global Instance subG_mapGpreS
    `{!crisG Γ Σ α β τ _S _I} :
  subG mapΓ Γ → mapGpreS.
Proof. solve_inG. Defined.

Local Existing Instances mapGS_pre map_modelG.

Global Instance map_modelGS
    `{!crisG Γ Σ α β τ _S _I, !mapGS} :
  ghost_mapG Σ loc (gmap nat nat) :=
  @subHG_ghost_map loc loc_eq_dec loc_countable (gmap nat nat) Γ Σ
    (subG_subHG Γ Σ _S) map_modelG.

Section resources.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS}.

  Definition map_auth (models : gmap loc (gmap nat nat)) : iProp Σ :=
    ghost_map_auth map_model_name 1 models.

  Definition is_map (handle : loc) (model : gmap nat nat) : iProp Σ :=
    ghost_map_elem map_model_name handle (DfracOwn 1) model.
End resources.

Module MapA. Section MapA.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS}.

  Definition new_map_spec : fspec :=
    fspec_simple
      (λ _ : unit,
        ((λ arg, ⌜arg = tt↑⌝),
         (λ ret,
            ∃ handle,
              ⌜ret = handle↑⌝ ∗
              is_map handle (∅ : gmap nat nat))))%I.

  Definition insert_spec : fspec :=
    fspec_simple
      (λ '(handle, model, key, value),
        ((λ arg,
            ⌜arg = (handle, (key, value))↑⌝ ∗
            is_map handle model),
         (λ ret,
            ⌜ret = tt↑⌝ ∗
            is_map handle (<[key := value]> model))))%I.

  Definition delete_spec : fspec :=
    fspec_simple
      (λ '(handle, model, key),
        ((λ arg,
            ⌜arg = (handle, key)↑⌝ ∗
            is_map handle model),
         (λ ret,
            ⌜ret = tt↑⌝ ∗
            is_map handle (delete key model))))%I.

  Definition get_spec : fspec :=
    fspec_simple
      (λ '(handle, model, key),
        ((λ arg,
            ⌜arg = (handle, key)↑⌝ ∗
            is_map handle model),
         (λ ret,
            ⌜ret = (model !! key)↑⌝ ∗
            is_map handle model)))%I.

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
    map_auth (∅ : gmap loc (gmap nat nat)).

  Definition init_cond : iProp Σ := auth_init.

  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End MapA. End MapA.

Lemma map_alloc
    `{!crisG Γ Σ α β τ _S _I, !mapGpreS} :
  ⊢ o=> ∃ (_ : mapGS), MapA.init_cond.
Proof.
  iMod (ghost_map_alloc_empty
    (K := loc) (V := gmap nat nat)) as (γ) "AUTH".
  pose (Hmap := {|
    mapGS_pre := _;
    map_model_name := γ
  |}).
  iExists Hmap. rewrite /MapA.init_cond /MapA.auth_init /map_auth.
  iModIntro. cbn. iExact "AUTH".
Qed.
