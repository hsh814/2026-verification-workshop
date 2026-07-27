(** * Template: Representation-Independent Map Specification

    Fill this file with the common specification before choosing a concrete
    representation.  The suggested scaffold uses one high-level [ghost_map]
    from handles to mathematical maps. *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From map.try Require Export MapHeader.

Definition amap : Type := gmap nat nat.

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
  subG mapΓ Γ -> mapGpreS.
Proof. solve_inG. Defined.

Local Existing Instances mapGS_pre map_modelG.

Global Instance map_modelGS
    `{!crisG Γ Σ α β τ _S _I, !mapGS} :
  ghost_mapG Σ loc amap :=
  @subHG_ghost_map loc loc_eq_dec loc_countable amap Γ Σ
    (subG_subHG Γ Σ _S) map_modelG.

Section resources.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS}.

  (** TODO: define exclusive ownership of handle [r] with model [m]. *)
  Definition is_map (r : loc) (m : amap) : iProp Σ.
  Admitted.
End resources.

Module MapA. Section MapA.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS}.

  (** TODO: specify the four operations over [gmap nat nat]. *)
  Definition new_map_spec : fspec.
  Admitted.

  Definition insert_spec : fspec.
  Admitted.

  Definition delete_spec : fspec.
  Admitted.

  Definition get_spec : fspec.
  Admitted.

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

(** TODO: allocate the authoritative empty handle registry. *)
Lemma map_alloc
    `{!crisG Γ Σ α β τ _S _I, !mapGpreS} :
  ⊢ o=> ∃ (_ : mapGS), MapA.init_cond.
Admitted.
