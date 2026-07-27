(** * Exercise 1: Write the Common Map Specification

    The ghost-state scaffold is supplied.  Define the client resource and
    specify all operations over [gmap nat nat].  Use the high-level
    [ghost_map] library, not a direct [own] expression. *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From map.linked_list Require Export MapHeader.

Class mapGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] map_modelG ::
    ghost_mapG Γ loc (gmap nat nat);
}.

Class mapGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] mapGS_pre :: mapGpreS;
  map_model_name : gname;
}.

Definition mapΓ : HRA :=
  ##[ghost_mapΣ loc (gmap nat nat)].

Global Instance subG_mapGpreS
    `{!crisG Γ Σ α β τ _S _I} :
  subG mapΓ Γ -> mapGpreS.
Proof. solve_inG. Defined.

Local Existing Instances mapGS_pre map_modelG.

Global Instance map_modelGS
    `{!crisG Γ Σ α β τ _S _I, !mapGS} :
  ghost_mapG Σ loc (gmap nat nat) :=
  @subHG_ghost_map loc loc_eq_dec loc_countable
    (gmap nat nat) Γ Σ
    (subG_subHG Γ Σ _S) map_modelG.

Section resources.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS}.

  (** TODO 1(a): authoritative ownership of all handle models. *)
  Definition map_auth
      (models : gmap loc (gmap nat nat)) : iProp Σ.
  Admitted.

  (** TODO 1(b): exclusive client ownership of one handle's model. *)
  Definition is_map
      (handle : loc) (model : gmap nat nat) : iProp Σ.
  Admitted.
End resources.

Module MapA. Section MapA.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS}.

  (** TODO 1(c): [new_map] creates an empty mathematical map. *)
  Definition new_map_spec : fspec.
  Admitted.

  (** TODO 1(d): [insert] updates one key with [<[key := value]> model]. *)
  Definition insert_spec : fspec.
  Admitted.

  (** TODO 1(e): [delete] removes one key with [delete key model]. *)
  Definition delete_spec : fspec.
  Admitted.

  (** TODO 1(f): [get] returns [model !! key] without changing [model]. *)
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
    map_auth (∅ : gmap loc (gmap nat nat)).

  Definition init_cond : iProp Σ := auth_init.

  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End MapA. End MapA.

(** TODO 1(g): allocate the initially empty authoritative registry. *)
Lemma map_alloc
    `{!crisG Γ Σ α β τ _S _I, !mapGpreS} :
  ⊢ o=> ∃ (_ : mapGS), MapA.init_cond.
Admitted.
