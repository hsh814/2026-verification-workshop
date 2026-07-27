(** * Template: Verify Your Map Representation *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From mem Require Import MemA.
From map.try Require Import MapA MapI.

Module MapIA. Section MapIA.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS, !memGS}.

  Context (sp_map sp_mem : specmap).
  Context (MAP_IN_SP : MapA.sp ⊆ sp_map).

  Local Definition MapAMod := MapA.t sp_map.
  Local Definition MapIMod := MapI.t ★ MemA.t sp_mem.

  (** TODO: define ownership of one concrete representation. *)
  Definition map_rep (r : loc) (m : amap) : iProp Σ.
  Admitted.

  (** TODO: relate the authoritative registry to all live representations. *)
  Definition Ist : ist_type Σ.
  Admitted.

  Lemma simF_new_map :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.new_map).
  Admitted.

  Lemma simF_insert :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.insert).
  Admitted.

  Lemma simF_delete :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.delete).
  Admitted.

  Lemma simF_get :
    ISim.sim_fun open MapAMod MapIMod Ist (fid MapHdr.get).
  Admitted.

  Lemma sim :
    ISim.t open MapAMod MapIMod MapA.auth_init Ist.
  Admitted.
End MapIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS, !memGS}.

  Lemma ctxr
      (sp_map sp_mem : specmap)
      (MAP_IN_SP : MapA.sp ⊆ sp_map) :
    MapA.auth_init ⊢ ctx_refines
      (MapI.t ★ MemA.t sp_mem)
      (MapA.t sp_map).
  Admitted.
End contextual_refinement. End MapIA.
