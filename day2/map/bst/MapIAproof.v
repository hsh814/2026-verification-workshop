(** * Exercise 2: Verify the Unbalanced-BST Map *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From mem Require Import MemA.
From map.bst Require Import MapA MapI.

Module MapIA. Section MapIA.
  Context `{!crisG Γ Σ α β τ _S _I, !mapGS, !memGS}.

  Context (sp_map sp_mem : specmap).
  Context (MAP_IN_SP : MapA.sp ⊆ sp_map).

  Local Definition MapAMod := MapA.t sp_map.
  Local Definition MapIMod := MapI.t ★ MemA.t sp_mem.

  (** TODO 2(a): define a recursive tree resource.  It should own every
      concrete node, enforce the BST ordering property, interpret [Vundef]
      as a deleted key, and agree with the abstract [gmap]. *)
  Definition map_rep
      (handle : loc) (model : gmap nat nat) : iProp Σ.
  Admitted.

  (** TODO 2(b): own the authoritative handle registry and one separating
      concrete tree representation for every entry in it. *)
  Definition Ist : ist_type Σ.
  Admitted.

  Lemma simF_new_map :
    ISim.sim_fun open MapAMod MapIMod Ist
      (fid MapHdr.new_map).
  Admitted.

  Lemma simF_insert :
    ISim.sim_fun open MapAMod MapIMod Ist
      (fid MapHdr.insert).
  Admitted.

  Lemma simF_delete :
    ISim.sim_fun open MapAMod MapIMod Ist
      (fid MapHdr.delete).
  Admitted.

  Lemma simF_get :
    ISim.sim_fun open MapAMod MapIMod Ist
      (fid MapHdr.get).
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
