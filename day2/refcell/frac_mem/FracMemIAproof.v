(** * Exercise 3: Prove Fractional Memory Correct *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From lib Require Import mono_nat.
From refcell.frac_mem Require Import FracMemA FracMemI.

Module FracMemIA. Section FracMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !frac_memGS}.
  Local Existing Instances
    frac_memGS_pre frac_mem_mapG frac_mem_countG.

  Context (sp : specmap).

  Local Definition FracMemAMod := FracMemA.t sp.
  Local Definition FracMemIMod := FracMemI.t.

  (** TODO 3(a): relate the concrete finite map and counter to their two
      authoritative high-level resources. *)
  Definition Ist : ist_type Σ.
  Admitted.

  (** TODO 3(b): the allocation proof is unchanged from ordinary memory. *)
  Lemma simF_alloc :
    ISim.sim_fun open FracMemAMod FracMemIMod Ist
      (fid FracMemHdr.alloc).
  Admitted.

  (** TODO 3(c): [ghost_map_lookup] accepts every [DfracOwn q], which is the
      key reason [load] works with a read-only share. *)
  Lemma simF_load :
    ISim.sim_fun open FracMemAMod FracMemIMod Ist
      (fid FracMemHdr.load).
  Admitted.

  (** TODO 3(d): [store] still uses [ghost_map_update] and therefore needs
      the full points-to fragment. *)
  Lemma simF_store :
    ISim.sim_fun open FracMemAMod FracMemIMod Ist
      (fid FracMemHdr.store).
  Admitted.

  (** TODO 3(e): reuse the persistent monotone-counter reasoning. *)
  Lemma simF_get_cnt :
    ISim.sim_fun open FracMemAMod FracMemIMod Ist
      (fid FracMemHdr.get_cnt).
  Admitted.

  Lemma sim :
    ISim.t open FracMemAMod FracMemIMod
      FracMemA.auth_init Ist.
  Admitted.
End FracMemIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !frac_memGS}.

  Lemma ctxr (sp : specmap) :
    FracMemA.auth_init ⊢
      ctx_refines FracMemI.t (FracMemA.t sp).
  Admitted.
End contextual_refinement. End FracMemIA.
