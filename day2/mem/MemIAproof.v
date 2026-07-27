(** * Exercise 2: Prove that [MemI] Refines [MemA] *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From lib Require Import mono_nat.
From mem Require Import MemA MemI.

Module MemIA. Section MemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.
  Local Existing Instances memGS_pre mem_mapG mem_countG.

  Context (sp : specmap).

  Local Definition MemAMod := MemA.t sp.
  Local Definition MemIMod := MemI.t.

  (** TODO 2(a): connect the source and target module states to the two
      authoritative resources.

      The abstract module state is empty.  The target state contains one
      [MemState.t] at [MemI.v_mem].  Its [cells] field must equal the
      authoritative ghost map and its [count] field must equal the
      authoritative monotone natural. *)
  Definition Ist : ist_type Σ.
  Admitted.

  (** TODO 2(b): prove the four function simulations with [cStartFunSim],
      [cStepsS]/[cStepsT], and Iris proof-mode tactics.  Keep [ghost_map] and
      [mono_nat] abstract; use their high-level library lemmas. *)

  Lemma simF_alloc :
    ISim.sim_fun open MemAMod MemIMod Ist (fid MemHdr.alloc).
  Proof.
    (* Choose [fresh (dom m.(MemState.cells))].  Prove it is absent with
       [not_elem_of_dom] and [is_fresh], then use [ghost_map_insert]. *)
  Admitted.

  Lemma simF_load :
    ISim.sim_fun open MemAMod MemIMod Ist (fid MemHdr.load).
  Proof.
    (* Use [ghost_map_lookup] to justify the concrete lookup.  Preserve the
       cell fragment and advance the authoritative counter with
       [mono_nat_own_update]. *)
  Admitted.

  Lemma simF_store :
    ISim.sim_fun open MemAMod MemIMod Ist (fid MemHdr.store).
  Proof.
    (* Use [ghost_map_lookup], [ghost_map_update], and
       [mono_nat_own_update].  Return the updated points-to resource. *)
  Admitted.

  Lemma simF_get_cnt :
    ISim.sim_fun open MemAMod MemIMod Ist (fid MemHdr.get_cnt).
  Proof.
    (* Validate the caller's lower-bound snapshot with
       [mono_nat_lb_own_valid], then obtain the current persistent snapshot
       with [mono_nat_lb_own_get].  [get_cnt] does not change the counter. *)
  Admitted.

  Lemma sim :
    ISim.t open MemAMod MemIMod MemA.auth_init Ist.
  Proof.
    (* TODO 2(c): use [cStartModSim], establish [Ist] for [MemState.empty],
       and discharge the four function goals with the lemmas above. *)
  Admitted.
End MemIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Lemma ctxr (sp : specmap) :
    MemA.auth_init ⊢ ctx_refines MemI.t (MemA.t sp).
  Proof.
    (* TODO 2(d): apply [main_adequacy] and [sim]. *)
  Admitted.
End contextual_refinement. End MemIA.
