(** * Exercise: Verify the Reference Cell *)

From Stdlib Require Import QArith.Qcanon.
From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From stdpp Require Import numbers.
From refcell.frac_mem Require Import FracMemA.
From refcell.refcell Require Import RefCellA RefCellI.

(** You may find it convenient to total all live ticket fractions in [Qc].
    Unlike [Qp], [Qc] contains zero, so the empty map has a natural sum. *)
Definition borrow_total (bs : gmap nat Qp) : Qcanon.Qc :=
  map_fold
    (fun _ q (total : Qcanon.Qc) =>
      (Qp_to_Qc q + total)%Qc)
    0%Qc bs.

Module RefCellIA. Section RefCellIA.
  Context `{!crisG Γ Σ α β τ _S _I,
    !frac_memGS, !refcellGS}.
  Local Existing Instances
    frac_memGS_pre frac_mem_mapG frac_mem_countG
    refcellGS_pre refcell_registryG refcell_borrowG.

  Context (sp_refcell sp_mem : specmap).
  Context (REFCELL_IN_SP : RefCellA.sp ⊆ sp_refcell).

  Local Definition RefCellAMod := RefCellA.t sp_refcell.
  Local Definition RefCellIMod := RefCellI.t ★ FracMemA.t sp_mem.

  (** TODO 5(a): shared mode should relate

      - the physical counter,
      - a ghost map of active ticket identifiers to fractions, and
      - the residual points-to fraction held by the invariant.

      The active fractions plus the residual fraction must total one. *)
  Definition shared_rep
      (r l : loc) (γb : gname)
      (borrows : gmap nat Qp) : iProp Σ.
  Admitted.

  (** TODO 5(b): mutable mode should record exactly one full ticket.  The
      borrower, rather than the invariant, owns the protected cell. *)
  Definition mutable_rep
      (r l : loc) (γb : gname) : iProp Σ.
  Admitted.

  (** TODO 5(c): combine the two modes for one registry entry. *)
  Definition cell_rep
      (r : loc) (info : refcell_info) : iProp Σ.
  Admitted.

  (** TODO 5(d): own the persistent outer registry and one separating
      [cell_rep] for every registered header. *)
  Definition Ist : ist_type Σ.
  Admitted.

  Lemma simF_new_refcell :
    ISim.sim_fun open RefCellAMod RefCellIMod Ist
      (fid RefCellHdr.new_refcell).
  Admitted.

  Lemma simF_try_borrow :
    ISim.sim_fun open RefCellAMod RefCellIMod Ist
      (fid RefCellHdr.try_borrow).
  Admitted.

  Lemma simF_try_borrow_mut :
    ISim.sim_fun open RefCellAMod RefCellIMod Ist
      (fid RefCellHdr.try_borrow_mut).
  Admitted.

  Lemma simF_drop :
    ISim.sim_fun open RefCellAMod RefCellIMod Ist
      (fid RefCellHdr.drop).
  Admitted.

  Lemma sim :
    ISim.t open RefCellAMod RefCellIMod
      RefCellA.auth_init Ist.
  Admitted.
End RefCellIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I,
    !frac_memGS, !refcellGS}.

  Lemma ctxr
      (sp_refcell sp_mem : specmap)
      (REFCELL_IN_SP : RefCellA.sp ⊆ sp_refcell) :
    RefCellA.auth_init ⊢ ctx_refines
      (RefCellI.t ★ FracMemA.t sp_mem)
      (RefCellA.t sp_refcell).
  Admitted.
End contextual_refinement. End RefCellIA.
