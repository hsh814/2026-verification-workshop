(** * Cancellation and final composition *)

From CRIS.common Require Import CRIS.
From CRIS.cancellation Require Import Cancel.
From CRIS.imp_system.mem Require Import MemI MemA MemIAproof.
From prime Require Import
  LListA LListI LListIAproof PrimeA PrimeI PrimeIAproof.

(** Exercise 4 links the proof layers and then cancels the final abstract
    module.

    [LListA] is an internal proof layer, not part of [smod_src].  The
    [PrimeIA] refinement inlines calls to [LListA] on its target side and
    removes that auxiliary module.  Consequently, the abstract module left
    for cancellation is [PrimeA] alone.

    Each abstraction boundary has its own specification map.  This makes the
    intermediate modules match exactly during composition and leaves
    [sp_prime] exactly equal to [SMod.sp_from smod_src], as required by
    cancellation. *)
Section PrimeAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !llistGS, !memGS}.

  (** The abstract module that remains after all auxiliary specifications
      have been discharged. *)
  Local Definition smod_src : SMod.t := PrimeA.smod.

  Local Definition sp_prime : specmap := SMod.sp_from PrimeA.smod.
  Local Definition sp_list : specmap := SMod.sp_from LListA.smod.
  Local Definition sp_mem : specmap := SMod.sp_from MemA.smod.

  Local Definition mod_src : Mod.t :=
    SMod.to_mod sp_prime smod_src.

  Local Definition mod_top : Mod.t :=
    SMod.to_mod ∅ (SMod.cancel smod_src).

  Local Definition mod_tgt : Mod.t :=
    PrimeI.t ★ LListI.t ★ MemI.t [].

  Local Definition init_cond : iProp Σ :=
    (LListA.init_cond ∗ MemA.init_cond [])%I.

  (** The map derived from [LListA.smod] contains the public linked-list
      specifications used by both adjacent proof layers. *)
  Lemma llist_in_sp : LListA.sp ⊆ sp_list.
  Proof.
    (* TODO 4(a): unfold [sp_list] and prove the finite-map inclusion. *)
  Admitted.

  (** Cancellation removes the specification machinery from the remaining
      source module.  [Cancel.init_res] is the administrative resource needed
      by the cancellation theorem. *)
  Lemma cancel_src :
    (init_cond ∗ Cancel.init_res)%I ⊢
      (init_cond ∗ refines mod_src mod_top)%I.
  Proof.
    (* TODO 4(b): first apply [Cancel.prepare], then [Cancel.cancel].
       [PrimeA] is cancellable and its entry has [fsp_none]. *)
  Admitted.

  (** Compose the implementation refinements in this order:

        MemI <= MemA
        LListI ★ MemA <= LListA
        PrimeI ★ LListA <= PrimeA.

      The source sides of [LListIA] and [PrimeIA] contain no auxiliary
      modules.  Frame the unused resource halves while applying each result,
      and finish with [LListA.init_cond = frag_init ∗ auth_init]. *)
  Lemma src_tgt :
    init_cond ⊢ refines mod_tgt mod_src.
  Proof.
    (* TODO 4(c): instantiate [MemIA.ctxr] with [sp_mem], [LListIA.ctxr]
       with [sp_list] and [sp_mem], and [PrimeIA.ctxr] with [sp_list]. *)
  Admitted.

  Lemma top_tgt :
    (init_cond ∗ Cancel.init_res)%I ⊢ refines mod_tgt mod_top.
  Proof.
    iIntros "R".
    iPoseProof (cancel_src with "R") as "[INIT REF2]".
    iPoseProof (src_tgt with "INIT") as "REF1".
    iApply refines_trans. iFrame.
  Qed.

  Lemma tgt_wf : Mod.wf mod_tgt.
  Proof.
    (* TODO 4(d): establish well-formedness of the three linked concrete
       modules. *)
  Admitted.
End PrimeAux.

Module PrimeAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ; llistΓ; memΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  (** The final theorem compares the fully concrete linked implementation
      with the cancelled abstract prime program. *)
  Theorem behavioral_refinement :
    ∃ β τ
      (Hinv : invGS Γ Σ α)
      (_ : crisG Γ Σ α β τ _ Hinv)
      (_ : llistGS)
      (_ : memGS)
      src_res tgt_res,
      refines_lmod
        (Mod.to_lmod mod_tgt tgt_res)
        (Mod.to_lmod mod_top src_res).
  Proof.
    (* TODO 4(e): allocate the CRIS, linked-list, and memory resources, then
       apply [top_tgt] and [tgt_wf] as in the other [*All.v] files. *)
  Admitted.
End PrimeAll.

(* Print Assumptions PrimeAll.behavioral_refinement. *)
