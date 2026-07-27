(** * Exercise 3: compose the proofs and cancel the specifications *)

From CRIS.common Require Import CRIS.
From CRIS.cancellation Require Import Cancel.
From CRIS.imp_system.mem Require Import MemA MemI.
From CRIS.imp_system.safe_mem Require Import MemNB MemINBproof.
From prime_safe Require Import
  LListA LListI LListIAproof PrimeA PrimeI PrimeIAproof.

(** Cancellation is applied to the complete body-preserving source module.
    Consequently [sp] is exactly [SMod.sp_from smod_src]; it contains the
    specifications of [PrimeA], [LListA], and [MemNB].  Cancellation removes
    those specifications but retains all three concrete bodies. *)
Section PrimeSafeAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !memGS}.

  Local Definition smod_src : SMod.t :=
    PrimeA.smod ☆ LListA.smod ☆ MemNB.smod [].

  Local Definition sp : specmap := SMod.sp_from smod_src.

  Local Definition mod_src : Mod.t :=
    SMod.to_mod sp smod_src.

  Local Definition mod_top : Mod.t :=
    SMod.to_mod ∅ (SMod.cancel smod_src).

  Local Definition mod_tgt : Mod.t :=
    PrimeI.t ★ LListI.t ★ MemI.t [].

  Local Definition init_cond : iProp Σ := MemA.init_cond [].

  Lemma prime_in_sp : PrimeA.sp ⊆ sp.
  Proof.
    (* TODO 3(a): unfold [sp] and prove the finite-map inclusion. *)
  Admitted.

  Lemma llist_in_sp : LListA.sp ⊆ sp.
  Proof.
    (* TODO 3(b): unfold [sp] and prove the finite-map inclusion. *)
  Admitted.

  Lemma mem_in_sp : MemNB.sp ⊆ sp.
  Proof.
    (* TODO 3(c): unfold [sp] and prove the finite-map inclusion. *)
  Admitted.

  Lemma cancel_src :
    (init_cond ∗ Cancel.init_res)%I ⊢
      (init_cond ∗ refines mod_src mod_top)%I.
  Proof.
    (* TODO 3(d): apply [Cancel.prepare] and then [Cancel.cancel] to
       [smod_src].  Its entry carries [PrimeA.get_prime_spec]. *)
  Admitted.

  (** Compose the body-preserving layers in this order:

        PrimeI ★ LListI ★ MemI
          <= PrimeI ★ LListI ★ MemNB
          <= PrimeI ★ LListA ★ MemNB
          <= PrimeA ★ LListA ★ MemNB.

      Every intermediate module uses the one map [sp], so the adjacent sides
      match exactly. *)
  Lemma src_tgt :
    init_cond ⊢ refines mod_tgt mod_src.
  Proof.
    (* TODO 3(e): frame and compose [MemINB.ctxr], [LListIA.ctxr], and
       [PrimeIA.ctxr], using the three inclusions above. *)
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
    (* TODO 3(f): prove that the three concrete modules link without
       duplicate definitions or scopes. *)
  Admitted.
End PrimeSafeAux.

Module PrimeSafeAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ; concΓ; memΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  (** The target is the original concrete program with unsafe memory.  The
      cancelled source keeps the same Prime, list, and safe-memory bodies,
      but all their specifications have disappeared. *)
  Theorem behavioral_refinement :
    ∃ β τ
      (Hinv : invGS Γ Σ α)
      (_ : crisG Γ Σ α β τ _ Hinv)
      (_ : memGS)
      src_res tgt_res,
      refines_lmod
        (Mod.to_lmod mod_tgt tgt_res)
        (Mod.to_lmod mod_top src_res).
  Proof.
    (* TODO 3(g): allocate the CRIS and memory resources, then apply
       [top_tgt] and [tgt_wf]. *)
  Admitted.
End PrimeSafeAll.

(* Print Assumptions PrimeSafeAll.behavioral_refinement. *)
