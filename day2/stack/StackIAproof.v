(** * Exercise 4: Prove that [StackI] Refines [StackA] Using [MemA] *)

From CRIS.common Require Import CRIS.
From mem Require Import MemA.
From stack Require Import StackA StackI.

Module StackIA. Section StackIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Context (sp_stack sp_mem : specmap).
  Context (STACK_IN_SP : StackA.sp ⊆ sp_stack).

  Local Definition StackAMod := StackA.t sp_stack.
  Local Definition StackIMod := StackI.t ★ MemA.t sp_mem.

  (** TODO 4(a): choose the simulation invariant.  Neither stack module has
      private state: all concrete stack data is already represented by
      client-visible memory resources. *)
  Definition Ist : ist_type Σ.
  Admitted.

  (** TODO 4(b): prove the three simulations by inlining only calls to
      [MemA].  At each call, force the corresponding memory specification and
      frame exactly the required points-to resource. *)

  Lemma simF_new_stack :
    ISim.sim_fun open StackAMod StackIMod Ist
      (fid StackHdr.new_stack).
  Proof.
    (* Allocate the header cell, store [Vloc None], and build
       [is_stack l []]. *)
  Admitted.

  Lemma simF_push :
    ISim.sim_fun open StackAMod StackIMod Ist
      (fid StackHdr.push).
  Proof.
    (* Open [is_stack].  Allocate a node, load the current header, initialize
       the node, update the header, and fold the new head of [linked_list]. *)
  Admitted.

  Lemma simF_pop :
    ISim.sim_fun open StackAMod StackIMod Ist
      (fid StackHdr.pop).
  Proof.
    (* Open [is_stack] and load the header.  Destruct the logical [values].
       The empty branch returns [None].  The nonempty branch exposes one
       node, loads it, advances the header, and returns [Some value]. *)
  Admitted.

  Lemma sim :
    ISim.t open StackAMod StackIMod emp Ist.
  Proof.
    (* TODO 4(c): use [cStartModSim].  The target composition has one extra
       ["Mem"] scope, so prove the scope inclusion before the initial
       invariant and three function goals. *)
  Admitted.
End StackIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Lemma ctxr
      (sp_stack sp_mem : specmap)
      (STACK_IN_SP : StackA.sp ⊆ sp_stack) :
    emp ⊢ ctx_refines
      (StackI.t ★ MemA.t sp_mem)
      (StackA.t sp_stack).
  Proof.
    (* TODO 4(d): apply [main_adequacy] and [sim]. *)
  Admitted.
End contextual_refinement. End StackIA.
