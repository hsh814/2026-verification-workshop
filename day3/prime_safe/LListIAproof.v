(** * Exercise 1: prove the linked-list safety specification *)

From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemA.
From CRIS.imp_system.safe_mem Require Import MemNB.
From prime_safe Require Import LListA LListI.

(** [LListA] and [LListI] have exactly the same linked-list bodies.
    [LListA] additionally attaches specifications to those bodies.  The
    memory module is kept on both sides of this refinement: its
    specifications provide the points-to rules used while checking the list
    bodies, and its concrete body is preserved for the final cancellation. *)
Module LListIA. Section LListIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Context (sp : specmap).
  Context (LIST_IN_SP : LListA.sp ⊆ sp).
  Context (MEM_IN_SP : MemNB.sp ⊆ sp).

  Local Definition ListAMod : Mod.t :=
    LListA.t sp ★ MemNB.t sp [].

  Local Definition ListIMod : Mod.t :=
    LListI.t ★ MemNB.t sp [].

  (** The list layer needs no private logical state.  [IstProd] separates its
      scopes from the shared [MemNB] suffix, whose state is related by
      [IstEq].  This lets the module simulation frame the common suffix
      automatically. *)
  Definition IstLocal : ist_type Σ := IstTrue.

  Definition Ist : ist_type Σ :=
    IstProd (IstSB (LListA.t sp).(Mod.scopes) IstLocal) IstEq.

  Lemma simF_new :
    ISim.sim_fun open ListAMod ListIMod Ist (fid LListHdr.new).
  Proof.
    (* TODO 1(a): match the source and target calls to [MemNB.alloc] and
       [MemNB.store].  The returned ownership establishes
       [LListA.is_list list_loc []].  Do not use [MemTactics]. *)
  Admitted.

  Lemma simF_push_front :
    ISim.sim_fun open ListAMod ListIMod Ist
      (fid LListHdr.push_front).
  Proof.
    (* TODO 1(b): open [LListA.is_list], then match the source and target
       memory calls while loading the head and constructing the new node.
       Do not use [MemTactics]. *)
  Admitted.

  Lemma simF_get :
    ISim.sim_fun open ListAMod ListIMod Ist (fid LListHdr.get).
  Proof.
    (* TODO 1(c): preserve [LListA.is_list list_loc values] while
       traversing [LListA.nodes].  Induct over the list and the index, and
       rebuild the same ownership before returning. *)
  Admitted.

  Lemma sim :
    ISim.t open ListAMod ListIMod emp%I Ist.
  Proof.
    (* TODO 1(d): start the module simulation and dispatch the three public
       functions above.  The [IstProd] structure lets [cStartModSim] handle
       the shared [MemNB] functions automatically. *)
  Admitted.
End LListIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Lemma ctxr
      (sp : specmap)
      (LIST_IN_SP : LListA.sp ⊆ sp)
      (MEM_IN_SP : MemNB.sp ⊆ sp) :
    emp%I ⊢ ctx_refines
      (LListI.t ★ MemNB.t sp [])
      (LListA.t sp ★ MemNB.t sp []).
  Proof.
    (* TODO 1(e): apply [main_adequacy] to [sim]. *)
  Admitted.
End contextual_refinement. End LListIA.
