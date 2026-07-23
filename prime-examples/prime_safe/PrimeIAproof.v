(** * Exercise 2: prove that the prime client is memory safe *)

From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemA.
From CRIS.imp_system.safe_mem Require Import MemNB.
From prime_safe Require Import
  LListA PrimeA PrimeI.

(** [PrimeA] and [PrimeI] also have identical bodies.  The proof uses the
    supplied [LListA] specifications to show that every list access is safe
    and that the [None] branch leading to [triggerUB] is unreachable. *)
Module PrimeIA. Section PrimeIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Context (sp : specmap).
  Context (PRIME_IN_SP : PrimeA.sp ⊆ sp).
  Context (LIST_IN_SP : LListA.sp ⊆ sp).
  Context (MEM_IN_SP : MemNB.sp ⊆ sp).

  Local Definition AuxMod : Mod.t :=
    LListA.t sp ★ MemNB.t sp [].

  Local Definition PrimeAMod : Mod.t :=
    PrimeA.t sp ★ AuxMod.

  Local Definition PrimeIMod : Mod.t :=
    PrimeI.t ★ AuxMod.

  (** The proof state is owned by [LListA.is_list].  [IstProd] separates the
      prime layer from the common list-and-memory suffix. *)
  Definition IstLocal : ist_type Σ := IstTrue.

  Definition Ist : ist_type Σ :=
    IstProd (IstSB (PrimeA.t sp).(Mod.scopes) IstLocal) IstEq.

  Lemma simF_get_prime :
    ISim.sim_fun open PrimeAMod PrimeIMod Ist
      (fid PrimeHdr.get_prime).
  Proof.
    (* TODO 2(a): suggested proof outline.

       1. Match the common input event and obtain
          [LListA.is_list list_loc []] from [LList.new].
       2. At the outer-loop head, maintain
            [LListA.is_list list_loc values]
          together with [length values = found].
       3. In [has_divisor], maintain [index <= found].  Therefore every
          call to [LList.get] made before [index = found] returns [Some _],
          and the [triggerUB] branch cannot be reached.
       4. A composite candidate preserves the list.  A non-composite
          candidate uses [push_front], producing a list whose length is
          [S found].
       5. When the loop returns, choose its natural-number result for the
          existential postcondition of [PrimeA.get_prime_spec].

       No primality facts or custom resource algebra are required. *)
  Admitted.

  Lemma sim :
    ISim.t open PrimeAMod PrimeIMod emp%I Ist.
  Proof.
    (* TODO 2(b): use [simF_get_prime].  The [IstProd] structure lets
       [cStartModSim] handle the shared list and memory functions. *)
  Admitted.
End PrimeIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Lemma ctxr
      (sp : specmap)
      (PRIME_IN_SP : PrimeA.sp ⊆ sp)
      (LIST_IN_SP : LListA.sp ⊆ sp)
      (MEM_IN_SP : MemNB.sp ⊆ sp) :
    emp%I ⊢ ctx_refines
      (PrimeI.t ★ LListA.t sp ★ MemNB.t sp [])
      (PrimeA.t sp ★ LListA.t sp ★ MemNB.t sp []).
  Proof.
    (* TODO 2(c): apply [main_adequacy] to [sim]. *)
  Admitted.
End contextual_refinement. End PrimeIA.
