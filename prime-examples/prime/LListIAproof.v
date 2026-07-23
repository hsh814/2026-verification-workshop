(** * Proofs that LListI refines LListA *)

From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemA MemTactics.
From prime Require Import LListA LListI.

(** Exercise 2: refine the resource-level specification by the linked-list
    implementation. *)
Module LListIA. Section LListIA.
  Context `{!crisG Γ Σ α β τ _S _I, !llistGS, !memGS}.

  (** Keep the maps for the source list specification and the target memory
      specification separate.  The same [sp_list] is later used by
      [PrimeIA], while [sp_mem] matches the source side of [MemIA]. *)
  Context (sp_list sp_mem : specmap).
  Context (LIST_IN_SP : LListA.sp ⊆ sp_list).

  Local Definition ListAMod := LListA.t sp_list.
  Local Definition ListIMod := LListI.t ★ MemA.t sp_mem.

  (** A concrete node consists of adjacent value and next-pointer cells. *)
  Fixpoint nodes (cursor : val) (values : list nat) : iProp Σ :=
    match values with
    | [] => ⌜cursor = Vnullptr⌝
    | value :: values' =>
        ∃ bo next,
          ⌜cursor = Vptr bo⌝ ∗
          bo |-> [Vint (Z.of_nat value); next] ∗
          nodes next values'
    end%I.

  (** The stable header cell contains the first node pointer. *)
  Definition represents
      (list_loc : val) (values : list nat) : iProp Σ :=
    (∃ bo head,
      ⌜list_loc = Vptr bo⌝ ∗
      bo ↦ head ∗
      nodes head values)%I.

  (** The list modules have no private state: all concrete list data lives in
      Imp memory.  [list_auth] connects that representation to the
      client-owned [list_user].  [MemA] appears only in the target module,
      where its calls are inlined during the simulation.

      TODO 2(a): adjust this invariant if your resource choice needs more
      information, but preserve its [ist_type] interface. *)
  Definition Ist : ist_type Σ :=
    (fun st_src st_tgt =>
      ⌜st_src = ∅ /\ st_tgt = ∅⌝ ∗
      ∃ state,
        LListA.list_auth state ∗
        match state with
        | None => emp
        | Some (list_loc, values) => represents list_loc values
        end)%I.

  (** TODO 2(b): prove each function simulation.  Suggested checkpoints are
      included so newcomers can tell what each proof must establish. *)
  Lemma simF_new :
    ISim.sim_fun open ListAMod ListIMod Ist (fid LListHdr.new).
  Proof.
    (* 1. [cStartFunSim], then expose [LListI.new].
       2. Consume [list_uninit] and use [list_agree] to establish that the
          authoritative state is [None].
       3. Use [mAllocT] and [mStoreT] to allocate the stable header and store
          [Vnullptr], then return its location [list_loc].
       4. Use [list_update] to move both resources to
          [Some (list_loc, [])]. *)
  Admitted.

  Lemma simF_push_front :
    ISim.sim_fun open ListAMod ListIMod Ist (fid LListHdr.push_front).
  Proof.
    (* Open [represents], use [mLoadT], allocate the two-cell node with
       [mAllocT], and perform its three stores with [mStoreT].  Then apply
       [list_update] while preserving the stable [list_loc]. *)
  Admitted.

  Lemma simF_get :
    ISim.sim_fun open ListAMod ListIMod Ist (fid LListHdr.get).
  Proof.
    (* Preserve [is_list list_loc values], load the header with [mLoadT], and
       induct over [nodes] and the requested index.  Each [iterC] step loads a
       value and next pointer; reaching [Vnullptr] returns [None]. *)
  Admitted.

  (** The module-level simulation theorem is intentionally already stated. *)
  Lemma sim :
    ISim.t open ListAMod ListIMod LListA.auth_init Ist.
  Proof.
    (* TODO 2(c): [cStartModSim], establish the initial invariant from the
       uninitialized authoritative half, and use the three function
       simulations above. *)
  Admitted.
End LListIA.

(** Contextual refinement is the public result of Exercises 1 and 2.
    Direction reminder: the implementation on the left refines the abstract
    resource specification on the right. *)
Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !llistGS, !memGS}.

  Lemma ctxr
      (sp_list sp_mem : specmap)
      (LIST_IN_SP : LListA.sp ⊆ sp_list) :
    LListA.auth_init ⊢ ctx_refines
      (LListI.t ★ MemA.t sp_mem)
      (LListA.t sp_list).
  Proof.
    (* TODO 2(d): this is one application of [main_adequacy] and [sim]. *)
  Admitted.
End contextual_refinement. End LListIA.
