From CRIS.common Require Import CRIS.
From prime Require Import LListA PrimeA PrimeI.

(** Exercise 3: verify the prime calculator while keeping the linked list at
    its resource-level specification.  This separation is deliberate: first
    verify the client against [LListA], then compose with [LListIA]. *)
Module PrimeIA. Section PrimeIA.
  Context `{!crisG Γ Σ α β τ _S _I, !llistGS}.

  (** [PrimeA.t] already uses the map derived from [PrimeA.smod].  This
      separate map belongs to the target-side [LListA] module and is shared
      with the source side of [LListIA]. *)
  Context (sp_list : specmap).
  Context (LIST_IN_SP : LListA.sp ⊆ sp_list).

  Local Definition PrimeAMod := PrimeA.t.
  Local Definition PrimeIMod := PrimeI.t ★ LListA.t sp_list.

  (** The modules have no private state at this layer.  [LListA] appears only
      in the target module, where its calls are inlined.  The interesting
      state is the resource-level list fragment.

      TODO 3(a): after initialization, strengthen [values] to
      [first_primes_desc found], keep the returned [list_loc] fixed, and
      record the interval containing [candidate].  It is often easiest to
      express that stronger fact as a pure invariant local to
      [simF_get_prime], while keeping this module invariant small. *)
  Definition Ist : ist_type Σ :=
    (fun st_src st_tgt =>
      ⌜st_src = st_tgt⌝ ∗
      ∃ state,
        LListA.list_user state)%I.

  Lemma simF_get_prime :
    ISim.sim_fun
      open PrimeAMod PrimeIMod Ist (fid PrimeHdr.get_prime).
  Proof.
    (* TODO 3(b): suggested proof plan.

       1. Start the function simulation and expose both [get_prime] bodies.
          Match their common [IO "input"] event and name its result [n].
       2. Inline the target call to [LList.new], name its stable result
          [list_loc], obtain [is_list list_loc []], and choose [nth_prime n]
          on the source side.
       3. Generalize the loop state [(candidate, found)] and use strong
          induction on a decreasing search measure.
       4. Maintain:
            values = first_primes_desc found
          and that [candidate] lies after the last found prime but no later
          than [nth_prime found].  Keep the same [list_loc] throughout.
       5. For [has_divisor], induct over its remaining indexes.  Each [get]
          call preserves [is_list list_loc values].  Use
          [first_primes_desc_length] to show that indexes below [found]
          return [Some]; record that visited primes do not divide
          [candidate].
       6. If traversal returns false, use the fact that every composite has a
          smaller prime divisor.  Thus [candidate] is prime; [push_front]
          changes the contents to [candidate :: values] while preserving
          [list_loc].
       7. When [found = n], choose [candidate] as the abstract return value
          and prove the pure guarantee [candidate = nth_prime n].

       Useful supplied facts include [primeb_spec], [next_prime_spec],
       [next_prime_min], [no_prime_between], [nth_prime_is_prime], and
       [nth_prime_strict]. *)
  Admitted.

  Lemma sim :
    ISim.t open PrimeAMod PrimeIMod LListA.frag_init Ist.
  Proof.
    (* TODO 3(c): start the module simulation, establish [Ist] from the
       uninitialized [LListA.frag_init], and dispatch [get_prime] to the lemma
       above.  The source has no linked-list auxiliary module. *)
  Admitted.
End PrimeIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !llistGS}.

  Lemma ctxr
      (sp_list : specmap)
      (LIST_IN_SP : LListA.sp ⊆ sp_list) :
    LListA.frag_init ⊢ ctx_refines
      (PrimeI.t ★ LListA.t sp_list)
      PrimeA.t.
  Proof.
    (* TODO 3(d): apply [main_adequacy] to [sim]. *)
  Admitted.
End contextual_refinement. End PrimeIA.
