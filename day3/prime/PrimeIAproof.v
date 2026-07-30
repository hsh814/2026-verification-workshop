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
      in the target module, where its calls are inlined.  The list fragment
      crosses [get_prime] through its function specification rather than the
      module invariant.

      TODO 3(a): use [IstEq] here.  During [get_prime], strengthen [values] to
      [first_primes_desc found], keep the returned [list_loc] fixed, and
      record the interval containing [candidate].  It is often easiest to
      express that stronger fact as a pure invariant local to
      [simF_get_prime]. *)
  Definition Ist : ist_type Σ := IstEq.

  Lemma simF_get_prime :
    ISim.sim_fun
      open PrimeAMod PrimeIMod Ist (fid PrimeHdr.get_prime).
  Proof.
    (* TODO 3(b): suggested proof plan.

       1. Start the function simulation, obtain [list_user] from
          [PrimeA.get_prime_spec], and expose both [get_prime] bodies.  Match
          their common [IO "input"] event and name its result [n].
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
       7. When [found = n], prove [candidate = nth_prime n], return the final
          [list_user] through the source postcondition, and establish [IstEq].

       Useful supplied facts include [primeb_spec], [next_prime_spec],
       [next_prime_min], [no_prime_between], [nth_prime_is_prime], and
       [nth_prime_strict]. *)
  Admitted.

  Lemma simF_main :
    ISim.sim_fun open PrimeAMod PrimeIMod Ist entry.
  Proof.
    (* TODO 3(c): obtain [list_uninit] from [PrimeA.main_spec], use it to
       establish the precondition of the source [get_prime] call, and match
       that call with [cCall].  After matching the common print event, return
       the resulting [list_user] through the entry postcondition. *)
  Admitted.

  Lemma sim :
    ISim.t open PrimeAMod PrimeIMod emp%I Ist.
  Proof.
    (* TODO 3(d): start the module simulation, establish [IstEq] from [emp],
       and dispatch [entry] and [get_prime] to the lemmas above.  The source
       has no linked-list auxiliary module. *)
  Admitted.
End PrimeIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !llistGS}.

  Lemma ctxr
      (sp_list : specmap)
      (LIST_IN_SP : LListA.sp ⊆ sp_list) :
    ⊢ ctx_refines
      (PrimeI.t ★ LListA.t sp_list)
      PrimeA.t.
  Proof.
    (* TODO 3(e): apply [main_adequacy] to [sim]. *)
  Admitted.
End contextual_refinement. End PrimeIA.
