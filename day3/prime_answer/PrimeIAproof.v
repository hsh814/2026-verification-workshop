From CRIS.common Require Import CRIS.
From prime_answer Require Import LListA PrimeA PrimeI.

Definition checked_prefix
    (candidate : nat) (values : list nat) (index : nat) : Prop :=
  forall position divisor,
    position < index ->
    values !! position = Some divisor ->
    candidate mod divisor <> 0.

Lemma checked_prefix_zero candidate values :
  checked_prefix candidate values 0.
Proof. intros position divisor BEFORE. lia. Qed.

Lemma checked_prefix_succ candidate values index divisor :
  checked_prefix candidate values index ->
  values !! index = Some divisor ->
  candidate mod divisor <> 0 ->
  checked_prefix candidate values (S index).
Proof.
  intros CHECKED LOOKUP NOT_DIVIDES position value BEFORE VALUE_LOOKUP.
  destruct (Nat.eq_dec position index) as [-> | NE].
  - congruence.
  - apply (CHECKED position value); first lia. exact VALUE_LOOKUP.
Qed.

Lemma In_lookup {A} (value : A) values :
  In value values -> exists index, values !! index = Some value.
Proof.
  induction values as [|head values IH]; simpl.
  - contradiction.
  - intros [<- | IN].
    + exists 0. reflexivity.
    + destruct (IH IN) as [index LOOKUP].
      exists (S index). exact LOOKUP.
Qed.

Lemma lookup_In {A} (value : A) values index :
  values !! index = Some value -> In value values.
Proof.
  revert index. induction values as [|head values IH];
    intros [|index]; simpl; intros LOOKUP; try discriminate.
  - inversion LOOKUP. left. reflexivity.
  - right. apply (IH index). exact LOOKUP.
Qed.

Lemma checked_prefix_all candidate values index :
  checked_prefix candidate values index ->
  length values <= index ->
  has_divisorb candidate values = false.
Proof.
  intros CHECKED LENGTH.
  apply (proj2 (has_divisorb_false candidate values)).
  intros divisor IN.
  destruct (In_lookup divisor values IN) as [position LOOKUP].
  apply (CHECKED position divisor); last exact LOOKUP.
  apply lookup_lt_Some in LOOKUP. lia.
Qed.

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
      module invariant.  During [get_prime], the proof strengthens [values] to
      [first_primes_desc found], keeps the returned [list_loc] fixed, and
      records the interval containing [candidate].  That stronger fact is
      expressed as a pure invariant local to [simF_get_prime]. *)
  Definition Ist : ist_type Σ := IstEq.

  Lemma simF_get_prime :
    ISim.sim_fun
      open PrimeAMod PrimeIMod Ist (fid PrimeHdr.get_prime).
  Proof.
    cStartFunSim.
    rewrite /PrimeA.get_prime /PrimeI.get_prime.
    cStepsS.
    iDestruct "ASM" as "(-> & -> & USER)". cSimpl.
    cStepsT. cStep.
    cStepsT. cInlineT. cStepsT.
    iDestruct "IST" as %->.
    cForceT _q.
    cForceT (tt↑). cForceT. iFrame. cSimpl.
    iSplit; first done.
    cStepsT.
    iDestruct "GRT" as "[-> GRT]".
    iDestruct "GRT" as (list_loc) "[-> USER]".
    cSimpl. cStepsT.
    set (loop_state := (2, 0)).
    iAssert
      (⌜candidate_window loop_state.2 loop_state.1 /\
         loop_state.2 <= ret⌝ ∗
       LListA.is_list list_loc (first_primes_desc loop_state.2))%I
      with "[USER]" as "LOOP".
    { subst loop_state. simpl. iSplit.
      - iPureIntro. split; first reflexivity. lia.
      - iFrame. }
    clearbody loop_state. destruct loop_state as [candidate found].
    iApply wsim_reset.
    iDestruct "LOOP" as "[%LOOP USER]".
    destruct LOOP as [WINDOW FOUND_LE].
    remember (search_measure ret found candidate) as fuel eqn:FUEL.
    iRevert "USER".
    iStopProof.
    revert candidate found WINDOW FOUND_LE FUEL.
    induction fuel using (well_founded_induction lt_wf);
      intros candidate found WINDOW FOUND_LE FUEL;
      iIntros "_ USER".
    rewrite unfold_iterC. cStepT. cStepsT.
    rewrite /PrimeI.has_divisor.
    set (index := 0) at 2.
    assert (INDEX : index <= found) by (subst index; lia).
    assert (CHECKED :
      checked_prefix candidate (first_primes_desc found) index).
    { subst index. apply checked_prefix_zero. }
    clearbody index.
    remember (found - index) as remaining eqn:REMAINING.
    revert index INDEX CHECKED REMAINING.
    induction remaining as [|remaining IH];
      intros index INDEX CHECKED REMAINING.
    - assert (index = found) as -> by lia.
      rewrite unfold_iterC.
      destruct (Nat.eq_dec found found); last lia.
      cStepsT.
      assert (HAS :
        has_divisorb candidate (first_primes_desc found) = false).
      { eapply checked_prefix_all; first exact CHECKED.
        rewrite first_primes_desc_length. lia. }
      clear CHECKED REMAINING INDEX.
      pose proof
        (no_divisor_found_prime found candidate WINDOW HAS) as PRIME.
      pose proof
        (candidate_prime_eq found candidate WINDOW PRIME) as CANDIDATE.
      cInlineT. cStepsT.
      cForceT (list_loc, first_primes_desc found, candidate).
      cForceT ((list_loc, candidate)↑). cForceT. iFrame. cSimpl.
      iSplit; first done.
      cStepsT.
      iDestruct "GRT" as "(-> & -> & USER)". cSimpl.
      destruct (Nat.eq_dec found ret) as [FOUND | NOT_FOUND].
      + subst found. cStepsT.
        cStepsS. cForcesS.
        iSplitL "USER".
        { iSplit; first done.
          iExists (Some
            (list_loc, nth_prime ret :: first_primes_desc ret)). iFrame. }
        cStep. done.
      + pose proof
          (no_divisor_found_window_step
            found (nth_prime found) WINDOW HAS)
          as NEXT_WINDOW.
        assert (FOUND_LT : found < ret) by lia.
        pose proof
          (no_divisor_found_measure_decreases
            ret found (nth_prime found) FOUND_LT WINDOW HAS)
          as DECREASE.
        cStepsT.
        iApply wsim_reset.
        iApply (H0 _ DECREASE
          (S (nth_prime found)) (S found)
          NEXT_WINDOW ltac:(lia) eq_refl).
        { done. }
        simpl. iFrame.
    - rewrite unfold_iterC.
      destruct (Nat.eq_dec index found) as [END | NOT_END].
      + lia.
      + cStepsT.
        assert (INDEX_LT : index < found) by lia.
        destruct
          (lookup_lt_is_Some_2 (first_primes_desc found) index)
          as [divisor LOOKUP].
        { rewrite first_primes_desc_length. exact INDEX_LT. }
        cInlineT. cStepsT.
        cForceT (list_loc, first_primes_desc found, index).
        cForceT ((list_loc, index)↑). cForceT. iFrame. cSimpl.
        iSplit; first done.
        cStepsT.
        iDestruct "GRT" as "(-> & -> & USER)".
        rewrite LOOKUP. cSimpl. cStepsT.
        destruct (Nat.eqb (candidate mod divisor) 0)
          eqn:DIVIDES.
        * apply Nat.eqb_eq in DIVIDES.
          assert (HAS :
            has_divisorb candidate (first_primes_desc found) = true).
          { apply (proj2
              (has_divisorb_true
                candidate (first_primes_desc found))).
            exists divisor. split; last exact DIVIDES.
            eapply lookup_In. exact LOOKUP. }
          pose proof
            (divisor_found_window_step found candidate WINDOW HAS)
            as NEXT_WINDOW.
          pose proof
            (divisor_found_measure_decreases
              ret found candidate FOUND_LE WINDOW HAS)
            as DECREASE.
          cStepsT. iApply wsim_reset.
          iApply (H0 _ DECREASE (S candidate) found
            NEXT_WINDOW FOUND_LE eq_refl).
          { done. }
          iFrame.
        * apply Nat.eqb_neq in DIVIDES.
          pose proof
            (checked_prefix_succ candidate
              (first_primes_desc found) index divisor
              CHECKED LOOKUP DIVIDES) as CHECKED_NEXT.
          cStepsT.
          apply IH.
          -- lia.
          -- exact CHECKED_NEXT.
          -- lia.
    (* Proof outline.

       1. Start the function simulation and expose both [get_prime] bodies.
          Match their common [IO "input"] event and name its result [n].
       2. Inline the target call to [LList.new], name its stable result
          [list_loc], and obtain [is_list list_loc []].
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
       7. When [found = n], prove [candidate = nth_prime n] and match the
          abstract return.

       Useful supplied facts include [primeb_spec], [next_prime_spec],
       [next_prime_min], [no_prime_between], [nth_prime_is_prime], and
       [nth_prime_strict]. *)
  Qed.

  Lemma simF_main :
    ISim.sim_fun open PrimeAMod PrimeIMod Ist entry.
  Proof.
    cStartFunSim.
    rewrite /PrimeA.main /PrimeI.main.
    cStepsS.
    iDestruct "ASM" as "(-> & -> & USER)". cSimpl.
    cStepsT.
    assert (GET_SPEC :
      (SMod.sp_from PrimeA.smod).1 !! fid PrimeHdr.get_prime =
        fsp_some PrimeA.get_prime_spec) by mod_tac.
    rewrite GET_SPEC.
    cForceS (None : llist_state). cForcesS.
    iSplitL "USER".
    { iSplit; first done. iSplit; first done. iFrame. }
    cCall "IST" as (prime st_src st_tgt) "IST".
    cStepsS.
    iDestruct "ASM" as "[-> USER]".
    iDestruct "USER" as (state) "USER".
    cSimpl.
    destruct (Any.downcast prime : option nat);
      cStepsS; des_ifs.
    cStepsT.
    cStep.
    cStepsS. cForcesS.
    iSplitL "USER".
    { iSplit; first done.
      iSplit; first done.
      iExists state. iFrame. }
    cStep.
    iFrame. done.
  Qed.

  Lemma sim :
    ISim.t open PrimeAMod PrimeIMod emp%I Ist.
  Proof.
    cStartModSim.
    - vm_compute.
      apply submseteq_cons, submseteq_skip, submseteq_nil.
    - iIntros "_". done.
    - apply simF_main.
    - apply simF_get_prime.
  Qed.
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
    eapply main_adequacy, sim; eauto.
  Qed.
End contextual_refinement. End PrimeIA.
