(** * Body-preserving prime-client specification *)

From CRIS.common Require Import CRIS.
From prime_safe Require Export LListHeader PrimeHeader.

(** [PrimeA] keeps the concrete client body.  Its deliberately small public
    specification states that a well-typed call returns a natural number.
    Memory safety inside the body is established through the specifications
    of the linked-list operations. *)
Module PrimeA. Section PrimeA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := ["Prime"].

  Definition get_prime_spec : fspec :=
    fspec_simple
      (fun _ : unit =>
        ((fun arg => ⌜arg = tt↑⌝),
         (fun ret => ∃ value : nat, ⌜ret = value↑⌝)))%I.

  Definition main_spec : fspec :=
    fspec_simple
      (fun _ : unit =>
        ((fun arg => ⌜arg = tt↑⌝),
         (fun ret => ⌜ret = tt↑⌝)))%I.

  Definition sp : specmap :=
    {[entry @ main_spec;
      fid PrimeHdr.get_prime @ get_prime_spec]}.

  (** These are exactly the bodies from [PrimeI]. *)

  (*** C-like behavior

  bool has_divisor(val list_loc, nat candidate, nat found) {
    for (nat index = 0; index < found; index++) {
      option<nat> entry = LList.get(list_loc, index);
      nat divisor = entry.value;  // [entry] must be [Some]
      if (candidate % divisor == 0)
        return true;
    }
    return false;
  }

  This helper is private to [PrimeI], rather than a linked-list operation.
  The caller knows that the list length is [found], so [get index] is [Some]
  inside the loop.  [triggerUB] marks a violation of that private invariant.
  ***)
  Definition has_divisor
      (list_loc : val) (candidate found : nat) : itree crisE bool :=
    iterC
      (fun index =>
        if Nat.eq_dec index found
        then Ret (inr false)
        else
          'entry_opt : option nat <-
            ccallU LListHdr.get (list_loc, index);;
          match entry_opt with
          | Some divisor =>
            if Nat.eqb (candidate mod divisor) 0
            then Ret (inr true)
            else Ret (inl (S index))
          | None => triggerUB
          end)
      0.

  (*** C-like behavior

  nat get_prime(void) {
    nat n = input();
    val list_loc = LList.new();

    nat candidate = 2;
    nat found = 0;  // number of primes strictly before candidate
    while (true) {
      bool composite = has_divisor(list_loc, candidate, found);
      if (composite) {
        candidate = candidate + 1;
      } else {
        LList.push_front(list_loc, candidate);
        if (found == n)
          return candidate;

        candidate++;
        found++;
      }
    }
  }

  The input event supplies the zero-based index.  At the outer loop head, the
  list is [first_primes_desc found].  Therefore a prime candidate with
  [found = n] is [nth_prime n].  [inl] continues with a new
  [(candidate, found)] state; [inr] returns the answer.
  ***)
  Definition get_prime : unit -> itree crisE nat :=
    fun _ =>
      n <- trigger (IO "input" ());;
      'list_loc : val <- ccallU LListHdr.new tt;;
      iterC
        (fun '(candidate, found) =>
          'composite : bool <-
            has_divisor list_loc candidate found;;
          if composite
          then Ret (inl (S candidate, found))
          else
            '_ : unit <-
              ccallU LListHdr.push_front (list_loc, candidate);;
            if Nat.eq_dec found n
            then Ret (inr candidate)
            else Ret (inl (S candidate, S found)))
        (2, 0).

  Definition main : Any.t -> itree crisE Any.t :=
    fun _ =>
      prime <- ccallU PrimeHdr.get_prime tt;;
      '_ : unit <- trigger (@IO nat unit "print" prime);;
      Ret tt↑.

  Definition fnsems : fnsemmap :=
    {[entry #
        (msk_scp scopes msk_true,
          (fsp_some main_spec, main));
      fid PrimeHdr.get_prime #
        (msk_scp scopes msk_true,
          (fsp_some get_prime_spec,
            cfunU PrimeHdr.get_prime get_prime))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := emp%I.
  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End PrimeA. End PrimeA.
