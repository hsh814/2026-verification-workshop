(** * Linked List Spec Module **)

From CRIS.common Require Import CRIS.
From prime_answer Require Export LListHeader.

(** * Exercise 1: give the linked-list API an Iris resource specification.

    The public names and theorem statements below are used by the later
    simulation files.

    This exercise tracks the logical state of one linked-list instance.
    [None] means that this logical state is uninitialized: [new] has not yet
    associated it with a concrete list.  [Some (list_loc, values)] means that
    [list_loc] is the stable location returned by [new], and [values] is the
    current logical content of that list.  Operations may change [values], but
    they preserve [list_loc]. *)

(* In fact, a more general resource model could track every list created by the
   module in an authoritative finite map from locations to lists.  Each map
   entry could then support an independent [is_list list_loc values]
   resource.  This generalized resource model is not required for the
   exercise.  Participants who want to extend the exercise to support
   multiple lists are encouraged to try it. *)

Definition llist_state : Type := option (val * list nat).

Canonical Structure llist_stateO := leibnizO llist_state.

(** The singleton logical state uses an exclusive authoritative resource.
    It must provide an authoritative element for the library proof and a
    client-owned fragment that agrees with it and can be updated jointly. *)
Local Definition LListRA : ucmra := excl_authR llist_stateO.

Class llistGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] llist_inG :: inG LListRA Γ;
}.

Class llistGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] llistGS_pre :: llistGpreS;
  llist_name : gname;
}.

(** Package [LListRA] as one
    discrete resource algebra. *)
Definition llistΓ : HRA := #[LListRA].

Global Instance subG_llistGpreS
  `{!crisG Γ Σ α β τ _S _I} :
  subG llistΓ Γ -> llistGpreS.
Proof.
  solve_inG.
Defined.

Module LListA. Section LListA.
  Context `{!crisG Γ Σ α β τ _S _I, !llistGS}.

  (** The authoritative implementation resource and the
      client-owned model (fragment) of the singleton state. *)
  Definition list_auth (state : llist_state) : iProp Σ :=
    own llist_name (●E state).

  Definition list_user (state : llist_state) : iProp Σ :=
    own llist_name (◯E state).

  Definition list_uninit : iProp Σ := list_user None.

  Definition is_list (list_loc : val) (values : list nat) : iProp Σ :=
    list_user (Some (list_loc, values)).

  (** RA facts used by the simulation. *)

  (** Owning both the authoritative resource and a user fragment reveals that
      their states agree. *)
  Lemma list_agree auth_state user_state :
    list_auth auth_state -∗
    list_user user_state -∗
    ⌜auth_state = user_state⌝.
  Proof.
    rewrite /list_auth /list_user.
    iIntros "AUTH USER".
    iCombine "USER AUTH" as "BOTH" gives %VALID.
    apply excl_auth_agree in VALID.
    iPureIntro. by apply leibniz_equiv.
  Qed.

  (** Joint ownership of the authoritative resource and its matching user
      fragment permits both resources to be updated to the same new state. *)
  Lemma list_update old_state new_state :
    list_auth old_state -∗ list_user old_state ==∗
      list_auth new_state ∗ list_user new_state.
  Proof.
    rewrite /list_auth /list_user.
    iIntros "AUTH USER".
    iCombine "AUTH USER" as "BOTH".
    iMod (own_update with "BOTH") as "[AUTH USER]".
    2: { iModIntro. iFrame. }
    rewrite comm. apply excl_auth_update.
  Qed.

  (** Resource-level operation specifications.  [new] consumes the currently
      tracked singleton state and replaces it with a fresh empty list. *)
  Definition new_spec : fspec :=
    fspec_simple
      (fun old_state : llist_state =>
        ((fun arg => ⌜arg = tt↑⌝ ∗ list_user old_state),
         (fun ret =>
            ∃ list_loc,
              ⌜ret = list_loc↑⌝ ∗ is_list list_loc [])))%I.

  Definition push_front_spec : fspec :=
    fspec_simple
      (fun '(list_loc, old, value) =>
        ((fun arg =>
            ⌜arg = (list_loc, value)↑⌝ ∗ is_list list_loc old),
         (fun ret =>
            ⌜ret = tt↑⌝ ∗ is_list list_loc (value :: old))))%I.

  Definition get_spec : fspec :=
    fspec_simple
      (fun '(list_loc, values, index) =>
        ((fun arg =>
            ⌜arg = (list_loc, index)↑⌝ ∗ is_list list_loc values),
         (fun ret =>
            ⌜ret = (values !! index)↑⌝ ∗
            is_list list_loc values)))%I.

  (** If you're not familiar with the notation [!!], then you can try these. **)
  (* Locate "_ !! _". *)
  (* Print lookup. *)
  (* Compute [1; 2] !! 0. *)
  (* Compute [1; 2] !! 2. *)

  Definition sp : specmap :=
    {[fid LListHdr.new @ new_spec;
      fid LListHdr.push_front @ push_front_spec;
      fid LListHdr.get @ get_spec]}.

  Definition scopes : list string := ["LList"].

  Definition fnsems : fnsemmap :=
    {[fid LListHdr.new #
        (msk_scp scopes msk_true, (fsp_some new_spec, fbody_trivial));
      fid LListHdr.push_front #
        (msk_scp scopes msk_true,
          (fsp_some push_front_spec, fbody_trivial));
      fid LListHdr.get #
        (msk_scp scopes msk_true,
          (fsp_some get_spec, fbody_trivial))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  (** The library proof and the client proof consume different halves.  The
      final theorem combines them.  Keeping these conditions separate makes
      the two contextual refinements compositional. *)
  Definition auth_init : iProp Σ := list_auth None.
  Definition frag_init : iProp Σ := list_uninit.
  Definition init_cond : iProp Σ := (frag_init ∗ auth_init)%I.

  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End LListA. End LListA.

(** Allocate the authoritative resource and its matching user
    fragment.  The final behavioral-refinement theorem uses this lemma to
    establish [LListA.init_cond]. *)
Lemma llist_alloc
    `{!crisG Γ Σ α β τ _S _I, !llistGpreS} :
  ⊢ o=> ∃ (_ : llistGS), LListA.init_cond.
Proof.
  iMod (own_alloc (●E (None : llist_state) ⋅ ◯E (None : llist_state)))
    as "[%γ LIST]".
  { apply excl_auth_valid. }
  pose (Build_llistGS _ _ _ _ _ _ _ _ _ γ) as Hlist.
  rewrite own_op. iExists Hlist. iModIntro.
  rewrite /LListA.init_cond /LListA.frag_init /LListA.list_uninit
    /LListA.list_user /LListA.auth_init /LListA.list_auth.
  rewrite comm. iExact "LIST".
Qed.
