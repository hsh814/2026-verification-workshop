(** * Body-preserving linked-list specification *)

From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemHeader MemA.
From prime_safe_answer Require Export LListHeader.

(** Unlike a conventional abstract module, [LListA] keeps the concrete
    linked-list bodies.  Its specifications expose the Imp-memory ownership
    required to execute those bodies without undefined memory behavior. *)
Module LListA. Section LListA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Definition scopes := ["LList"].

  (** A concrete node contains an integer followed by its next pointer. *)
  Fixpoint nodes (cursor : val) (values : list nat) : iProp Σ :=
    match values with
    | [] => ⌜cursor = Vnullptr⌝
    | value :: values' =>
        ∃ bo next,
          ⌜cursor = Vptr bo⌝ ∗
          bo |-> [Vint (Z.of_nat value); next] ∗
          nodes next values'
    end%I.

  (** The stable list location owns the header cell containing [head]. *)
  Definition is_list
      (list_loc : val) (values : list nat) : iProp Σ :=
    (∃ bo head,
      ⌜list_loc = Vptr bo⌝ ∗
      bo ↦ head ∗
      nodes head values)%I.

  Definition new_spec : fspec :=
    fspec_simple
      (fun _ : unit =>
        ((fun arg => ⌜arg = tt↑⌝),
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

  Definition sp : specmap :=
    {[fid LListHdr.new @ new_spec;
      fid LListHdr.push_front @ push_front_spec;
      fid LListHdr.get @ get_spec]}.

  (** These are exactly the bodies from [LListI]. *)

  (*** C-like behavior

  val new(void) {
    val list_loc = Mem.alloc(1);
    Mem.store(list_loc, NULL);
    return list_loc;
  }
  ***)
  Definition new : unit -> itree crisE val :=
    fun _ =>
      'list_loc : val <- ccallU MemHdr.alloc [Vint 1];;
      '_ : val <- ccallU MemHdr.store [list_loc; Vnullptr];;
      Ret list_loc.

  (*** C-like behavior

  void push_front(val list_loc, nat value) {
    val old_head = Mem.load(list_loc);
    val new_node = Mem.alloc(2);
    Mem.store(new_node, value);
    Mem.store(new_node + 1, old_head);
    Mem.store(list_loc, new_node);
    return;
  }

  Thus [push_front] inserts at the front.  When the prime client pushes values
  in increasing order, the resulting list is in decreasing order.
  ***)
  Definition push_front : (val * nat) -> itree crisE unit :=
    fun '(list_loc, value) =>
      'old_head : val <- ccallU MemHdr.load [list_loc];;
      'new_node : val <- ccallU MemHdr.alloc [Vint 2];;
      'next_cell : val <- (vadd new_node (Vint 8))?;;
      '_ : val <- ccallU MemHdr.store [new_node; Vint (Z.of_nat value)];;
      '_ : val <- ccallU MemHdr.store [next_cell; old_head];;
      '_ : val <- ccallU MemHdr.store [list_loc; new_node];;
      Ret tt.

  (*** C-like behavior

  option<nat> get(val list_loc, nat index) {
    val cursor = Mem.load(list_loc);

    while (true) {
      if (cursor == NULL)
        return None;

      nat value = Mem.load(cursor);
      if (index == 0)
        return Some(value);

      cursor = Mem.load(cursor + 1);
      index--;
    }
  }

  [get] is total for every index: an index past the end returns [None].
  The [iterC] state contains the current pointer and remaining index.
  Failed memory accesses and malformed values produce undefined behavior;
  the representation invariant in [LListIAproof] rules them out.
  ***)
  Definition get : (val * nat) -> itree crisE (option nat) :=
    fun '(list_loc, index) =>
      'head : val <- ccallU MemHdr.load [list_loc];;
      iterC
        (fun '(cursor, remaining) =>
          if decide (cursor = Vnullptr)
          then Ret (inr None)
          else
            'value_raw : val <- ccallU MemHdr.load [cursor];;
            'value : Z <- (unint value_raw)?;;
            if Nat.eq_dec remaining 0
            then Ret (inr (Some (Z.to_nat value)))
            else
              'next_cell : val <- (vadd cursor (Vint 8))?;;
              'next_cursor : val <- ccallU MemHdr.load [next_cell];;
              Ret (inl (next_cursor, Nat.pred remaining)))
        (head, index).

  Definition fnsems : fnsemmap :=
    {[fid LListHdr.new #
        (msk_scp scopes msk_true,
          (fsp_some new_spec, cfunU LListHdr.new new));
      fid LListHdr.push_front #
        (msk_scp scopes msk_true,
          (fsp_some push_front_spec,
            cfunU LListHdr.push_front push_front));
      fid LListHdr.get #
        (msk_scp scopes msk_true,
          (fsp_some get_spec, cfunU LListHdr.get get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := emp%I.
  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End LListA. End LListA.
