(** * Linked List Implementatino Module **)

From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemHeader.
From prime Require Export LListHeader.

(** Given implementation.  Each location returned by [new] is a stable,
    one-cell list header.  Its head pointer changes as nodes are inserted, but
    the header location passed to [push_front] and [get] never changes.

    A node occupies two Imp-memory cells: [(value, next_pointer)].  The null
    pointer is [Vnullptr]. *)
Module LListI. Section LListI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := ["LList"].

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
          (None, cfunU LListHdr.new new));
      fid LListHdr.push_front #
        (msk_scp scopes msk_true,
          (None, cfunU LListHdr.push_front push_front));
      fid LListHdr.get #
        (msk_scp scopes msk_true,
          (None, cfunU LListHdr.get get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End LListI. End LListI.
