(** * Linked-List Map Implementation *)

From CRIS.common Require Import CRIS.
From mem_answer Require Import MemHeader.
From map.linked_list_answer Require Export MapHeader.

(** Every map has a stable header containing its current head pointer.
    A node stores a key, an optional live value, and its next pointer.
    [Vundef] is a tombstone; historical keys therefore remain unique even
    after deletion. *)
Module MapI. Section MapI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition node_value (value : option nat) : memval :=
    match value with
    | Some value => Vnat value
    | None => Vundef
    end.

  Definition node_contents
      (key : nat) (value : option nat) (next : option loc) : memval :=
    Vpair (Vnat key) (Vpair (node_value value) (Vloc next)).

  Definition found : Type := loc * (memval * option loc).

  Definition find_step (key : nat) (cursor : option loc) :
      itree crisE (option loc + option found) :=
    match cursor with
    | None => Ret (inr None)
    | Some node =>
        raw <- ccallU MemHdr.load node;;
        match raw with
        | Vpair (Vnat key') (Vpair value (Vloc next)) =>
            if Nat.eq_dec key key'
            then Ret (inr (Some (node, (value, next))))
            else Ret (inl next)
        | _ => triggerUB
        end
    end.

  Definition find (key : nat) (head : option loc) :
      itree crisE (option found) :=
    ITree.iter (find_step key) head.

  Definition new_map : unit → itree crisE loc :=
    λ _,
      header <- ccallU MemHdr.alloc tt;;
      _ <- ccallU MemHdr.store (header, Vloc None);;
      Ret header.

  Definition insert : loc * (nat * nat) → itree crisE unit :=
    λ '(header, (key, value)),
      raw_head <- ccallU MemHdr.load header;;
      head <- match raw_head with
              | Vloc head => Ret head
              | _ => triggerUB
              end;;
      result <- find key head;;
      match result with
      | Some (node, (_, next)) =>
          _ <- ccallU MemHdr.store
            (node, node_contents key (Some value) next);;
          Ret tt
      | None =>
          node <- ccallU MemHdr.alloc tt;;
          _ <- ccallU MemHdr.store
            (node, node_contents key (Some value) head);;
          _ <- ccallU MemHdr.store (header, Vloc (Some node));;
          Ret tt
      end.

  Definition delete : loc * nat → itree crisE unit :=
    λ '(header, key),
      raw_head <- ccallU MemHdr.load header;;
      head <- match raw_head with
              | Vloc head => Ret head
              | _ => triggerUB
              end;;
      result <- find key head;;
      match result with
      | Some (node, (_, next)) =>
          _ <- ccallU MemHdr.store
            (node, node_contents key None next);;
          Ret tt
      | None => Ret tt
      end.

  Definition get : loc * nat → itree crisE (option nat) :=
    λ '(header, key),
      raw_head <- ccallU MemHdr.load header;;
      head <- match raw_head with
              | Vloc head => Ret head
              | _ => triggerUB
              end;;
      result <- find key head;;
      match result with
      | Some (_, (Vnat value, _)) => Ret (Some value)
      | Some (_, (Vundef, _)) => Ret None
      | Some _ => triggerUB
      | None => Ret None
      end.

  Definition scopes : list string := ["Map"].

  Definition fnsems : fnsemmap :=
    {[fid MapHdr.new_map #
        (msk_scp scopes msk_true,
          (None, cfunU MapHdr.new_map new_map));
      fid MapHdr.insert #
        (msk_scp scopes msk_true,
          (None, cfunU MapHdr.insert insert));
      fid MapHdr.delete #
        (msk_scp scopes msk_true,
          (None, cfunU MapHdr.delete delete));
      fid MapHdr.get #
        (msk_scp scopes msk_true,
          (None, cfunU MapHdr.get get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End MapI. End MapI.
