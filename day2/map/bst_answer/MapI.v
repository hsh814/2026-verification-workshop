(** * Unbalanced Binary-Search-Tree Map Implementation *)

From CRIS.common Require Import CRIS.
From mem_answer Require Import MemHeader.
From map.bst_answer Require Export MapHeader.

(** A map handle is a stable one-cell header containing the root pointer.
    Every tree node occupies one memory cell:

      [(key, (payload, (left, right)))]

    A live payload is [Vnat v].  [Vundef] is a tombstone left by deletion.
    Insertions revive tombstoned nodes in place. *)
Module MapI. Section MapI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["Map"].

  Definition node_val
      (key : nat) (payload : option nat)
      (left_child right_child : option loc) : memval :=
    Vpair (Vnat key)
      (Vpair
        (match payload with
         | Some value => Vnat value
         | None => Vundef
         end)
        (Vpair (Vloc left_child) (Vloc right_child))).

  Definition new_map : unit → itree crisE loc :=
    λ _,
      header <- ccallU MemHdr.alloc tt;;
      _ <- ccallU MemHdr.store (header, Vloc None);;
      Ret header.

  Definition get : loc * nat → itree crisE (option nat) :=
    λ '(header, query),
      raw_root <- ccallU MemHdr.load header;;
      root <- match raw_root with
              | Vloc root => Ret root
              | _ => triggerUB
              end;;
      iterC
        (λ cursor,
          match cursor with
          | None => Ret (inr None)
          | Some cursor =>
              raw_node <- ccallU MemHdr.load cursor;;
              match raw_node with
              | Vpair (Vnat key)
                  (Vpair payload
                    (Vpair (Vloc left_child) (Vloc right_child))) =>
                  match Nat.compare query key with
                  | Eq =>
                      match payload with
                      | Vnat value => Ret (inr (Some value))
                      | Vundef => Ret (inr None)
                      | _ => triggerUB
                      end
                  | Lt =>
                      Ret (inl left_child)
                  | Gt =>
                      Ret (inl right_child)
                  end
              | _ => triggerUB
              end
          end)
        root.

  Definition insert : loc * (nat * nat) → itree crisE unit :=
    λ '(header, (query, value)),
      raw_root <- ccallU MemHdr.load header;;
      root <- match raw_root with
              | Vloc root => Ret root
              | _ => triggerUB
              end;;
      match root with
      | None =>
          node <- ccallU MemHdr.alloc tt;;
          _ <- ccallU MemHdr.store
            (node, node_val query (Some value) None None);;
          _ <- ccallU MemHdr.store (header, Vloc (Some node));;
          Ret tt
      | Some root =>
          iterC
            (λ cursor,
              raw_node <- ccallU MemHdr.load cursor;;
              match raw_node with
              | Vpair (Vnat key)
                  (Vpair payload
                    (Vpair (Vloc left_child) (Vloc right_child))) =>
                  match Nat.compare query key with
                  | Eq =>
                      _ <- ccallU MemHdr.store
                        (cursor,
                          Vpair (Vnat key)
                            (Vpair (Vnat value)
                              (Vpair
                                (Vloc left_child) (Vloc right_child))));;
                      Ret (inr tt)
                  | Lt =>
                      match left_child with
                      | Some next => Ret (inl next)
                      | None =>
                          node <- ccallU MemHdr.alloc tt;;
                          _ <- ccallU MemHdr.store
                            (node, node_val query (Some value) None None);;
                          _ <- ccallU MemHdr.store
                            (cursor,
                              Vpair (Vnat key)
                                (Vpair payload
                                  (Vpair
                                    (Vloc (Some node)) (Vloc right_child))));;
                          Ret (inr tt)
                      end
                  | Gt =>
                      match right_child with
                      | Some next => Ret (inl next)
                      | None =>
                          node <- ccallU MemHdr.alloc tt;;
                          _ <- ccallU MemHdr.store
                            (node, node_val query (Some value) None None);;
                          _ <- ccallU MemHdr.store
                            (cursor,
                              Vpair (Vnat key)
                                (Vpair payload
                                  (Vpair
                                    (Vloc left_child) (Vloc (Some node)))));;
                          Ret (inr tt)
                      end
                  end
              | _ => triggerUB
              end)
            root
      end.

  Definition delete : loc * nat → itree crisE unit :=
    λ '(header, query),
      raw_root <- ccallU MemHdr.load header;;
      root <- match raw_root with
              | Vloc root => Ret root
              | _ => triggerUB
              end;;
      iterC
        (λ cursor,
          match cursor with
          | None => Ret (inr tt)
          | Some cursor =>
              raw_node <- ccallU MemHdr.load cursor;;
              match raw_node with
              | Vpair (Vnat key)
                  (Vpair payload
                    (Vpair (Vloc left_child) (Vloc right_child))) =>
                  match Nat.compare query key with
                  | Eq =>
                      _ <- ccallU MemHdr.store
                        (cursor,
                          node_val key None left_child right_child);;
                      Ret (inr tt)
                  | Lt =>
                      Ret (inl left_child)
                  | Gt =>
                      Ret (inl right_child)
                  end
              | _ => triggerUB
              end
          end)
        root.

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
