(** * Linked-List Stack Implementation *)

From CRIS.common Require Import CRIS.
From mem_answer Require Import MemHeader.
From stack_answer Require Export StackHeader.

Module StackI. Section StackI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["Stack"].

  Definition new_stack : unit → itree crisE loc :=
    λ _,
      l <- ccallU MemHdr.alloc tt;;
      _ <- ccallU MemHdr.store (l, Vloc None);;
      Ret l.

  Definition push : loc * nat → itree crisE unit :=
    λ '(l, value),
      node <- ccallU MemHdr.alloc tt;;
      raw_head <- ccallU MemHdr.load l;;
      head <- match raw_head with
              | Vloc head => Ret head
              | _ => triggerUB
              end;;
      _ <- ccallU MemHdr.store
        (node, Vpair (Vnat value) (Vloc head));;
      _ <- ccallU MemHdr.store (l, Vloc (Some node));;
      Ret tt.

  Definition pop : loc → itree crisE (option nat) :=
    λ l,
      raw_head <- ccallU MemHdr.load l;;
      head <- match raw_head with
              | Vloc head => Ret head
              | _ => triggerUB
              end;;
      match head with
      | None => Ret None
      | Some node =>
          raw_node <- ccallU MemHdr.load node;;
          match raw_node with
          | Vpair (Vnat value) (Vloc next) =>
              _ <- ccallU MemHdr.store (l, Vloc next);;
              Ret (Some value)
          | _ => triggerUB
          end
      end.

  Definition fnsems : fnsemmap :=
    {[fid StackHdr.new_stack #
        (msk_scp scopes msk_true,
          (None, cfunU StackHdr.new_stack new_stack));
      fid StackHdr.push #
        (msk_scp scopes msk_true,
          (None, cfunU StackHdr.push push));
      fid StackHdr.pop #
        (msk_scp scopes msk_true,
          (None, cfunU StackHdr.pop pop))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End StackI. End StackI.
