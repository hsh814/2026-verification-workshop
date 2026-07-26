(** * Abstract Stack Predicate and Specifications *)

From CRIS.common Require Import CRIS.
From mem_answer Require Import MemA.
From stack_answer Require Export StackHeader.

Section stack_resources.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  (** [linked_list head values] owns exactly the nodes reachable from [head].
      The list is top-first: [value :: values] means [value] is popped next. *)
  Fixpoint linked_list
      (head : option loc) (values : list nat) : iProp Σ :=
    match values with
    | [] => ⌜head = None⌝
    | value :: values' =>
        ∃ node next,
          ⌜head = Some node⌝ ∗
          node ↦ Vpair (Vnat value) (Vloc next) ∗
          linked_list next values'
    end%I.

  (** A stable header cell contains the current linked-list head. *)
  Definition is_stack (l : loc) (values : list nat) : iProp Σ :=
    (∃ head, l ↦ Vloc head ∗ linked_list head values)%I.
End stack_resources.

Module StackA. Section StackA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Definition new_stack_spec : fspec :=
    fspec_simple
      (λ _ : unit,
        ((λ arg, ⌜arg = tt↑⌝),
         (λ ret, ∃ l, ⌜ret = l↑⌝ ∗ is_stack l [])))%I.

  Definition push_spec : fspec :=
    fspec_simple
      (λ '(l, values, value),
        ((λ arg,
            ⌜arg = (l, value)↑⌝ ∗ is_stack l values),
         (λ ret,
            ⌜ret = tt↑⌝ ∗ is_stack l (value :: values))))%I.

  Definition pop_spec : fspec :=
    fspec_simple
      (λ '(l, values),
        ((λ arg, ⌜arg = l↑⌝ ∗ is_stack l values),
         (λ ret,
            match values with
            | [] =>
                ⌜ret = (None : option nat)↑⌝ ∗ is_stack l []
            | value :: values' =>
                ⌜ret = (Some value)↑⌝ ∗ is_stack l values'
            end)))%I.

  Definition sp : specmap :=
    {[fid StackHdr.new_stack @ new_stack_spec;
      fid StackHdr.push @ push_spec;
      fid StackHdr.pop @ pop_spec]}.

  Definition scopes : list string := ["Stack"].

  Definition fnsems : fnsemmap :=
    {[fid StackHdr.new_stack #
        (msk_scp scopes msk_true,
          (fsp_some new_stack_spec, fbody_trivial));
      fid StackHdr.push #
        (msk_scp scopes msk_true,
          (fsp_some push_spec, fbody_trivial));
      fid StackHdr.pop #
        (msk_scp scopes msk_true,
          (fsp_some pop_spec, fbody_trivial))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End StackA. End StackA.
