(** * Exercise: Reference Cell Resources and Specifications

    The public specifications are supplied.  Complete the two logical
    resources using [ghost_map], then allocate their initial ghost state.
    Do not define these resources with a low-level [own] expression. *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From refcell.frac_mem Require Import FracMemA.
From refcell.refcell Require Export RefCellHeader.

(** A registry entry records the protected location and the ghost name of
    that cell's active-borrow registry. *)
Definition refcell_info : Type := loc * gname.

Class refcellGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] refcell_registryG ::
    ghost_mapG Γ loc refcell_info;
  #[local] refcell_borrowG ::
    ghost_mapG Γ nat Qp;
}.

Class refcellGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] refcellGS_pre :: refcellGpreS;
  refcell_registry_name : gname;
}.

Definition refcellΓ : HRA :=
  ##[ghost_mapΣ loc refcell_info; ghost_mapΣ nat Qp].

Global Instance subG_refcellGpreS
    `{!crisG Γ Σ α β τ _S _I} :
  subG refcellΓ Γ -> refcellGpreS.
Proof. solve_inG. Defined.

Local Existing Instances
  refcellGS_pre refcell_registryG refcell_borrowG.

Global Instance refcell_registryGS
    `{!crisG Γ Σ α β τ _S _I, !refcellGS} :
  ghost_mapG Σ loc refcell_info :=
  @subHG_ghost_map loc loc_eq_dec loc_countable refcell_info Γ Σ
    (subG_subHG Γ Σ _S) refcell_registryG.

Global Instance refcell_borrowGS
    `{!crisG Γ Σ α β τ _S _I, !refcellGS} :
  ghost_mapG Σ nat Qp :=
  @subHG_ghost_map nat Nat.eq_dec nat_countable Qp Γ Σ
    (subG_subHG Γ Σ _S) refcell_borrowG.

Section resources.
  Context `{!crisG Γ Σ α β τ _S _I, !refcellGS}.

  (** TODO 1: define a persistent fact saying header [r] protects [l].
      Keep the mutable points-to resources in [Ist], not here. *)
  Definition RefCell (r l : loc) : iProp Σ.
  Admitted.

  (** TODO 2: prove that clients may freely duplicate [RefCell r l]. *)
  Global Instance RefCell_persistent r l :
    Persistent (RefCell r l).
  Admitted.

  (** TODO 3: define one linear ticket for an active fraction-[q] borrow.
      A hidden ticket identifier should make each successful borrow authorize
      exactly one [drop]. *)
  Definition Borrowed (r : loc) (q : Qp) : iProp Σ.
  Admitted.
End resources.

Module RefCellA. Section RefCellA.
  Context `{!crisG Γ Σ α β τ _S _I,
    !frac_memGS, !refcellGS}.

  (** Constructing a cell hides its value inside the implementation
      invariant and returns the persistent handle fact. *)
  Definition new_refcell_spec : fspec :=
    fspec_simple
      (fun value : memval =>
        ((fun arg => ⌜arg = value↑⌝),
         (fun ret =>
            ∃ r l,
              ⌜ret = r↑⌝ ∗ RefCell r l)))%I.

  (** A shared borrow either fails, or returns a read-only fraction [q < 1]
      together with its linear borrow ticket. *)
  Definition try_borrow_spec : fspec :=
    fspec_simple
      (fun '(r, l) =>
        ((fun arg =>
            ⌜arg = r↑⌝ ∗ RefCell r l),
         (fun ret =>
            RefCell r l ∗
            (⌜ret = (None : option loc)↑⌝ ∨
             ∃ q v,
               ⌜ret = (Some l)↑⌝ ∗ ⌜(q < 1)%Qp⌝ ∗
               l ↦{q} v ∗ Borrowed r q))))%I.

  (** A mutable borrow succeeds only when no other borrow is active.  It
      returns full ownership, hence read-write permission. *)
  Definition try_borrow_mut_spec : fspec :=
    fspec_simple
      (fun '(r, l) =>
        ((fun arg =>
            ⌜arg = r↑⌝ ∗ RefCell r l),
         (fun ret =>
            RefCell r l ∗
            (⌜ret = (None : option loc)↑⌝ ∨
             ∃ v,
               ⌜ret = (Some l)↑⌝ ∗
               l ↦ v ∗ Borrowed r 1))))%I.

  (** Dropping a borrow returns its fraction to the cell invariant. *)
  Definition drop_spec : fspec :=
    fspec_simple
      (fun '(r, l, q, v) =>
        ((fun arg =>
            ⌜arg = r↑⌝ ∗ RefCell r l ∗
            Borrowed r q ∗ l ↦{q} v),
         (fun ret =>
            ⌜ret = tt↑⌝ ∗ RefCell r l)))%I.

  Definition sp : specmap :=
    {[fid RefCellHdr.new_refcell @ new_refcell_spec;
      fid RefCellHdr.try_borrow @ try_borrow_spec;
      fid RefCellHdr.try_borrow_mut @ try_borrow_mut_spec;
      fid RefCellHdr.drop @ drop_spec]}.

  Definition scopes : list string := ["RefCell"].

  Definition fnsems : fnsemmap :=
    {[fid RefCellHdr.new_refcell #
        (msk_scp scopes msk_true,
          (fsp_some new_refcell_spec, fbody_trivial));
      fid RefCellHdr.try_borrow #
        (msk_scp scopes msk_true,
          (fsp_some try_borrow_spec, fbody_trivial));
      fid RefCellHdr.try_borrow_mut #
        (msk_scp scopes msk_true,
          (fsp_some try_borrow_mut_spec, fbody_trivial));
      fid RefCellHdr.drop #
        (msk_scp scopes msk_true,
          (fsp_some drop_spec, fbody_trivial))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition auth_init : iProp Σ :=
    ghost_map_auth refcell_registry_name 1
      (∅ : gmap loc refcell_info).

  Definition t (sp : specmap) : Mod.t := SMod.to_mod sp smod.
End RefCellA. End RefCellA.

(** TODO 4: allocate the initially empty persistent registry. *)
Lemma refcell_alloc
    `{!crisG Γ Σ α β τ _S _I, !refcellGpreS} :
  ⊢ o=> ∃ (_ : refcellGS), RefCellA.auth_init.
Admitted.
