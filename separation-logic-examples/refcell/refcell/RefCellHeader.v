(** * Dynamically Checked Reference Cell Interface *)

From CRIS.common Require Import CRIS.
From refcell.frac_mem Require Export FracMemHeader.

Module RefCellHdr.
  Definition new_refcell :=
    fnsig "RefCell.new_refcell" (fntyp memval loc).
  Definition try_borrow :=
    fnsig "RefCell.try_borrow" (fntyp loc (option loc)).
  Definition try_borrow_mut :=
    fnsig "RefCell.try_borrow_mut" (fntyp loc (option loc)).
  Definition drop :=
    fnsig "RefCell.drop" (fntyp loc unit).
End RefCellHdr.
