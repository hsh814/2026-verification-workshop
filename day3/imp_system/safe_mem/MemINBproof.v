From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemHeader MemI MemA MemIAproof.
From CRIS.imp_system.safe_mem Require Import MemNB.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.filter Require Import CallFilter.
From iris.algebra Require Import auth excl agree csum functions dfrac_agree.

Module MemINB. Section MemINB.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.
  Local Existing Instances memGS_memGSpreS mem_inG.

  Context (genv : GEnv.t).
  Context (sp: specmap).
  Context (MEM_IN_SP: MemNB.sp ⊆ sp).

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    λ st_src st_tgt,
      ((∃ (mem_tgt : Mem.t) (mem_src : MemA._memRA),
      ⌜st_tgt = {[MemI.v_mem # mem_tgt↑]} 
      ∧ st_src = {[MemNB.v_mem # mem_tgt↑]} 
      ∧ sim_mem mem_src mem_tgt ∧ mem_wf mem_tgt⌝ ∗
      ( |==> own mem_name (● mem_src))))%I.

  Local Definition MemNB := (MemNB.t sp genv).
  Local Definition MemI := (MemI.t genv).
  Local Definition IstFull := (IstProd (IstSB MemNB.(Mod.scopes) Ist) IstEq).

  Definition mem_get (mem: MemA._memRA) b ofs :=
    match or_else (mem b ofs) (to_dfrac_agree (DfracOwn 1) Vundef) with
    | (_,v) => or_else (nth_error v.(agree_car) 0) Vundef
    end.

  Local Definition state : Type := gmap key (option Any.t).
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.

  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Lemma simF_alloc : ISim.sim_fun open MemNB MemI IstFull (fid MemHdr.alloc).
  Proof using.
    cStartFunSim. rewrite /MemI.alloc /MemNB.alloc. cStepsS.
    rename _q into sz, _q0 into varg.
    iDestruct "ASM" as "[-> [-> %]]".

    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> [-> [%Hsim %Hwf]]] >B]]]] & ->)".
    cStepsT. case_bool_decide; [|lia]. cStepsT.

    rename _q into pad.
    set (blk := Mem.nb mem_tgt + pad).
    iPoseProof (own_valid with "B") as "%".
    iPoseProof (mem_ra_alloc with "B") as ">B"; et.
    iDestruct "B" as "[BLK WHT]". iPoseProof (points_to_transform with "WHT") as "WHT".

    cStepsS. case_bool_decide; ss. cForceS pad. cStepsS.
    cForceS ((Vptr (blk, 0%Z)) ↑). cForcesS. iFrame. iSplit; eauto.
    cStep. iFrame.
    repeat (iSplit; first done).
    iExists _, _, _, _; iSplit; [iPureIntro; split; refl|iSplit; eauto].
    repeat (iSplit; eauto).
    iExists _; iSplit; eauto.
    iPureIntro; esplits; eauto; cycle 1.
    { intros ??? Hwf2; ss.
      rewrite /update in Hwf2; case_match; subst; ss.
      rewrite /mem_wf in Hwf; exploit Hwf; eauto; nia.
    }

    intros blk' ofs'; rewrite ?discrete_fun_lookup_op /= Z.add_0_l Z.sub_0_r length_replicate.
    destruct (mem_tgt.(Mem.cnts) blk ofs') eqn:E.
    { exfalso. exploit Hwf; et. nia. }
    ss. hexploit (Hsim blk ofs'); et.
    rewrite E. intro U. des; ss.

    case_bool_decide as Hblkofs; [destruct Hblkofs as [Hblk Hofs]|].
    { rewrite lookup_replicate_2; [subst|lia]; rewrite U left_id; right; esplits; eauto.
      rewrite /update; destruct (dec _ _); ss; case_bool_decide; ss.
    }
    rewrite right_id /update; destruct (_ blk' ofs') eqn : ?; hexploit (Hsim blk' ofs');
        i; des; destruct (dec _ _); ss; try case_bool_decide; naive_solver.
  (*SLOW*)Qed.

  Lemma simF_free : ISim.sim_fun open MemNB MemI IstFull (fid MemHdr.free).
  Proof using.
    cStartFunSim. rewrite /MemI.free /MemNB.free.
    cStepS. destruct _q as [[blk ofs] v].
    cStepS. rename _q into varg. cStepS.
    iDestruct "ASM" as "[-> [-> ↦]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> [-> [%Hsim %Hwf]]] >B]]]] & ->)".

    cStepsS. cStepsT.

    iPoseProof (mem_ra_lookup with "[B ↦]") as "[%HIT ->]"; et; iFrame. cStepsT.

    cStepsS. cForceS. iMod (mem_ra_free with "[B ↦]") as "H"; et; iFrame.
    cForcesS; iSplit; eauto.
    cStep; iFrame. repeat (iSplit; et).
    iExists _, _, _, _; repeat (iSplit; et).
    iExists _; iSplit; eauto.
    iPureIntro. esplits; eauto.
    - ii. s. rewrite /mem_ra_upd /update.
      repeat destruct dec; case_bool_decide; des; ss; subst; naive_solver.
    - rewrite /update. ii. ss. repeat destruct dec; ss; subst; et.
  (*SLOW*)Qed.

  Lemma simF_load : ISim.sim_fun open MemNB MemI IstFull (fid MemHdr.load).
  Proof using.
    cStartFunSim. rewrite /MemI.load /MemNB.load.
    cStepS. destruct _q as [[[blk ofs] q] v]. cStepsS.

    iDestruct "ASM" as "[-> [-> ↦]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> [-> [%Hsim %Hwf]]] >B]]]] & ->)".

    cStepsT. cStepsS.

    iPoseProof (mem_ra_lookup with "[B ↦]") as "[%HIT ->]"; et; iFrame. cStepsT.
    cForcesS. iFrame. iSplit; eauto.
    cStep. iFrame. repeat (iSplit; et).
    iExists _, _, _, _; repeat (iSplit; et).
  (*SLOW*)Qed.

  Lemma simF_store : ISim.sim_fun open MemNB MemI IstFull (fid MemHdr.store).
  Proof using.
    cStartFunSim. rewrite /MemI.store /MemNB.store.
    cStepS. destruct _q as [[[blk ofs] q] v]. cStepsS.

    iDestruct "ASM" as "[-> [-> ↦]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> [-> [%Hsim %Hwf]]] >B]]]] & ->)".

    cStepsS. cStepsT.

    iPoseProof (mem_ra_lookup with "[B ↦]") as "[%HIT %HIT2]"; et; iFrame; rewrite HIT2. cStepsT.
    iMod (mem_ra_update with "[B ↦]") as "[B ↦]"; et; iFrame.

    cStepsS. cForcesS. iFrame. iSplit; eauto.
    cStep. iFrame. repeat (iSplit; et).
    iExists _, _, _, _; repeat (iSplit; et).
    iExists _; iSplit; et.
    iPureIntro. split; eauto. esplits.
    - ii. s. rewrite /mem_ra_upd /update.
      repeat destruct dec; ss; subst; case_bool_decide; des; naive_solver.
    - ii. s. rewrite /mem_ra_upd /update.
      repeat destruct dec; ss; subst; case_bool_decide; des; naive_solver.
    - ii; ss; repeat destruct dec; ss; subst; eauto.
  (*SLOW*)Qed.

  Lemma simF_cmp : ISim.sim_fun open MemNB MemI IstFull (fid MemHdr.cmp).
  Proof using.
    cStartFunSim. rewrite /MemI.cmp /MemNB.cmp.
    cStepS. destruct _q as [[[v_old v_new] v_cmp] Cmp]. cStepsS.
    iDestruct "ASM" as "[-> [[-> %Hcmp2] [Cmp Cmp2]]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> [-> [%Hsim %Hwf]]] >B]]]] & ->)".

    cStepsT. cStepsS.

    iMod ("Cmp2" with "Cmp") as (????) "[C1 [C2 C3]]".
    iPoseProof (mem_ra_cmp with "[B C1 C2]") as "->"; eauto; iFrame.
    iMod ("C3" with "[$]").

    cStepsT. cStepsS.
    case_bool_decide; clarify; ss.
    { cForcesS. iFrame. iSplit; eauto. cStep. iFrame. iSplit; eauto.
      iExists _, _, _, _; iSplit; eauto. }
    { cForcesS. iFrame. iSplit; eauto.
      { iPureIntro. move : Hcmp2; rewrite /MemA.compare_val; des_ifs; i; clarify. }
      cStep. iFrame. iSplit; eauto.
      iExists _, _, _, _; iSplit; eauto. }
  (*SLOW*)Qed.

  Lemma simF_cas : ISim.sim_fun open MemNB MemI IstFull (fid MemHdr.cas).
  Proof using MEM_IN_SP.
    cStartFunSim. rewrite /MemI.cas /MemNB.cas.
    cStepS. destruct _q as [[[[[[blk ofs ] v_old] v_new] v_upd] v_cmp] Cmp]. cStepsS.
    iDestruct "ASM" as "[-> [[-> %Hcmp2] [↦ [Cmp Cmp2]]]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> [-> [%Hsim %Hwf]]] >B]]]] & ->)".

    cStepsT. cStepsS. rewrite /SModTr.HoareCall. cStepsS.
    iPoseProof (mem_ra_lookup with "[B ↦]") as "[% %Hlookup]"; eauto; [iFrame|].

    (* Load *)
    erewrite lookup_weaken; try eapply MEM_IN_SP; eauto.
    cForceS (blk, ofs, 1%Qp, v_old). cForcesS. iFrame; iSplit; eauto.
    destruct (bool_decide ("MemAtom.load" ∈ MemHdr.exports ∧ msk_true Any.t (subevent Any.t (Call "MemAtom.load" [Vptr (blk, ofs)] ↑)))) eqn:BD; cycle 1.
    { case_bool_decide; des; ss. exfalso. eapply H2; ss. }
    clear BD. cStepsS. cCall "B" as (???) "IST".
    { iFrame; iExists _, _, _, _; iPureIntro; esplits; eauto. }
    cStepsS. iDestruct "ASM" as "[-> [B ->]]".
    cStepsS; cStepsT.

    (* Cmp *)
    rewrite /SModTr.HoareCall.
    erewrite lookup_weaken; try eapply MEM_IN_SP; eauto; ss.
    cForceS (v_old, v_new, v_cmp, Cmp).
    cForceS ([v_old; v_new] ↑). cForcesS. iFrame. iSplit; eauto.
    destruct (bool_decide
      ("MemAtom.cmp" ∈ MemHdr.exports ∧
       msk_true Any.t
         (subevent Any.t (Call "MemAtom.cmp" [v_old; v_new] ↑))))
      eqn:BD; cycle 1.
    { case_bool_decide; des; ss. exfalso. eapply H2; ss. }
    clear BD. cStepsS. cCall "IST" as (???) "IST".
    cStepsS. iDestruct "ASM" as "[-> [-> Cmp]]".
    cStepsS; cStepsT.

    repeat case_bool_decide; simplify_eq.
    { (* Store *)
      cStepsS. cStepsT. rewrite /SModTr.HoareCall. cStepsS.
      erewrite lookup_weaken; try eapply MEM_IN_SP; eauto; ss.
      cForceS (blk, ofs, v_old, v_upd). cForcesS.
      iFrame; iSplit; eauto.
      destruct (bool_decide
        ("MemAtom.store" ∈ MemHdr.exports ∧
         msk_true Any.t
           (subevent Any.t
             (Call "MemAtom.store" [Vptr (blk, ofs); v_upd] ↑))))
        eqn:BD; cycle 1.
      { case_bool_decide; des; ss. exfalso. eapply H2; ss. }
      clear BD. cStepsS. cCall "IST" as (???) "IST".
      cStepsS. iDestruct "ASM" as "[-> [B ->]]".
      cStepsS; cStepsT.
      cForceS (v_old ↑). cForcesS. iFrame.
      iSplit; first done. cStep. iFrame. done.
    }
    cStepsS; cStepsT.
    cForceS (v_old ↑). cForcesS.
    case_bool_decide; simplify_eq. iFrame.
    iSplit; first done. cStep. iFrame. done.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MemNB MemI (MemA.init_cond genv) IstFull.
  Proof using MEM_IN_SP.
    cStartModSim.
    { iIntros "?"; iFrame.
      iExists _, _, ∅, ∅; iSplit; eauto.
      { rewrite ?right_id //. }
      repeat (iSplit; ss).
      iExists _; iSplit; ss. iPureIntro; split; ss.
      split.
      { ii. rewrite /mem_init_val /Mem.load_mem.
        rewrite /mbind /option_bind.
        des_ifs; bsimpl; des; subst; ss; rewrite ?Heq0 ?Heq1 ?Heq2; des_ifs; et.
      }
      split.
      { ii. rewrite /mem_init_val /Mem.load_mem.
        rewrite /mbind /option_bind.
        des_ifs; bsimpl; des; subst; ss; rewrite ?Heq0 ?Heq1 ?Heq2; des_ifs; et.
      }
      { intros ? ? ? H'. revert H'. rewrite /Mem.load_mem /mbind /option_bind; s. des_ifs.
        i. inv H'. eapply lookup_lt_Some; eauto.
      }
    }
    { apply simF_alloc. }
    { apply simF_free. }
    { apply simF_load. }
    { apply simF_store. }
    { apply simF_cmp. }
    { apply simF_cas. }
  (*SLOW*)Qed.
End MemINB.
Section MemINB.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !memGS}.

  Lemma ctxr sp genv (MEM_IN_SP : MemNB.sp ⊆ sp) :
    MemA.init_cond genv ⊢ ctx_refines (MemI.t genv) (MemNB.t sp genv).
  Proof using.
    eapply main_adequacy, sim; eauto.
  Qed.
End MemINB. End MemINB.
