(** * Proof that [FracMemI] Refines [FracMemA] *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From lib Require Import mono_nat.
From refcell.frac_mem_answer Require Import FracMemA FracMemI.

Module FracMemIA. Section FracMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !frac_memGS}.
  Local Existing Instances
    frac_memGS_pre frac_mem_mapG frac_mem_countG.

  Context (sp : specmap).

  Local Definition FracMemAMod := FracMemA.t sp.
  Local Definition FracMemIMod := FracMemI.t.

  Definition Ist : ist_type Σ :=
    (λ st_src st_tgt,
      ∃ m : FracMemState.t,
        ⌜st_src = ∅ ∧
          st_tgt = {[FracMemI.v_mem # m↑]}⌝ ∗
        ghost_map_auth frac_mem_map_name 1
          m.(FracMemState.cells) ∗
        mono_nat_auth_own frac_mem_count_name 1
          m.(FracMemState.count))%I.

  Lemma simF_alloc :
    ISim.sim_fun open FracMemAMod FracMemIMod Ist
      (fid FracMemHdr.alloc).
  Proof.
    cStartFunSim.
    rewrite /FracMemI.alloc.
    cStepsS.
    iDestruct "ASM" as "[-> ->]".
    iDestruct "IST" as (m) "(%ST & MAP & COUNT)".
    destruct ST as [-> ->].
    cStepsT.
    set (l := fresh (dom m.(FracMemState.cells))).
    assert (FRESH : m.(FracMemState.cells) !! l = None).
    { apply not_elem_of_dom. subst l. apply is_fresh. }
    iMod (ghost_map_insert l Vundef with "MAP")
      as "[MAP CELL]"; first exact FRESH.
    cForceS (l↑). cStepsS. cForcesS.
    iSplitL "CELL".
    { iSplitR "CELL"; first done.
      iExists l. iSplitR "CELL"; first done.
      rewrite /pointsto. iExact "CELL". }
    cStep.
    rewrite /ist_with_eq /Ist.
    iSplitR "MAP COUNT"; first done.
    iExists (FracMemState.mk
      (<[l := Vundef]> m.(FracMemState.cells))
      m.(FracMemState.count)).
    iSplitR "MAP COUNT"; first done.
    iCombine "MAP COUNT" as "RES". iExact "RES".
  Qed.

  Lemma simF_load :
    ISim.sim_fun open FracMemAMod FracMemIMod Ist
      (fid FracMemHdr.load).
  Proof.
    cStartFunSim.
    rewrite /FracMemI.load.
    cStepsS.
    destruct _q as [[l q] v].
    iDestruct "ASM" as "[-> [-> CELL]]".
    iDestruct "IST" as (m) "(%ST & MAP & COUNT)".
    destruct ST as [-> ->].
    cStepsT.
    iEval (rewrite /pointsto) in "CELL".
    iPoseProof (ghost_map_lookup with "MAP CELL") as "%HIT".
    rewrite /FracMemState.load HIT.
    cStepsT.
    iMod (mono_nat_own_update (S m.(FracMemState.count))
      with "COUNT") as "[COUNT _]"; first lia.
    cForceS (v↑). cStepsS. cForcesS.
    iSplitL "CELL".
    { iSplitR "CELL"; first done.
      iSplitR "CELL"; first done.
      rewrite /pointsto. iExact "CELL". }
    cStep.
    rewrite /ist_with_eq /Ist.
    iSplitR "MAP COUNT"; first done.
    iExists (FracMemState.mk
      m.(FracMemState.cells) (S m.(FracMemState.count))).
    iSplitR "MAP COUNT"; first done.
    iCombine "MAP COUNT" as "RES". iExact "RES".
  Qed.

  Lemma simF_store :
    ISim.sim_fun open FracMemAMod FracMemIMod Ist
      (fid FracMemHdr.store).
  Proof.
    cStartFunSim.
    rewrite /FracMemI.store.
    cStepsS.
    destruct _q as [[l old] new].
    iDestruct "ASM" as "[-> [-> CELL]]".
    iDestruct "IST" as (m) "(%ST & MAP & COUNT)".
    destruct ST as [-> ->].
    cStepsT.
    iEval (rewrite /pointsto) in "CELL".
    iPoseProof (ghost_map_lookup with "MAP CELL") as "%HIT".
    rewrite /FracMemState.store HIT.
    cStepsT.
    iMod (ghost_map_update new with "MAP CELL")
      as "[MAP CELL]".
    iMod (mono_nat_own_update (S m.(FracMemState.count))
      with "COUNT") as "[COUNT _]"; first lia.
    cForceS (tt↑). cStepsS. cForcesS.
    iSplitL "CELL".
    { iSplitR "CELL"; first done.
      iSplitR "CELL"; first done.
      rewrite /pointsto. iExact "CELL". }
    cStep.
    rewrite /ist_with_eq /Ist.
    iSplitR "MAP COUNT"; first done.
    iExists (FracMemState.mk
      (<[l := new]> m.(FracMemState.cells))
      (S m.(FracMemState.count))).
    iSplitR "MAP COUNT"; first done.
    iCombine "MAP COUNT" as "RES". iExact "RES".
  Qed.

  Lemma simF_get_cnt :
    ISim.sim_fun open FracMemAMod FracMemIMod Ist
      (fid FracMemHdr.get_cnt).
  Proof.
    cStartFunSim.
    rewrite /FracMemI.get_cnt.
    cStepsS.
    iDestruct "ASM" as "[-> [-> SNAP]]".
    iDestruct "IST" as (m) "(%ST & MAP & COUNT)".
    destruct ST as [-> ->].
    cStepsT.
    iEval (rewrite /count_snapshot) in "SNAP".
    iPoseProof (mono_nat_lb_own_valid with "COUNT SNAP")
      as "%VALID".
    destruct VALID as [_ LE].
    iPoseProof (mono_nat_lb_own_get with "COUNT") as "#SNAP'".
    cForceS (m.(FracMemState.count)↑). cStepsS. cForcesS.
    iSplitR "MAP COUNT".
    { iSplitR; first done.
      iExists m.(FracMemState.count).
      iSplitR; first (iPureIntro; split; done).
      rewrite /count_snapshot. iExact "SNAP'". }
    cStep.
    rewrite /ist_with_eq /Ist.
    iSplitR "MAP COUNT"; first done.
    iExists m. iSplitR "MAP COUNT"; first done.
    iCombine "MAP COUNT" as "RES". iExact "RES".
  Qed.

  Lemma sim :
    ISim.t open FracMemAMod FracMemIMod FracMemA.auth_init Ist.
  Proof.
    cStartModSim.
    - iIntros "INIT".
      iDestruct "INIT" as "[MAP COUNT]".
      rewrite /Ist.
      iExists FracMemState.empty.
      iSplitR "MAP COUNT"; first done.
      iCombine "MAP COUNT" as "RES". iExact "RES".
    - apply simF_alloc.
    - apply simF_load.
    - apply simF_store.
    - apply simF_get_cnt.
  Qed.
End FracMemIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !frac_memGS}.

  Lemma ctxr (sp : specmap) :
    FracMemA.auth_init ⊢
      ctx_refines FracMemI.t (FracMemA.t sp).
  Proof.
    eapply main_adequacy, sim.
  Qed.
End contextual_refinement. End FracMemIA.
