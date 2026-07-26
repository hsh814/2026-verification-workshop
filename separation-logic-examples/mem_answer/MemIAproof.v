(** * Proof that [MemI] Refines [MemA] *)

From CRIS.common Require Import CRIS.
From CRIS.iris_system.lib Require Import ghost_map.
From lib Require Import mono_nat.
From mem_answer Require Import MemA MemI.

Module MemIA. Section MemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.
  Local Existing Instances memGS_pre mem_mapG mem_countG.

  Context (sp : specmap).

  Local Definition MemAMod := MemA.t sp.
  Local Definition MemIMod := MemI.t.

  (** The authoritative resources agree exactly with the physical target
      state.  The abstract specification module itself has no private state. *)
  Definition Ist : ist_type Σ :=
    (λ st_src st_tgt,
      ∃ m : MemState.t,
        ⌜st_src = ∅ ∧ st_tgt = {[MemI.v_mem # m↑]}⌝ ∗
        ghost_map_auth mem_map_name 1 m.(MemState.cells) ∗
        mono_nat_auth_own mem_count_name 1 m.(MemState.count))%I.

  Lemma simF_alloc :
    ISim.sim_fun open MemAMod MemIMod Ist (fid MemHdr.alloc).
  Proof.
    cStartFunSim.
    rewrite /MemI.alloc.
    cStepsS.
    iDestruct "ASM" as "[-> ->]".
    iDestruct "IST" as (m) "(%ST & MAP & COUNT)".
    destruct ST as [-> ->].
    cStepsT.
    set (l := fresh (dom m.(MemState.cells))).
    assert (FRESH : m.(MemState.cells) !! l = None).
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
    iExists (MemState.mk
      (<[l := Vundef]> m.(MemState.cells)) m.(MemState.count)).
    iSplitR "MAP COUNT"; first done.
    iCombine "MAP COUNT" as "RES". iExact "RES".
  Qed.

  Lemma simF_load :
    ISim.sim_fun open MemAMod MemIMod Ist (fid MemHdr.load).
  Proof.
    cStartFunSim.
    rewrite /MemI.load.
    cStepsS.
    destruct _q as [l v].
    iDestruct "ASM" as "[-> [-> CELL]]".
    iDestruct "IST" as (m) "(%ST & MAP & COUNT)".
    destruct ST as [-> ->].
    cStepsT.
    iEval (rewrite /pointsto) in "CELL".
    iPoseProof (ghost_map_lookup with "MAP CELL") as "%HIT".
    rewrite /MemState.load HIT.
    cStepsT.
    iMod (mono_nat_own_update (S m.(MemState.count))
      with "COUNT") as "[COUNT _]"; first lia.
    cForceS (v↑). cStepsS. cForcesS.
    iSplitL "CELL".
    { iSplitR "CELL"; first done.
      iSplitR "CELL"; first done.
      rewrite /pointsto. iExact "CELL". }
    cStep.
    rewrite /ist_with_eq /Ist.
    iSplitR "MAP COUNT"; first done.
    iExists (MemState.mk
      m.(MemState.cells) (S m.(MemState.count))).
    iSplitR "MAP COUNT"; first done.
    iCombine "MAP COUNT" as "RES". iExact "RES".
  Qed.

  Lemma simF_store :
    ISim.sim_fun open MemAMod MemIMod Ist (fid MemHdr.store).
  Proof.
    cStartFunSim.
    rewrite /MemI.store.
    cStepsS.
    destruct _q as [[l old] new].
    iDestruct "ASM" as "[-> [-> CELL]]".
    iDestruct "IST" as (m) "(%ST & MAP & COUNT)".
    destruct ST as [-> ->].
    cStepsT.
    iEval (rewrite /pointsto) in "CELL".
    iPoseProof (ghost_map_lookup with "MAP CELL") as "%HIT".
    rewrite /MemState.store HIT.
    cStepsT.
    iMod (ghost_map_update new with "MAP CELL")
      as "[MAP CELL]".
    iMod (mono_nat_own_update (S m.(MemState.count))
      with "COUNT") as "[COUNT _]"; first lia.
    cForceS (tt↑). cStepsS. cForcesS.
    iSplitL "CELL".
    { iSplitR "CELL"; first done.
      iSplitR "CELL"; first done.
      rewrite /pointsto. iExact "CELL". }
    cStep.
    rewrite /ist_with_eq /Ist.
    iSplitR "MAP COUNT"; first done.
    iExists (MemState.mk
      (<[l := new]> m.(MemState.cells)) (S m.(MemState.count))).
    iSplitR "MAP COUNT"; first done.
    iCombine "MAP COUNT" as "RES". iExact "RES".
  Qed.

  Lemma simF_get_cnt :
    ISim.sim_fun open MemAMod MemIMod Ist (fid MemHdr.get_cnt).
  Proof.
    cStartFunSim.
    rewrite /MemI.get_cnt.
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
    cForceS (m.(MemState.count)↑). cStepsS. cForcesS.
    iSplitR "MAP COUNT".
    { iSplitR; first done.
      iExists m.(MemState.count).
      iSplitR; first (iPureIntro; split; done).
      rewrite /count_snapshot. iExact "SNAP'". }
    cStep.
    rewrite /ist_with_eq /Ist.
    iSplitR "MAP COUNT"; first done.
    iExists m. iSplitR "MAP COUNT"; first done.
    iCombine "MAP COUNT" as "RES". iExact "RES".
  Qed.

  Lemma sim :
    ISim.t open MemAMod MemIMod MemA.auth_init Ist.
  Proof.
    cStartModSim.
    - iIntros "INIT".
      iDestruct "INIT" as "[MAP COUNT]".
      rewrite /Ist.
      iExists MemState.empty.
      iSplitR "MAP COUNT"; first done.
      iCombine "MAP COUNT" as "RES". iExact "RES".
    - apply simF_alloc.
    - apply simF_load.
    - apply simF_store.
    - apply simF_get_cnt.
  Qed.
End MemIA.

Section contextual_refinement.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Lemma ctxr (sp : specmap) :
    MemA.auth_init ⊢ ctx_refines MemI.t (MemA.t sp).
  Proof.
    eapply main_adequacy, sim.
  Qed.
End contextual_refinement. End MemIA.
