From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemHeader MemI MemA.
From CRIS.helping Require Import HelpingHeader.
From CRIS.prophecy Require Import ProphecyHeader.

Module MemNB. Section MemNB.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Definition scopes : list string := ["Mem"].
  Definition v_mem : key := "Mem" ↯ "mem".

  Definition alloc : list val → itree crisE val :=
    λ arg,
      'sz : Z <- (pargs [Tint] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      if (bool_decide (0 <= (8 * sz) < modulus_64))%Z
      then
        delta <- trigger (Choose _);;
        let mem0 : Mem.t := Mem.mem_pad mem delta in
        let (blk, mem1) := Mem.alloc mem0 sz in
        trigger (SPut v_mem mem1↑);;;
        Ret (Vptr (blk, 0%Z))
      else triggerNB.

  Definition free : list val → itree crisE val :=
    λ arg,
      bofs <- (pargs [Tptr] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.free mem bofs)!;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0).

  Definition load: list val → itree crisE val :=
    λ arg,
      bofs <- (pargs [Tptr] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      v <- (Mem.load mem bofs)!;;
      Ret v.

  Definition store : list val → itree crisE val :=
    λ arg,
      '(bofs, v): _ <- (pargs [Tptr; Tuntyped] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.store mem bofs v)!;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0).

  Definition cmp : list val → itree crisE val :=
    λ arg,
      '(v0, v1): _ <- (pargs [Tuntyped; Tuntyped] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      'b: bool <- (Mem.vcmp mem v0 v1)!;;
      Ret (Vint (if b then 1 else 0)).

  Definition cas: list val → itree crisE val :=
    λ arg,
      '(bofs, (v_old, v_new)) : _ <- (pargs [Tptr; Tuntyped; Tuntyped] arg)?;;
      'v_cur : val <- ccallU MemHdr.load [Vptr bofs];;
      'succ : val <- ccallU MemHdr.cmp [v_cur; v_old];;
      (if (bool_decide (succ = (Vint 1)))
       then ccallU MemHdr.store [Vptr bofs; v_new]
       else Ret Vundef);;;
      Ret v_cur.

  Definition mask : emask :=
    msk_scp scopes (CFilter.msk_filter_in MemHdr.exports msk_true).

  Definition fnsems : fnsemmap :=
    {[fid MemHdr.alloc # (mask, (fsp_some MemA.alloc, (cfunU imp_fun_t alloc)));
      fid MemHdr.free  # (mask, (fsp_some MemA.free, (cfunU imp_fun_t free)));
      fid MemHdr.load  # (mask, (fsp_some MemA.load, (cfunU imp_fun_t load)));
      fid MemHdr.store # (mask, (fsp_some MemA.store, (cfunU imp_fun_t store)));
      fid MemHdr.cmp   # (mask, (fsp_some MemA.cmp, (cfunU imp_fun_t cmp)));
      fid MemHdr.cas   # (mask, (fsp_some MemA.cas, (cfunU imp_fun_t cas)))]}.

  Definition sp : specmap :=
    {[fid MemHdr.alloc @ MemA.alloc;
      fid MemHdr.free  @ MemA.free;
      fid MemHdr.load  @ MemA.load;
      fid MemHdr.store @ MemA.store;
      fid MemHdr.cmp   @ MemA.cmp;
      fid MemHdr.cas   @ MemA.cas]}.

  Program Definition smod genv : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_mem # (Mem.load_mem genv)↑]};
  |}.
  Solve Obligations with mod_tac.

  Definition t sp genv : Mod.t := SMod.to_mod sp (smod genv).

  Lemma filter_prophecy mn sp genv:
    CFilter.filter (Prophecy.exports mn) (t sp genv) = t sp genv.
  Proof. cfilter_solver. Qed.

  Lemma filter_helping mn sp genv:
    CFilter.filter (Helping.exports mn) (t sp genv) = t sp genv.
  Proof. cfilter_solver. Qed.

  (* Lemma real genv: Mod.real_mod (t genv). *)
  (* Proof. real_mod_solver. Qed. *)
  
End MemNB. End MemNB.

