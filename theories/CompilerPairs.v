From CRIS Require Import CRIS.

Set Implicit Arguments.

Local Open Scope Z_scope.

Module CompilerHdr.
  Definition mn := "WorkshopCompilerPairs".

  Definition fn (method : string) := mn +:+ "." +:+ method.

  Definition scratch := fnsig (fn "scratch") (fntyp () Z).
  Definition print_scratch := fnsig (fn "print_scratch") (fntyp () ()).
End CompilerHdr.

Module CompilerSource. Section CompilerSource.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scratch : () -> itree crisE Z :=
    fun _ => Ret (40 + 2).

  Definition print_scratch : () -> itree crisE () :=
    fun _ =>
      trigger (@IO _ unit "print" ([42] : list Z)↑);;;
      Ret tt.

  Definition fnsems : fnsemmap :=
    {[ fid CompilerHdr.scratch #
         (msk_scp [] msk_true,
          (fsp_none, cfunU CompilerHdr.scratch scratch));
       fid CompilerHdr.print_scratch #
         (msk_scp [] msk_true,
          (fsp_none, cfunU CompilerHdr.print_scratch print_scratch)) ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CompilerSource. End CompilerSource.

Module CompilerTarget. Section CompilerTarget.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := [CompilerHdr.mn].
  Definition tmp := CompilerHdr.mn ↯ "tmp".

  Definition scratch : () -> itree crisE Z :=
    fun _ =>
      cput tmp (40 : Z);;;
      x <- cgetU tmp;;
      Ret (x + 2).

  Definition print_scratch : () -> itree crisE () :=
    fun _ =>
      cput tmp (40 : Z);;;
      x <- cgetU tmp;;
      trigger (@IO _ unit "print" ([x + 2] : list Z)↑);;;
      Ret tt.

  Definition fnsems : fnsemmap :=
    {[ fid CompilerHdr.scratch #
         (msk_scp scopes msk_true,
          (fsp_none, cfunU CompilerHdr.scratch scratch));
       fid CompilerHdr.print_scratch #
         (msk_scp scopes msk_true,
          (fsp_none, cfunU CompilerHdr.print_scratch print_scratch)) ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[tmp # (0 : Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End CompilerTarget. End CompilerTarget.

Module CompilerProof. Section CompilerProof.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (** The scratch slot is compiler-private.  Its current value is irrelevant
      at function boundaries; only its presence and type matter. *)
  Definition Ist : ist_type Σ :=
    fun st_src st_tgt =>
      (⌜st_src = ∅⌝ ∧ ∃ n : Z, ⌜st_tgt = {[CompilerTarget.tmp # n↑]}⌝)%I.

  Local Definition Source := CompilerSource.t.
  Local Definition Target := CompilerTarget.t.

  (** Pair 1: [SPut]/[SGet] are internal local-state steps. *)
  Lemma simF_scratch :
    ISim.sim_fun open Source Target Ist (fid CompilerHdr.scratch).
  Proof using.
    cStartFunSim. unfold CompilerSource.scratch, CompilerTarget.scratch.
    iDestruct "IST" as "(-> & %old & ->)".
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    cStepsT. cStep. iSplit; eauto.
  Qed.

  (** Pair 2: after the internal lowering steps, both sides expose exactly the
      same [IO] request.  [cStep] matches that request and quantifies over the
      environment's response. *)
  Lemma simF_print_scratch :
    ISim.sim_fun open Source Target Ist (fid CompilerHdr.print_scratch).
  Proof using.
    cStartFunSim.
    unfold CompilerSource.print_scratch, CompilerTarget.print_scratch.
    iDestruct "IST" as "(-> & %old & ->)".
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    cStepsT. cStep. cStep. iSplit; eauto.
  Qed.

  Lemma sim : ISim.t open Source Target emp%I Ist.
  Proof using.
    cStartModSim.
    - iIntros "_". iSplit; first done. iExists 0. done.
    - apply simF_scratch.
    - apply simF_print_scratch.
  Qed.

  Lemma ctxr :
    ctx_refines (Target, emp%I) (Source, emp%I).
  Proof using. eapply main_adequacy, sim. Qed.
End CompilerProof. End CompilerProof.

(** Bad pair (deliberately no simulation theorem).

    These programs differ at an observable request: the source prints [42],
    while the target prints [43].  Internal stuttering cannot repair this
    mismatch, so the matching-[IO] simulation case is inapplicable.  The pair
    is kept as a discussion/countertrace exercise, not as an unfinished proof. *)
Module BadIOPair. Section BadIOPair.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition source : itree crisE unit :=
    trigger (@IO _ unit "print" ([42] : list Z)↑);;;
    Ret tt.

  Definition target : itree crisE unit :=
    trigger (@IO _ unit "print" ([43] : list Z)↑);;;
    Ret tt.
End BadIOPair. End BadIOPair.
