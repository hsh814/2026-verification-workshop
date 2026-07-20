From CRIS Require Import CRIS.
From Workshop Require Import CompilerPairs.

Set Implicit Arguments.

Local Open Scope Z_scope.

Module AfterCompilerPairs. Section Checkpoint.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition CheckpointIst : ist_type Σ :=
    fun st_src st_tgt =>
      (⌜st_src = ∅⌝ ∧
       ∃ n : Z, ⌜st_tgt = {[CompilerTarget.tmp # n↑]}⌝)%I.

  Local Definition Source := CompilerSource.t.
  Local Definition Target := CompilerTarget.t.

  Lemma checkpoint_simF_scratch :
    ISim.sim_fun open Source Target CheckpointIst
      (fid CompilerHdr.scratch).
  Proof using.
    cStartFunSim. unfold CompilerSource.scratch, CompilerTarget.scratch.
    iDestruct "IST" as "(-> & %old & ->)".
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    cStepsT. cStep. iSplit; eauto.
  Qed.

  Lemma checkpoint_simF_print_scratch :
    ISim.sim_fun open Source Target CheckpointIst
      (fid CompilerHdr.print_scratch).
  Proof using.
    cStartFunSim.
    unfold CompilerSource.print_scratch, CompilerTarget.print_scratch.
    iDestruct "IST" as "(-> & %old & ->)".
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    cStepsT. cStep. cStep. iSplit; eauto.
  Qed.

  Lemma checkpoint_bad_io_payloads_differ :
    ([42] : list Z) <> [43].
  Proof. discriminate. Qed.
End Checkpoint. End AfterCompilerPairs.
