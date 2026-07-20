From CRIS Require Import CRIS.
From Workshop Require Import SimulationCases.

Set Implicit Arguments.

Module AfterFirstSimulation. Section Checkpoint.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition CheckpointIst : ist_type Σ :=
    fun st_src st_tgt => ⌜st_src = ∅ /\ st_tgt = ∅⌝%I.

  Local Definition Source := CasesSource.t.
  Local Definition Target := CasesTarget.t.

  (** Checkpoint: the first [Ret]/[Tau] simulation is complete. *)
  Lemma checkpoint_simF_ret_tau :
    ISim.sim_fun open Source Target CheckpointIst (fid CasesHdr.ret_tau).
  Proof using.
    cStartFunSim. unfold CasesSource.ret_tau, CasesTarget.ret_tau.
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    cStepsT. cStep. iSplit; eauto.
  Qed.

  (** Continue here: source-side [Choose] is existential. *)
  Lemma checkpoint_exercise_simF_choose_zero :
    ISim.sim_fun open Source Target CheckpointIst
      (fid CasesHdr.choose_zero).
  Proof using.
    cStartFunSim. unfold CasesSource.choose_zero, CasesTarget.choose_zero.
    cStepsS. cStepsT. destruct (Any.downcast arg) as [[]|];
      cStepsS; [cStepsT|]; ss.
    (* TODO: [cForceS true], then close the return and invariant. *)
  Abort.
End Checkpoint. End AfterFirstSimulation.
