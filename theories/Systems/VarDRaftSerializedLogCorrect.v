From Verdi Require Import Verdi VarD LogCorrect.
From Cheerios Require Import Cheerios.
From VerdiRaft Require Import Raft CommonDefinitions.
From VerdiRaft Require Import Linearizability RaftLinearizableProofs.
From VerdiRaft Require Import VarDRaftSerializedCorrect.
From VerdiRaft Require Import VarDRaftSerializedLog.

Section SerializedLogCorrect.
  Variables n snapshot_interval : nat.

  Instance raft_params : RaftParams VarD.vard_base_params :=
    raft_params n.

  Instance transformed_base_params : BaseParams :=
    transformed_base_params n.
  Instance transformed_multi_params : DiskOpMultiParams _ :=
    transformed_multi_params n snapshot_interval.
  Instance transformed_failure_params : DiskOpFailureParams _ :=
    transformed_failure_params n snapshot_interval.

  Theorem vard_raft_log_linearizable :
    forall failed net tr,
      input_correct tr ->
      step_failure_disk_ops_star step_failure_disk_ops_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
  Proof using.
    intros failed net tr H_inp H_step.
    apply log_step_failure_star_simulation in H_step.
    find_apply_lem_hyp vard_raft_serialized_linearizable; auto.
  Qed.
End SerializedLogCorrect.
