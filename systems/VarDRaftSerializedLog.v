From Verdi Require Import Verdi VarD SerializedMsgParams Log.
From Cheerios Require Import Cheerios Tree.
From VerdiRaft Require Import Raft VarDRaftSerializers VarDRaftSerialized.

Section SerializedLog.
  Variables n snapshot_interval : nat.

  Instance raft_params : RaftParams VarD.vard_base_params :=
    raft_params n.

  Definition orig_base_params : BaseParams :=
    transformed_base_params n.
  Definition orig_multi_params : MultiParams orig_base_params :=
    transformed_multi_params n.
  Definition orig_failure_params : FailureParams orig_multi_params :=
    transformed_failure_params n.

  Definition transformed_base_params : BaseParams :=
    @log_base_params orig_base_params.
  Definition transformed_multi_params : DiskOpMultiParams transformed_base_params :=
    @log_multi_params orig_base_params orig_multi_params _  _ _ _ snapshot_interval.
  Definition transformed_failure_params : DiskOpFailureParams transformed_multi_params :=
    @log_failure_params orig_base_params orig_multi_params orig_failure_params _ _ _ _ snapshot_interval.
End SerializedLog.
