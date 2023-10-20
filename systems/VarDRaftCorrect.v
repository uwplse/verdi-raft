From Verdi Require Import Verdi VarD.
From VerdiRaft Require Import Raft CommonDefinitions.
From VerdiRaft Require Import Linearizability RaftLinearizableProofs.
From VerdiRaft Require Import EndToEndLinearizability VarDRaft.

Section VarDRaftCorrect.
  Variable n : nat.

  Instance raft_params : RaftParams VarD.vard_base_params :=
    raft_params n.

  Instance base_params : BaseParams :=
    vard_raft_base_params n.

  Instance multi_params : MultiParams _ :=
    vard_raft_multi_params n.

  Instance failure_params : FailureParams _ :=
    vard_raft_failure_params n.

  Theorem vard_raft_linearizable :
    forall failed net tr,
      input_correct tr ->
      step_failure_star step_failure_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
   Proof using.
     exact raft_linearizable.
   Qed.
End VarDRaftCorrect.
