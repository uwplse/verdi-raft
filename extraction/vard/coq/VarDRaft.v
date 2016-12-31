Require Import Raft.
Require Import Verdi.VarD.

Section VarDRaft.
  Instance raft_params : RaftParams vard_base_params :=
    {
      N := 7;
      input_eq_dec := input_eq_dec;
      output_eq_dec := output_eq_dec
    }.

  Definition vard_raft_base_params := base_params.
  Definition vard_raft_multi_params := multi_params.
  Definition vard_raft_failure_params := failure_params.
End VarDRaft.
