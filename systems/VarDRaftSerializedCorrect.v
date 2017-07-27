Require Import Verdi.Verdi.
Require Import Verdi.VarD.
Require Import Cheerios.Cheerios.
Require Import VerdiRaft.Raft.

Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.Linearizability.
Require Import VerdiRaft.RaftLinearizableProofs.

Require Import VerdiRaft.EndToEndLinearizability.
Require Import VerdiCheerios.SerializedMsgParamsCorrect.

Require Import VerdiRaft.VarDRaftSerialized.

Section SerializedCorrect.
  Variable n : nat.

  Instance raft_params : RaftParams VarD.vard_base_params :=
    raft_params n.

  Instance base_params : BaseParams :=
    transformed_base_params n.

  Instance multi_params : MultiParams _ :=
    transformed_multi_params n.

  Instance failure_params : FailureParams _ :=
    transformed_failure_params n.

  Theorem serialized_raft_linearizable :
    forall failed net tr,
      input_correct tr ->
      step_failure_star step_failure_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
  Proof using.
    intros.
    apply step_failure_deserialized_simulation_star in H0.
    break_exists.
    break_and.
    assert (H_eq: tr = x). admit. subst.
    apply raft_linearizable in H0; auto.
  Admitted.
End SerializedCorrect.
