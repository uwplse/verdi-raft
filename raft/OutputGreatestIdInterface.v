Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.TraceUtil.

Section OutputGreatestId.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.


  Section inner.

  Variables client id : nat.


  Definition greatest_id_for_client (net : network) : Prop :=
    forall id',
      id < id' ->
      before_func (has_key client id) (has_key client id') (applied_entries (nwState net)).
  
  End inner.

  Class output_greatest_id_interface : Prop :=
    {
      output_greatest_id :
        forall client id failed net tr,
          step_failure_star step_failure_init (failed, net) tr ->
          key_in_output_trace client id tr ->
          greatest_id_for_client client id net
    }.
End OutputGreatestId.
