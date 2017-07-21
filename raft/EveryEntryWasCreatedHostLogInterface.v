Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementCommonDefinitions.

Section EveryEntryWasCreatedHostLogInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition every_entry_was_created_host_log (net : network) : Prop :=
    forall e h,
      In e (log (snd (nwState net h))) ->
      term_was_created net (eTerm e).

  Class every_entry_was_created_host_log_interface : Prop :=
    {
      every_entry_was_created_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          every_entry_was_created_host_log net
    }.
End EveryEntryWasCreatedHostLogInterface.
