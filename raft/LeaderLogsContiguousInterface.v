Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.

Require Import VerdiRaft.CommonTheorems.

Section LeaderLogsContiguous.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition leaderLogs_contiguous (net : network) : Prop :=
    forall h t ll,
      In (t, ll) (leaderLogs (fst (nwState net h))) ->
      contiguous_range_exact_lo ll 0.
  
  Class leaderLogs_contiguous_interface : Prop :=
    {
      leaderLogs_contiguous_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          leaderLogs_contiguous net
    }.
End LeaderLogsContiguous.
