Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.

Section LeaderLogsSorted.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition leaderLogs_sorted (net : network) : Prop :=
    forall h t log, 
      In (t, log) (leaderLogs (fst (nwState net h))) -> 
      sorted log.

  Class leaderLogs_sorted_interface : Prop :=
    { 
      leaderLogs_sorted_invariant : 
        forall net, 
          refined_raft_intermediate_reachable net -> 
          leaderLogs_sorted net
    }.
End LeaderLogsSorted.
