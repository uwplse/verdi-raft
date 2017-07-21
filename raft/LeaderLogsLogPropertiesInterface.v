Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.

Section LeaderLogsLogProperties.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.
  
  Definition log_property (P : list entry -> Prop) :=
    forall net h,
      refined_raft_intermediate_reachable net ->
      P (log (snd (nwState net h))).
    
  Definition log_properties_hold_on_leader_logs net :=
    forall P h t ll,
      log_property P ->
      In (t, ll) (leaderLogs (fst (nwState net h))) ->
      P ll.


  Class log_properties_hold_on_leader_logs_interface : Prop :=
    {
      log_properties_hold_on_leader_logs_invariant :
        forall (net : network),
          refined_raft_intermediate_reachable net ->
          log_properties_hold_on_leader_logs net
    }.
        
End LeaderLogsLogProperties.
