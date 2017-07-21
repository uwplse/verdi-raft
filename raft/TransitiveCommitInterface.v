Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.LeaderCompletenessInterface.

Section TransitiveCommit.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition transitive_commit net :=
    forall h e e' t,
      In e (log (snd (nwState net h))) ->
      In e' (log (snd (nwState net h))) ->
      eIndex e <= eIndex e' ->
      committed net e' t ->
      committed net e t.

  Class transitive_commit_interface : Prop :=
    {
      transitive_commit_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          transitive_commit net
    }.
  
End TransitiveCommit.
