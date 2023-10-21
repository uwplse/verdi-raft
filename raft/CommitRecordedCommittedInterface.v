From Verdi Require Import GhostSimulations.
From VerdiRaft Require Import Raft RaftRefinementInterface.
From VerdiRaft Require Import LeaderCompletenessInterface.
From VerdiRaft Require Import CommonDefinitions.

Section CommitRecordedCommitted.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition commit_recorded_committed net :=
    forall h e,
      commit_recorded (deghost net) h e ->
      committed net e (currentTerm (snd (nwState net h))).

  Class commit_recorded_committed_interface : Prop :=
    {
      commit_recorded_committed_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          commit_recorded_committed net
    }.
End CommitRecordedCommitted.
