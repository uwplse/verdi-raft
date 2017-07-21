Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.

Section VotesWithLogTermSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition votesWithLog_term_sanity net :=
    forall t l hs h,
      In (t, l, hs) (votesWithLog (fst (nwState net h))) ->
      t <= currentTerm (snd (nwState net h)).

  Class votesWithLog_term_sanity_interface : Prop :=
    {
      votesWithLog_term_sanity_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          votesWithLog_term_sanity net
    }.
End VotesWithLogTermSanity.
