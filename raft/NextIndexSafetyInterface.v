Require Import VerdiRaft.Raft.

Section NextIndexSafety.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition nextIndex_safety (net : network) : Prop :=
    forall h h',
      type (nwState net h) = Leader ->
      pred (getNextIndex (nwState net h) h') <= maxIndex (log (nwState net h)).

  Class nextIndex_safety_interface : Prop :=
    {
      nextIndex_safety_invariant :
        forall net,
          raft_intermediate_reachable net ->
          nextIndex_safety net
    }.
End NextIndexSafety.
