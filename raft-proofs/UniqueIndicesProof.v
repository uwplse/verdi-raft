Require Import VerdiRaft.Raft.

Require Import VerdiRaft.SortedInterface.

Require Import VerdiRaft.CommonTheorems.

Require Import VerdiRaft.UniqueIndicesInterface.

Section UniqueIndices.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {si : sorted_interface}.

  Theorem UniqueIndices_invariant :
    forall net,
      raft_intermediate_reachable net ->
      UniqueIndices net.
  Proof using si. 
    intros.
    find_apply_lem_hyp logs_sorted_invariant.
    unfold logs_sorted, UniqueIndices in *. intuition.
    - unfold uniqueIndices_host_invariant, logs_sorted_host in *.
      eauto using sorted_uniqueIndices.
    - unfold uniqueIndices_nw_invariant, logs_sorted_nw in *.
      eauto using sorted_uniqueIndices.
  Qed.

  Instance uii : unique_indices_interface.
  Proof.
    split.
    exact UniqueIndices_invariant.
  Qed.
End UniqueIndices.
