Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.

Section AppendEntriesRequestTermSanity.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Definition append_entries_request_term_sanity net :=
    forall p t n pli plt es ci e,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      In e es ->
      eTerm e >= plt.


  Class append_entries_request_term_sanity_interface : Prop :=
    {
      append_entries_request_term_sanity_invariant :
        forall net,
          refined_raft_intermediate_reachable net ->
          append_entries_request_term_sanity net
    }.

End AppendEntriesRequestTermSanity.
