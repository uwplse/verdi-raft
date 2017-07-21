Require Import Verdi.GhostSimulations.

Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.NoAppendEntriesToSelfInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.AppendEntriesRequestsCameFromLeadersInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsInterface.

Require Import VerdiRaft.NoAppendEntriesToLeaderInterface.

Section NoAppendEntriesToLeader.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {naetsi : no_append_entries_to_self_interface}.
  Context {ollpti : one_leaderLog_per_term_interface}.
  Context {aercfli : append_entries_came_from_leaders_interface}.
  Context {lhlli : leaders_have_leaderLogs_interface}.

  Definition no_append_entries_to_leader' (net : network) : Prop :=
    forall p t n pli plt es ci,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      type (snd (nwState net (pDst p))) = Leader ->
      currentTerm (snd (nwState net (pDst p))) = t ->
      False.


  Definition no_append_entries_to_self' (net : network) : Prop :=
    forall p t n pli plt es ci,
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      pDst p = pSrc p ->
      False.
  
  Theorem lift_no_append_entries_to_self :
    forall net,
      refined_raft_intermediate_reachable net ->
      no_append_entries_to_self (deghost net).
  Proof using naetsi rri. 
    intros.
    eapply lift_prop; eauto using no_append_entries_to_self_invariant.
  Qed.

  Lemma ghost_packet :
    forall (net : network (params := raft_refined_multi_params)) p,
      In p (nwPackets net) ->
      In (deghost_packet p) (nwPackets (deghost net)).
  Proof using. 
    unfold deghost.
    simpl. intuition.
    apply in_map_iff.
    eexists; eauto.
  Qed.

  Theorem no_append_entries_to_self'_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      no_append_entries_to_self' net.
  Proof using naetsi rri. 
    unfold no_append_entries_to_self'. intros.
    find_apply_lem_hyp ghost_packet.
    find_eapply_lem_hyp lift_no_append_entries_to_self; auto.
    simpl in *. eauto.
  Qed.
  
  Lemma no_append_entries_to_leader_invariant' :
    forall net,
      refined_raft_intermediate_reachable net ->
      no_append_entries_to_leader' net.
  Proof using lhlli aercfli ollpti naetsi rri. 
    unfold no_append_entries_to_leader'. intros. subst.
    find_copy_eapply_lem_hyp no_append_entries_to_self'_invariant; eauto.
    find_false.
    find_eapply_lem_hyp leaders_have_leaderLogs_invariant; eauto.
    break_exists.
    find_eapply_lem_hyp append_entries_came_from_leaders_invariant; eauto.
    break_exists.
    eapply one_leaderLog_per_term_host_invariant; eauto.
  Qed.
  
  Lemma deghost_packet_exists :
    forall net p,
      In p (nwPackets (deghost net)) ->
      exists (q : packet (params := raft_refined_multi_params (raft_params := raft_params))),
        In q (nwPackets net) /\ p = deghost_packet q.
  Proof using. 
    unfold deghost.
    simpl.
    intros.
    do_in_map.
    eauto.
  Qed.
  
  Instance noaetli : no_append_entries_to_leader_interface.
  split. intros.
  apply lower_prop; auto.
  intros.
  find_apply_lem_hyp no_append_entries_to_leader_invariant'.
  unfold no_append_entries_to_leader', no_append_entries_to_leader in *.
  intros.
  find_apply_lem_hyp deghost_packet_exists. break_exists. intuition. subst.
  simpl in *. repeat break_match; simpl in *. subst.
  match goal with
    | H : nwState ?h = (?gd, ?d) |- _ =>
      replace gd with (fst (nwState h)) in * by (rewrite H; reflexivity);
        replace d with (snd (nwState h)) in * by (rewrite H; reflexivity);
        clear H
  end. eauto.
  Qed.
End NoAppendEntriesToLeader.
