Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.

Require Import VerdiRaft.CommonTheorems.

Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.EveryEntryWasCreatedInterface.
Require Import VerdiRaft.LeaderLogsCandidateEntriesInterface.

Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.VotesCorrectInterface.

Require Import VerdiRaft.RefinementCommonTheorems.

Require Import VerdiRaft.LeaderLogsSublogInterface.

Section LeaderLogsSublog.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.
  Context {lsi : leader_sublog_interface}.
  Context {lltsi : leaderLogs_term_sanity_interface}.
  Context {eewci : every_entry_was_created_interface}.
  Context {llcei : leaderLogs_candidate_entries_interface}.

  Context {cci : cronies_correct_interface}.
  Context {vci : votes_correct_interface}.

  Theorem leaderLogs_sublog_init :
    refined_raft_net_invariant_init leaderLogs_sublog.
  Proof using. 
    unfold refined_raft_net_invariant_init, leaderLogs_sublog.
    simpl. intuition.
  Qed.

  Ltac start :=
    repeat match goal with
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := fst) in H
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := snd) in H
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := leaderLogs) in H
           end;
  rewrite update_fun_comm with (f := snd);
  simpl in *;
  match goal with
    | [ H : context [ type ] |- _ ] =>
      rewrite update_fun_comm in H;
        rewrite update_nop_ext' in H by auto
  end;
  match goal with
    | [ H : context [ currentTerm ] |- _ ] =>
      rewrite update_fun_comm in H;
        rewrite update_nop_ext' in H by auto
  end.

  Theorem leaderLogs_sublog_client_request :
    refined_raft_net_invariant_client_request leaderLogs_sublog.
  Proof using. 
    unfold refined_raft_net_invariant_client_request, leaderLogs_sublog.
    intuition.
    simpl in *.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleClientRequest_type. intuition.
    start.
    find_rewrite_lem update_elections_data_client_request_leaderLogs.
    find_erewrite_lem update_nop_ext' .
    update_destruct_max_simplify.
    - destruct (log d) using (handleClientRequest_log_ind ltac:(eauto)).
      + eauto.
      + simpl. right. eauto.
    - eauto.
  Qed.

  Theorem leaderLogs_sublog_timeout :
    refined_raft_net_invariant_timeout leaderLogs_sublog.
  Proof using. 
    unfold refined_raft_net_invariant_timeout, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleTimeout_type.
    intuition.
    - start.
      find_rewrite_lem update_elections_data_timeout_leaderLogs.
      find_erewrite_lem update_nop_ext' .
      update_destruct_max_simplify; eauto.
      erewrite handleTimeout_log_same by eauto; eauto.
    - repeat update_destruct_max_simplify; try congruence.
      + find_rewrite_lem update_elections_data_timeout_leaderLogs.
        eauto.
      + eauto.
  Qed.

  Lemma handleAppendEntries_leader :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      type st' = Leader ->
      log st' = log st.
  Proof using. 
    unfold handleAppendEntries.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto; discriminate.
  Qed.

  Theorem leaderLogs_sublog_append_entries :
    refined_raft_net_invariant_append_entries leaderLogs_sublog.
  Proof using. 
    unfold refined_raft_net_invariant_append_entries, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleAppendEntries_type.
    intuition.
    - start.
      find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
      find_erewrite_lem update_nop_ext'.
      update_destruct_max_simplify; eauto.
      erewrite handleAppendEntries_leader by (eauto; congruence).
      eauto.
    - repeat update_destruct_max_simplify; try congruence.
      + find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
        eauto.
      + eauto.
  Qed.

  Theorem leaderLogs_sublog_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply leaderLogs_sublog.
  Proof using. 
    unfold refined_raft_net_invariant_append_entries_reply, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleAppendEntriesReply_type.
    intuition.
    - start.
      find_erewrite_lem update_nop_ext'.
      update_destruct_max_simplify; eauto.
      erewrite handleAppendEntriesReply_same_log by eauto.
      eauto.
    - repeat update_destruct_max_simplify; try congruence; eauto.
  Qed.

  Theorem leaderLogs_sublog_request_vote :
    refined_raft_net_invariant_request_vote leaderLogs_sublog.
  Proof using. 
    unfold refined_raft_net_invariant_request_vote, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleRequestVote_type.
    intuition.
    - start.
      find_rewrite_lem leaderLogs_update_elections_data_requestVote.
      find_erewrite_lem update_nop_ext'.
      update_destruct_max_simplify; eauto.
      erewrite handleRequestVote_same_log by eauto.
      eauto.
    - repeat update_destruct_max_simplify; try congruence.
      + find_rewrite_lem leaderLogs_update_elections_data_requestVote.
        eauto.
      + eauto.
  Qed.

  Lemma lifted_leader_sublog_host :
    forall net leader h e,
      refined_raft_intermediate_reachable net ->
      type (snd (nwState net leader)) = Leader ->
      In e (log (snd (nwState net h))) ->
      eTerm e = currentTerm (snd (nwState net leader)) ->
      In e (log (snd (nwState net leader))).
  Proof using lsi rri. 
    intros.
    pose proof (lift_prop _ leader_sublog_invariant_invariant).
    find_apply_hyp_hyp.
    match goal with H : forall _ , _ |- _ => clear H end.
    unfold leader_sublog_invariant, leader_sublog_host_invariant in *.
    break_and.
    do 3 find_insterU.
    repeat find_rewrite_lem deghost_spec.
    eauto.
  Qed.

  Lemma handleRequestVoteReply_RVR_spec :
    forall h st h' t r st',
      handleRequestVoteReply h st h' t r = st' ->
      st' = st \/
      (type st' = Follower /\
       currentTerm st' = t /\
       log st' = log st) \/
      (currentTerm st' = currentTerm st /\
       log st' = log st /\
       ((type st = Candidate /\ type st' = Leader /\ r = true /\ currentTerm st = t /\
         wonElection (dedup name_eq_dec (h' :: votesReceived st)) = true) \/ type st' = type st)).
  Proof using. 
    intros.
    unfold handleRequestVoteReply, advanceCurrentTerm in *.
    repeat break_match; try find_inversion; subst; simpl in *; intuition;
    do_bool; intuition; try right; congruence.
  Qed.

  Lemma contradict_leaderLogs_term_sanity :
    forall net h t ll e,
      refined_raft_intermediate_reachable net ->
      In (t, ll) (leaderLogs (fst (nwState net h))) ->
      In e ll ->
      eTerm e = currentTerm (snd (nwState net h)) ->
      False.
  Proof using lltsi. 
    intros.
    find_copy_eapply_lem_hyp leaderLogs_term_sanity_invariant; eauto.
    find_eapply_lem_hyp leaderLogs_currentTerm_invariant; eauto.
    omega.
  Qed.

  Arguments dedup : simpl never.

  Lemma leaderLogs_candidate_entries_rvr :
    forall net,
      leaderLogs_candidateEntries net ->
      votes_correct net ->
      cronies_correct net ->
      forall p h t ll e,
        In (t, ll) (leaderLogs (fst (nwState net h))) ->
        In e ll ->
        In p (nwPackets net) ->
        pBody p = RequestVoteReply (eTerm e) true ->
        currentTerm (snd (nwState net (pDst p))) = eTerm e ->
        wonElection (dedup name_eq_dec (pSrc p :: votesReceived (snd (nwState net (pDst p))))) = true ->
        type (snd (nwState net (pDst p))) <> Candidate.
  Proof using. 
    intros.
    eapply_prop_hyp leaderLogs_candidateEntries In; eauto.
    eapply wonElection_candidateEntries_rvr; auto. eauto. auto.  auto.
  Qed.

  Theorem leaderLogs_sublog_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply leaderLogs_sublog.
  Proof using vci cci llcei lltsi lsi rri. 
    unfold refined_raft_net_invariant_request_vote_reply, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp handleRequestVoteReply_RVR_spec.
    intuition.
    - subst. repeat find_rewrite.
      repeat update_destruct_max_simplify; eauto;
      find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition eauto;
      unfold raft_data in *; congruence.
    - repeat update_destruct_max_simplify; try congruence.
      + find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition eauto.
        subst_max. repeat find_rewrite. discriminate.
      + eauto.
    - repeat update_destruct_max_simplify.
      + repeat find_rewrite.
        find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
        * exfalso. eauto using contradict_leaderLogs_term_sanity.
        * subst. unfold raft_data in *. repeat find_rewrite. auto.
      + repeat find_rewrite.
        exfalso.
        eapply leaderLogs_candidate_entries_rvr; eauto;
          eauto using leaderLogs_candidate_entries_invariant,
                      votes_correct_invariant,
                      cronies_correct_invariant.
        congruence.
      + find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
        * eauto.
        * subst. unfold raft_data in *. repeat find_rewrite.
          eapply lifted_leader_sublog_host; eauto.
      + eauto.
    - repeat update_destruct_max_simplify.
      + find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
        * repeat find_rewrite. eauto.
        * subst. unfold raft_data in *. repeat find_rewrite. auto.
      + repeat find_rewrite. eauto.
      + find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
        * repeat find_rewrite. eauto.
        * subst. unfold raft_data in *. repeat find_rewrite. discriminate.
      + eauto.
  Qed.

  Theorem leaderLogs_sublog_do_leader :
    refined_raft_net_invariant_do_leader leaderLogs_sublog.
  Proof using. 
    unfold refined_raft_net_invariant_do_leader, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp doLeader_type.
    intuition.
    repeat match goal with
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := fst) in H
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := snd) in H
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := leaderLogs) in H
           end.
      rewrite update_fun_comm with (f := snd).
      simpl in *.
      rewrite update_fun_comm.
      rewrite update_nop_ext' by (find_apply_lem_hyp doLeader_same_log; repeat find_rewrite; auto).
      find_rewrite_lem update_fun_comm.
      match goal with
        | H : _ |- _ => rewrite update_nop_ext' in H by (repeat find_rewrite; auto)
      end.
      match goal with
          | H : context [ type ] |- _ =>
            rewrite update_fun_comm in H;
              rewrite update_nop_ext' in H by (repeat find_rewrite; auto)
      end.
      match goal with
        | H : _ |- _ => rewrite update_nop_ext' in H by (repeat find_rewrite; auto)
      end.
      eauto.
  Qed.


  Theorem leaderLogs_sublog_do_generic_server :
    refined_raft_net_invariant_do_generic_server leaderLogs_sublog.
  Proof using. 
    unfold refined_raft_net_invariant_do_generic_server, leaderLogs_sublog.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    find_copy_apply_lem_hyp doGenericServer_type.
    intuition.
    repeat match goal with
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := fst) in H
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := snd) in H
             | [ H : _ |- _ ] =>
               rewrite update_fun_comm with (f := leaderLogs) in H
           end.
      rewrite update_fun_comm with (f := snd).
      simpl in *.
      rewrite update_fun_comm.
      rewrite update_nop_ext' by (find_apply_lem_hyp doGenericServer_log; repeat find_rewrite; auto).
      find_rewrite_lem update_fun_comm.
      match goal with
        | H : _ |- _ => rewrite update_nop_ext' in H by (repeat find_rewrite; auto)
      end.
      match goal with
          | H : context [ type ] |- _ =>
            rewrite update_fun_comm in H;
              rewrite update_nop_ext' in H by (repeat find_rewrite; auto)
      end.

      match goal with
        | H : _ |- _ => rewrite update_nop_ext' in H by (repeat find_rewrite; auto)
      end.
      eauto.
  Qed.

  Theorem leaderLogs_sublog_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset leaderLogs_sublog.
  Proof using. 
    unfold refined_raft_net_invariant_state_same_packet_subset, leaderLogs_sublog.
    intuition.
    repeat find_reverse_higher_order_rewrite.
    eauto.
  Qed.

  Theorem leaderLogs_sublog_reboot :
    refined_raft_net_invariant_reboot leaderLogs_sublog.
  Proof using. 
    unfold refined_raft_net_invariant_reboot, leaderLogs_sublog.
    unfold reboot.
    simpl. intuition.
    repeat find_higher_order_rewrite.
    subst.
    repeat update_destruct_max_simplify; simpl in *; try discriminate;
    match goal with
      | [ H : _, H' : _ |- _ ] => solve [eapply H; eauto; rewrite H'; eauto]
    end.
  Qed.

  Theorem leaderLogs_sublog_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      leaderLogs_sublog net.
  Proof using vci cci llcei lltsi lsi rri. 
    intros.
    eapply refined_raft_net_invariant; eauto.
    - apply leaderLogs_sublog_init.
    - apply leaderLogs_sublog_client_request.
    - apply leaderLogs_sublog_timeout.
    - apply leaderLogs_sublog_append_entries.
    - apply leaderLogs_sublog_append_entries_reply.
    - apply leaderLogs_sublog_request_vote.
    - apply leaderLogs_sublog_request_vote_reply.
    - apply leaderLogs_sublog_do_leader.
    - apply leaderLogs_sublog_do_generic_server.
    - apply leaderLogs_sublog_state_same_packet_subset.
    - apply leaderLogs_sublog_reboot.
  Qed.

  Instance llsli : leaderLogs_sublog_interface.
  Proof.
    split.
    exact leaderLogs_sublog_invariant.
  Qed.
End LeaderLogsSublog.
