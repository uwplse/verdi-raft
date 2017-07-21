Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RaftMsgRefinementInterface.

Require Import VerdiRaft.CommonTheorems.

Require Import VerdiRaft.SpecLemmas.


Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.GhostLogCorrectInterface.
Require Import VerdiRaft.GhostLogsLogPropertiesInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.AllEntriesLeaderSublogInterface.
Require Import VerdiRaft.GhostLogAllEntriesInterface.

Require Import VerdiRaft.GhostLogLogMatchingInterface.


Section GhostLogLogMatching.

  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rmri : raft_msg_refinement_interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.
  Context {glci : ghost_log_correct_interface}.
  Context {lphogli : log_properties_hold_on_ghost_logs_interface}.
  Context {tsi : term_sanity_interface}.
  Context {aelsi : allEntries_leader_sublog_interface}.
  Context {glaei : ghost_log_allEntries_interface}.
  
  Definition ghost_log_entries_match_nw (net : network) : Prop :=
    forall p p',
      In p (nwPackets net) ->
      In p' (nwPackets net) ->
      entries_match (fst (pBody p)) (fst (pBody p')).

  Definition ghost_log_entries_match (net : network) : Prop :=
    ghost_log_entries_match_host net /\
    ghost_log_entries_match_nw net.

  Definition lifted_entries_contiguous net :=
    forall h,
      contiguous_range_exact_lo (log (snd (nwState net h))) 0.

  Definition lifted_entries_sorted net :=
    forall h,
      sorted (log (snd (nwState net h))).
  
  Lemma lifted_entries_contiguous_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_entries_contiguous net.
  Proof using rlmli rmri. 
    intros.
    enough (entries_contiguous (mgv_deghost net)) by
        (unfold entries_contiguous, lifted_entries_contiguous, mgv_deghost in *;
         simpl in *;
         repeat break_match; simpl in *; auto).
    apply msg_lift_prop; eauto using entries_contiguous_invariant.
  Qed.

  Lemma lifted_entries_sorted_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_entries_sorted net.
  Proof using rlmli rmri. 
    intros.
    enough (entries_sorted (mgv_deghost net)) by
        (unfold entries_sorted, lifted_entries_sorted, mgv_deghost in *;
         simpl in *;
         repeat break_match; simpl in *; auto).
    apply msg_lift_prop; eauto using entries_sorted_invariant.
  Qed.

  Definition lifted_entries_contiguous_nw net :=
    forall p t n pli plt es ci,
      In p (nwPackets net) ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      contiguous_range_exact_lo es pli.

  Lemma lifted_entries_contiguous_nw_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_entries_contiguous_nw net.
  Proof using rlmli rmri. 
    intros.
    assert (entries_contiguous_nw (mgv_deghost net)) by
        (apply msg_lift_prop; eauto using entries_contiguous_nw_invariant).
    unfold entries_contiguous_nw, lifted_entries_contiguous_nw, mgv_deghost in *;
      intros.
    simpl in *;
      repeat break_match; simpl in *; auto.
    match goal with
      | H : context [contiguous_range_exact_lo] |- _ =>
        specialize (H (@mgv_deghost_packet _ _ ghost_log_params p));
          eapply H; simpl in *; eauto
    end.
    apply in_map_iff. eexists; eauto.
  Qed.

  Definition lifted_entries_match net :=
    forall h h',
      entries_match (log (snd (nwState net h))) (log (snd (nwState net h'))).

  Lemma lifted_entries_match_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_entries_match net.
  Proof using rlmli rmri. 
    intros.
    unfold lifted_entries_match; intros.
    find_eapply_lem_hyp msg_lift_prop;
      [|intros; eapply (entries_match_invariant ltac:(eauto) h h'); eauto].
    simpl in *.
    repeat break_match; simpl in *; auto.
  Qed.
  
  Definition lifted_no_entries_past_current_term_host net :=
    forall (h : name) e,
      In e (log (snd (nwState net h))) ->
      eTerm e <= currentTerm (snd (nwState net h)).

  Lemma lifted_no_entries_past_current_term_host_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_no_entries_past_current_term_host net.
  Proof using tsi rmri. 
    intros.
    enough (no_entries_past_current_term_host (deghost (mgv_deghost net))) by
        (unfold no_entries_past_current_term_host, lifted_no_entries_past_current_term_host, deghost, mgv_deghost in *;
         simpl in *;
         repeat break_match; simpl in *; auto).
    apply msg_lift_prop_all_the_way; eauto.
    intros.
    eapply no_entries_past_current_term_invariant; eauto.
  Qed.
  
  Lemma ghost_log_sorted :
    forall net p,
      msg_refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      sorted (fst (pBody p)).
  Proof using lphogli rlmli rmri. 
    assert (msg_log_property sorted) by
        (unfold msg_log_property; intros; eapply lifted_entries_sorted_invariant; eauto).
    intros.
    find_eapply_lem_hyp log_properties_hold_on_ghost_logs_invariant; eauto.
  Qed.

  Lemma ghost_log_contiguous :
    forall net p,
      msg_refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      contiguous_range_exact_lo (fst (pBody p)) 0.
  Proof using lphogli rlmli rmri. 
    assert (msg_log_property (fun x => contiguous_range_exact_lo x 0)) by
        (unfold msg_log_property; intros; eapply lifted_entries_contiguous_invariant; eauto).
    intros.
    find_eapply_lem_hyp log_properties_hold_on_ghost_logs_invariant;
      eauto; simpl in *; auto.
  Qed.

  Definition lifted_allEntries_leader_sublog (net : network) :=
    forall leader e h,
      type (snd (nwState net leader)) = Leader ->
      In e (map snd (allEntries (fst (nwState net h)))) ->
      eTerm e = currentTerm (snd (nwState net leader)) ->
      In e (log (snd (nwState net leader))).

  Lemma lifted_allEntries_leader_sublog_invariant :
    forall (net : @network _ raft_msg_refined_multi_params),
      msg_refined_raft_intermediate_reachable net ->
      lifted_allEntries_leader_sublog net.
  Proof using aelsi rmri. 
    intros.
    unfold lifted_allEntries_leader_sublog; intros.
    find_eapply_lem_hyp msg_lift_prop;
      [|intros; eapply allEntries_leader_sublog_invariant; eauto].
    simpl in *.
    unfold allEntries_leader_sublog in *.
    unfold mgv_deghost in *.
    simpl in *.
    repeat break_match; simpl in *; eauto.
  Qed.
  
  Lemma ghost_log_entries_match_init :
    msg_refined_raft_net_invariant_init ghost_log_entries_match.
  Proof using. 
    red. split;
      red; intros; simpl in *; intuition.
  Qed.

  Lemma handleAppendEntries_ghost_log:
    forall (p : packet) (net : network) (d : raft_data) 
      (m : msg) (t : term) (n : name) (pli : logIndex) 
      (plt : term) (es : list entry) (ci : logIndex) 
      (h : Net.name),
      msg_refined_raft_intermediate_reachable net ->
      entries_match (log (snd (nwState net h))) (fst (pBody p)) ->
      handleAppendEntries h (snd (nwState net h)) t n pli plt es ci = (d, m) ->
      snd (pBody p) = AppendEntries t n pli plt es ci ->
      In p (nwPackets net) -> log d = log (snd (nwState net h)) \/ log d = fst (pBody p).
  Proof using lphogli glci rlmli rmri. 
    intros.
    find_copy_eapply_lem_hyp ghost_log_correct_invariant; eauto;
    repeat conclude_using eauto.
    find_apply_lem_hyp handleAppendEntries_log.
    intuition; subst; auto.
    - repeat find_rewrite.
      rewrite sorted_findGtIndex_0; auto;
      [|eapply ghost_log_sorted; eauto].
      intros.
      eapply ghost_log_contiguous; eauto.
    - right.
      repeat find_rewrite.
      break_exists. intuition.
      subst.
      replace (eIndex x0) with (eIndex x).
      eapply thing; eauto; repeat find_rewrite; auto using findGtIndex_Prefix;
      try solve [eapply ghost_log_sorted; eauto];
      try solve [eapply ghost_log_contiguous; eauto];
      try solve [eapply lifted_entries_sorted_invariant; eauto];
      try solve [eapply lifted_entries_contiguous_nw_invariant; eauto].
  Qed.

  Hint Resolve entries_match_refl.
  Hint Resolve entries_match_sym.
    
  Lemma ghost_log_entries_match_append_entries :
    msg_refined_raft_net_invariant_append_entries' ghost_log_entries_match.
  Proof using lphogli glci rlmli rmri. 
    red.
    split; red; intros; simpl in *; intuition;
    unfold ghost_log_entries_match in *; break_and.
    - repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto.
      + match goal with
        | [ H : msg_refined_raft_intermediate_reachable (mkNetwork _ _) |- _ ] => clear H
        end.
        find_apply_hyp_hyp. intuition.
        * find_eapply_lem_hyp handleAppendEntries_ghost_log; eauto.
          intuition; repeat find_rewrite; eauto.
        * subst. simpl in *.
          find_eapply_lem_hyp handleAppendEntries_ghost_log; eauto.
      + find_apply_hyp_hyp. intuition; eauto.
        subst. simpl in *. unfold write_ghost_log.
        simpl.
        replace d with (snd (nwState {| nwPackets := ps'; nwState := st' |} (pDst p))) by
            (simpl; find_higher_order_rewrite; rewrite_update; reflexivity).
        replace (nwState net h) with (nwState {| nwPackets := ps'; nwState := st' |} h)by
            (simpl; find_higher_order_rewrite; rewrite_update; reflexivity).
        apply lifted_entries_match_invariant; auto.
    - find_apply_hyp_hyp.
      find_apply_hyp_hyp.
      intuition.
      + eauto.
      + subst. simpl in *.
        unfold write_ghost_log.
        simpl.
        match goal with
        | [ H : context [handleAppendEntries] |- _ ] =>
          eapply handleAppendEntries_ghost_log in H; eauto
        end.
        intuition.
        * find_rewrite. eauto.
        * find_rewrite. eauto.
      + subst. simpl in *.
        unfold write_ghost_log.
        simpl.
        match goal with
        | [ H : context [handleAppendEntries] |- _ ] =>
          eapply handleAppendEntries_ghost_log in H; eauto
        end.
        intuition.
        * find_rewrite. eauto.
        * find_rewrite. eauto.
      + subst. simpl in *. apply entries_match_refl.
  Qed.

  Ltac packet_simpl :=
    first [do_in_map; subst; simpl in *;
           unfold add_ghost_msg in *;
           do_in_map; subst; simpl in *|subst; simpl in *].

  Arguments write_ghost_log / _ _ _ _ _.
  
  Lemma ghost_log_entries_match_append_entries_reply :
    msg_refined_raft_net_invariant_append_entries_reply ghost_log_entries_match.
  Proof using rlmli rmri. 
    red.
    split; red; intros; simpl in *; intuition;
    unfold ghost_log_entries_match in *; break_and.
    - repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto.
      + find_apply_hyp_hyp. intuition.
        * erewrite handleAppendEntriesReply_log; eauto.
        * packet_simpl. apply entries_match_refl.
      + find_apply_hyp_hyp. intuition.
        * eauto.
        * packet_simpl.
          erewrite handleAppendEntriesReply_log with (st'0 := d) by eauto.
          eapply lifted_entries_match_invariant; eauto.
    - find_apply_hyp_hyp.
      find_apply_hyp_hyp.
      intuition.
      + eauto.
      + subst. simpl in *.
        do_in_map. subst. simpl in *.
        unfold add_ghost_msg in *. do_in_map. subst. simpl in *.
        erewrite handleAppendEntriesReply_same_log by eauto.
        eauto.
      + subst. simpl in *.
        do_in_map. subst. simpl in *.
        unfold add_ghost_msg in *. do_in_map. subst. simpl in *.
        erewrite handleAppendEntriesReply_same_log by eauto.
        eauto.
      + subst. simpl in *.
        repeat do_in_map. subst. simpl in *.
        unfold add_ghost_msg in *. repeat do_in_map. subst. simpl in *.
        auto.
  Qed.

  Lemma ghost_log_entries_match_request_vote :
    msg_refined_raft_net_invariant_request_vote' ghost_log_entries_match.
  Proof using rlmli rmri. 
    red.
    split; red; intros; simpl in *; intuition;
    unfold ghost_log_entries_match in *; break_and.
    - repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto.
      + find_apply_hyp_hyp. intuition.
        * erewrite handleRequestVote_log; eauto.
        * packet_simpl. auto.
      + find_apply_hyp_hyp. intuition.
        * eauto.
        * packet_simpl.
          erewrite handleRequestVote_log with (st'0 := d) by eauto.
          eapply lifted_entries_match_invariant; eauto.
    - find_apply_hyp_hyp.
      find_apply_hyp_hyp.
      intuition.
      + eauto.
      + subst. simpl in *. erewrite handleRequestVote_log; eauto.
      + subst. simpl in *. erewrite handleRequestVote_log; eauto.
      + subst. simpl in *. erewrite handleRequestVote_log; eauto.
  Qed.

  Lemma ghost_log_entries_match_request_vote_reply :
    msg_refined_raft_net_invariant_request_vote_reply ghost_log_entries_match.
  Proof using. 
    red.
    split; red; intros; simpl in *; intuition;
    unfold ghost_log_entries_match in *; break_and.
    - repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto.
      erewrite handleRequestVoteReply_log; eauto.
    - repeat find_apply_hyp_hyp; intuition; eauto;
      repeat packet_simpl; eauto.
  Qed.

  Lemma sorted_entries_match_cons :
    forall l l' e,
      sorted (e :: l) ->
      entries_match l l' ->
      (~ exists e', eIndex e' = eIndex e /\ eTerm e' = eTerm e /\ In e'  l') ->
      entries_match (e :: l) l'.
  Proof using. 
    intros. simpl in *.
    intuition.
    unfold entries_match in *.
    split; simpl in *; intuition; subst_max; auto;
    try solve [find_false; eauto].
    - find_apply_hyp_hyp. omega.
    - eapply H0; eauto.
    - right. eapply H0; eauto.
  Qed.

  Lemma ghost_log_entries_match_client_request :
    msg_refined_raft_net_invariant_client_request ghost_log_entries_match.
  Proof using glaei aelsi tsi rlmli rmri. 
    red.
    split; red; intros; simpl in *; intuition;
    unfold ghost_log_entries_match in *; break_and.
    - find_copy_apply_lem_hyp handleClientRequest_packets.
      subst. simpl in *.
      find_apply_hyp_hyp. intuition.
      repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto.
      find_apply_lem_hyp handleClientRequest_log.
      intuition; subst; simpl in *; repeat find_rewrite; eauto.
      break_exists_name e.
      intuition; repeat find_rewrite; simpl in *. subst.
      eapply sorted_entries_match_cons; eauto.
      + simpl. intuition; try solve [eapply lifted_entries_sorted_invariant; eauto].
        * find_eapply_lem_hyp maxIndex_is_max; eauto; try omega.
          eapply lifted_entries_sorted_invariant; eauto.
        * repeat find_rewrite.
          find_eapply_lem_hyp lifted_no_entries_past_current_term_host_invariant; eauto.
      + intuition.
        break_exists. intuition.
        repeat find_rewrite.
        enough (exists x, In x (log (snd (nwState net h0))) /\ eIndex x = eIndex e /\ eTerm x = eTerm e).
        * break_exists. intuition. repeat find_rewrite.
          find_eapply_lem_hyp maxIndex_is_max; eauto;
          unfold raft_data in *; simpl in *;
          unfold raft_data in *; simpl in *;
          [omega|]. eapply lifted_entries_sorted_invariant; eauto.
        * find_eapply_lem_hyp ghost_log_allEntries_invariant; eauto.
          break_exists.
          repeat find_rewrite.
          find_copy_eapply_lem_hyp lifted_allEntries_leader_sublog_invariant; eauto.
          apply in_map_iff. eexists; intuition; eauto; auto.
    - find_apply_hyp_hyp.
      find_apply_hyp_hyp.
      find_copy_apply_lem_hyp handleClientRequest_packets.
      subst. simpl in *. intuition.
  Qed.

  Lemma ghost_log_entries_match_timeout :
    msg_refined_raft_net_invariant_timeout ghost_log_entries_match.
  Proof using rlmli rmri. 
    red.
    split; red; intros; simpl in *; intuition;
    unfold ghost_log_entries_match in *; break_and.
    - repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto.
      + find_apply_hyp_hyp. intuition.
        * erewrite handleTimeout_log_same; eauto.
        * packet_simpl. eauto.
      + find_apply_hyp_hyp. intuition.
        packet_simpl.
        erewrite handleTimeout_log_same with (d' := d) by eauto.
        eapply lifted_entries_match_invariant; eauto.
    - find_apply_hyp_hyp.
      find_apply_hyp_hyp.
      intuition.
      + do_in_map. subst. unfold add_ghost_msg in *. do_in_map.
        subst. simpl in *.
        erewrite handleTimeout_log_same; eauto.
      + do_in_map. subst. unfold add_ghost_msg in *. do_in_map.
        subst. simpl in *.
        erewrite handleTimeout_log_same; eauto.
      + repeat do_in_map. subst. unfold add_ghost_msg in *. repeat do_in_map.
        subst. simpl in *. auto.
  Qed.

  Lemma ghost_log_entries_match_do_leader :
    msg_refined_raft_net_invariant_do_leader ghost_log_entries_match.
  Proof using rlmli rmri. 
    red. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.    
    split; red; intros; simpl in *; intuition;
    unfold ghost_log_entries_match in *; break_and.
    - repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto.
      + find_apply_hyp_hyp. intuition.
        * erewrite doLeader_log; eauto.
        * packet_simpl. eauto.
      + find_apply_hyp_hyp. intuition.
        packet_simpl.
        erewrite doLeader_log with (st'0 := d') by eauto.
        eapply lifted_entries_match_invariant; eauto.
    - find_apply_hyp_hyp.
      find_apply_hyp_hyp.
      intuition.
      + do_in_map. subst. unfold add_ghost_msg in *. do_in_map.
        subst. simpl in *.
        erewrite doLeader_log; eauto.
      + do_in_map. subst. unfold add_ghost_msg in *. do_in_map.
        subst. simpl in *.
        erewrite doLeader_log; eauto.
      + repeat do_in_map. subst. unfold add_ghost_msg in *. repeat do_in_map.
        subst. simpl in *. auto.
  Qed.

  Lemma ghost_log_entries_match_do_generic_server :
    msg_refined_raft_net_invariant_do_generic_server ghost_log_entries_match.
  Proof using rlmli rmri. 
    red. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.    
    split; red; intros; simpl in *; intuition;
    unfold ghost_log_entries_match in *; break_and.
    - repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto.
      + find_apply_hyp_hyp. intuition.
        * erewrite doGenericServer_log; eauto.
        * packet_simpl. eauto.
      + find_apply_hyp_hyp. intuition.
        packet_simpl.
        erewrite doGenericServer_log with (st'0 := d') by eauto.
        eapply lifted_entries_match_invariant; eauto.
    - find_apply_hyp_hyp.
      find_apply_hyp_hyp.
      intuition.
      + do_in_map. subst. unfold add_ghost_msg in *. do_in_map.
        subst. simpl in *.
        erewrite doGenericServer_log; eauto.
      + do_in_map. subst. unfold add_ghost_msg in *. do_in_map.
        subst. simpl in *.
        erewrite doGenericServer_log; eauto.
      + repeat do_in_map. subst. unfold add_ghost_msg in *. repeat do_in_map.
        subst. simpl in *. auto.
  Qed.

  Lemma ghost_log_entries_match_reboot :
    msg_refined_raft_net_invariant_reboot ghost_log_entries_match.
  Proof using. 
    red. intros.
    match goal with
      | H : nwState ?net ?h = (?gd, ?d) |- _ =>
        replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity);
          replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity);
          clear H
    end.    
    split; red; intros; simpl in *; intuition;
    unfold ghost_log_entries_match in *; break_and.
    - repeat find_higher_order_rewrite; destruct_update; simpl in *; eauto;
      repeat find_reverse_rewrite; eauto.
    - repeat find_reverse_rewrite; eauto.
  Qed.

  Lemma ghost_log_entries_match_state_same_packet_subset :
    msg_refined_raft_net_invariant_state_same_packet_subset ghost_log_entries_match.
  Proof using. 
    red. intros.
    split; red; intros; simpl in *; intuition;
    unfold ghost_log_entries_match in *; break_and.
    - find_apply_hyp_hyp. repeat find_reverse_higher_order_rewrite. eauto.
    - repeat find_apply_hyp_hyp. eauto.
  Qed.

  Lemma ghost_log_entries_match_invariant :
    forall net,
      msg_refined_raft_intermediate_reachable net ->
      ghost_log_entries_match net.
  Proof using glaei aelsi tsi lphogli glci rlmli rmri. 
    intros.
    apply msg_refined_raft_net_invariant'; auto.
    - apply ghost_log_entries_match_init.
    - apply msg_refined_raft_net_invariant_client_request'_weak.
      apply ghost_log_entries_match_client_request.
    - apply msg_refined_raft_net_invariant_timeout'_weak.
      apply ghost_log_entries_match_timeout.
    - apply ghost_log_entries_match_append_entries.
    - apply msg_refined_raft_net_invariant_append_entries_reply'_weak.
      apply ghost_log_entries_match_append_entries_reply.
    - apply ghost_log_entries_match_request_vote.
    - apply msg_refined_raft_net_invariant_request_vote_reply'_weak.
      apply ghost_log_entries_match_request_vote_reply.
    - apply msg_refined_raft_net_invariant_do_leader'_weak.
      apply ghost_log_entries_match_do_leader.
    - apply msg_refined_raft_net_invariant_do_generic_server'_weak.
      apply ghost_log_entries_match_do_generic_server.
    - apply msg_refined_raft_net_invariant_subset'_weak.
      apply ghost_log_entries_match_state_same_packet_subset.
    - apply msg_refined_raft_net_invariant_reboot'_weak. apply ghost_log_entries_match_reboot.
  Qed.

  Instance glemi : ghost_log_entries_match_interface.
  Proof.
    split.
    apply ghost_log_entries_match_invariant.
  Qed.
End GhostLogLogMatching.
