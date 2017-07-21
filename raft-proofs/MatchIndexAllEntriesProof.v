Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.

Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import VerdiRaft.NoAppendEntriesToLeaderInterface.
Require Import VerdiRaft.NoAppendEntriesToSelfInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.LogAllEntriesInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.MatchIndexLeaderInterface.
Require Import VerdiRaft.MatchIndexSanityInterface.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.

Require Import VerdiRaft.MatchIndexAllEntriesInterface.

Section MatchIndexAllEntries.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {rri : raft_refinement_interface}.

  Context {naetli : no_append_entries_to_leader_interface}.
  Context {naetsi : no_append_entries_to_self_interface}.
  Context {taifoli : terms_and_indices_from_one_log_interface}.
  Context {rlmli : refined_log_matching_lemmas_interface}.
  Context {laei : log_all_entries_interface}.
  Context {aelli : append_entries_leaderLogs_interface}.
  Context {lsi : leader_sublog_interface}.
  Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
  Context {ollpti : one_leaderLog_per_term_interface}.
  Context {mili : match_index_leader_interface}.
  Context {matchisi : match_index_sanity_interface}.
  Context {aersi : append_entries_reply_sublog_interface}.
  Context {cei : candidate_entries_interface}.
  Context {vci : votes_correct_interface}.
  Context {cci : cronies_correct_interface}.

  Definition match_index_all_entries_nw (net : network) : Prop :=
    forall p t es e,
      In p (nwPackets net) ->
      pBody p = AppendEntriesReply t es true ->
      currentTerm (snd (nwState net (pDst p))) = t ->
      In e (log (snd (nwState net (pDst p)))) ->
      eTerm e = t ->
      eIndex e <= maxIndex es ->
      type (snd (nwState net (pDst p))) = Leader ->
      In (t, e) (allEntries (fst (nwState net (pSrc p)))).

  Definition match_index_all_entries_inv (net : network) : Prop :=
    match_index_all_entries net /\ match_index_all_entries_nw net.

  Lemma match_index_all_entries_init :
    refined_raft_net_invariant_init match_index_all_entries_inv.
  Proof using. 
    unfold refined_raft_net_invariant_init,
           match_index_all_entries_inv,
           match_index_all_entries_nw,
           match_index_all_entries.
    simpl. intros.
    intuition.
  Qed.

  Theorem handleClientRequest_matchIndex_log :
    forall h st client id c out st' ps,
      handleClientRequest h st client id c = (out, st', ps) ->
      ps = nil /\
      (log st' = log st /\ matchIndex st' = matchIndex st \/
       exists e,
         log st' = e :: log st /\
         eIndex e = S (maxIndex (log st)) /\
         eTerm e = currentTerm st /\
         eClient e = client /\
         eInput e = c /\
         eId e = id /\
         type st = Leader /\
         matchIndex st' = assoc_set name_eq_dec (matchIndex st) h (S (maxIndex (log st)))).
  Proof using. 
    intros. unfold handleClientRequest in *.
    break_match; find_inversion; subst; intuition.
    simpl in *. eauto 10.
  Qed.

  Lemma lifted_match_index_leader :
    forall net leader,
      refined_raft_intermediate_reachable net ->
      type (snd (nwState net leader)) = Leader ->
      assoc_default name_eq_dec (matchIndex (snd (nwState net leader))) leader 0 =
      maxIndex (log (snd (nwState net leader))).
  Proof using mili rri. 
    intros.
    pose proof lift_prop _ match_index_leader_invariant _ ltac:(eauto) leader.
    find_rewrite_lem deghost_spec. concludes. auto.
  Qed.

  Lemma lifted_match_index_sanity :
    forall net leader h,
      refined_raft_intermediate_reachable net ->
      type (snd (nwState net leader)) = Leader ->
      assoc_default name_eq_dec (matchIndex (snd (nwState net leader))) h 0 <=
      maxIndex (log (snd (nwState net leader))).
  Proof using matchisi rri. 
    intros.
    pose proof lift_prop _ match_index_sanity_invariant _ ltac:(eauto) leader h.
    find_rewrite_lem deghost_spec. concludes. auto.
  Qed.

  Lemma lifted_append_entries_reply_sublog :
    forall net p t es h e,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntriesReply t es true ->
      currentTerm (snd (nwState net h)) = t ->
      type (snd (nwState net h)) = Leader ->
      In e es ->
      In e (log (snd (nwState net h))).
  Proof using aersi rri. 
    intros.
    pose proof lift_prop _ append_entries_reply_sublog_invariant _ ltac:(eauto).
    unfold append_entries_reply_sublog in *.
    find_apply_lem_hyp ghost_packet.
    eapply_prop_hyp In In; eauto; try rewrite deghost_spec; eauto.
    find_rewrite_lem deghost_spec. auto.
  Qed.

  Lemma match_index_all_entries_client_request :
    refined_raft_net_invariant_client_request match_index_all_entries_inv.
  Proof using aersi matchisi mili rlmli rri. 
    unfold refined_raft_net_invariant_client_request, match_index_all_entries_inv.
    simpl. intros. break_and. split.
    - unfold match_index_all_entries in *. simpl in *. intros.
      repeat find_higher_order_rewrite. update_destruct_simplify_hyp.
      + find_copy_apply_lem_hyp handleClientRequest_type.
        find_copy_apply_lem_hyp handleClientRequest_matchIndex_log. intuition.
        * repeat find_rewrite.
          { update_destruct_simplify_hyp.
            - apply update_elections_data_clientRequest_allEntries_old'.
              find_apply_hyp_hyp. repeat find_rewrite. auto.
            - find_apply_hyp_hyp. repeat find_rewrite. auto.
          }
        * break_exists. break_and. repeat find_rewrite.
          { update_destruct_simplify_hyp.
            - unfold update_elections_data_client_request. find_rewrite.
              break_if.
              + repeat find_rewrite. simpl. break_or_hyp.
                * auto.
                * right.
                  find_copy_apply_lem_hyp maxIndex_is_max; [|solve[apply entries_sorted_invariant; auto]].
                  rewrite <- lifted_match_index_leader in * by auto.
                  eapply_prop_hyp In In; eauto. repeat find_rewrite. auto.
              + do_bool. find_rewrite. simpl length in *. omega.
            - find_erewrite_lem get_set_diff_default.
              pose proof lifted_match_index_sanity _ leader h0 ltac:(eauto) ltac:(auto).
              break_or_hyp.
              + simpl in *. omega.
              + find_apply_hyp_hyp. repeat find_rewrite. auto.
          }
      + find_apply_hyp_hyp. update_destruct_simplify_hyp.
        * apply update_elections_data_clientRequest_allEntries_old'.
          repeat find_rewrite. auto.
        * repeat find_rewrite. auto.
    - unfold match_index_all_entries_nw in *.
      simpl. intros.
      find_apply_hyp_hyp. break_or_hyp.
      + repeat find_higher_order_rewrite. update_destruct_simplify_hyp.
        * find_copy_apply_lem_hyp handleClientRequest_type. break_and. repeat find_rewrite.
          find_copy_apply_lem_hyp handleClientRequest_log.
          { intuition.
            - repeat find_rewrite.
              eapply_prop_hyp In In; eauto.
              update_destruct_simplify_hyp.
              + apply update_elections_data_clientRequest_allEntries_old'.
                repeat find_rewrite. auto.
              + repeat find_rewrite. auto.
            - break_exists. break_and. repeat find_rewrite.
              assert (es <> nil).
              {
                apply maxIndex_gt_0_nonempty.
                eapply lt_le_trans; [|eauto].
                simpl in *. break_or_hyp.
                - repeat find_rewrite. omega.
                - eapply entries_gt_0_invariant; eauto.
              }
              pose proof maxIndex_non_empty es. concludes.
              break_exists_name max_e. intuition.
              find_eapply_lem_hyp lifted_append_entries_reply_sublog; repeat find_rewrite; eauto.
              simpl In in *. break_or_hyp.
              + find_apply_lem_hyp maxIndex_is_max; [|solve[apply entries_sorted_invariant; auto]].
                omega.
              + eapply_prop_hyp In In; eauto; [|solve[repeat find_rewrite; auto]].
                update_destruct_simplify_hyp.
                * apply update_elections_data_clientRequest_allEntries_old'.
                  repeat find_rewrite. auto.
                * repeat find_rewrite. auto.
          }
        * eapply_prop_hyp In In; eauto.
          { update_destruct_simplify_hyp.
            - apply update_elections_data_clientRequest_allEntries_old'.
              repeat find_rewrite. auto.
            - repeat find_rewrite. auto.
          }
      + find_apply_lem_hyp handleClientRequest_packets. subst. simpl in *. intuition.
  Qed.

  Lemma handleTimeout_matchIndex :
    forall h st out st' l,
       handleTimeout h st = (out, st', l) ->
       matchIndex st' = matchIndex st.
  Proof using. 
    unfold handleTimeout, tryToBecomeLeader.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto.
  Qed.

  Lemma allEntries_update_timeout :
    forall x h h' net d,
      In x (allEntries (fst (nwState net h))) ->
      In x (allEntries (fst (update name_eq_dec (nwState net) h'
                                    (update_elections_data_timeout h' (nwState net h'), d) h))).
  Proof using. 
    intros.
    update_destruct_simplify_hyp.
    - unfold update_elections_data_timeout. repeat break_match; auto.
    - auto.
  Qed.

  Lemma handleTimeout_sends_RV :
    forall h st out st' l m,
      handleTimeout h st = (out, st', l) ->
      In m l ->
      exists node t h mi mt,
        m = (node, RequestVote t h mi mt).
  Proof using. 
    unfold handleTimeout, tryToBecomeLeader.
    intros.
    repeat break_match; repeat find_inversion.
    - do_in_map. subst. eauto 10.
    - do_in_map. subst. eauto 10.
    - simpl in *. intuition.
  Qed.

  Lemma match_index_all_entries_timeout :
    refined_raft_net_invariant_timeout match_index_all_entries_inv.
  Proof using. 
    unfold refined_raft_net_invariant_timeout, match_index_all_entries_inv.
    simpl. intros. break_and. split.
    - unfold match_index_all_entries in *. simpl. intros.
      repeat find_higher_order_rewrite.
      apply allEntries_update_timeout.
      update_destruct_simplify_hyp.
      + find_erewrite_lem handleTimeout_log_same.
        find_copy_apply_lem_hyp handleTimeout_type. intuition; try congruence.
        find_erewrite_lem handleTimeout_matchIndex.
        repeat find_rewrite.
        eapply_prop_hyp In In; eauto. congruence.
      + eapply_prop_hyp In In; eauto. congruence.
    - unfold match_index_all_entries_nw in *.
      simpl. intros.
      find_apply_hyp_hyp. break_or_hyp.
      + repeat find_higher_order_rewrite.
        apply allEntries_update_timeout.
        update_destruct_simplify_hyp.
        * find_erewrite_lem handleTimeout_log_same.
          find_copy_apply_lem_hyp handleTimeout_type.
          intuition; try congruence.
          eapply_prop_hyp In In; eauto; try congruence.
        * eapply_prop_hyp In In; eauto; congruence.
      + do_in_map. find_eapply_lem_hyp handleTimeout_sends_RV; eauto.
        break_exists. subst. simpl in *. discriminate.
  Qed.

  Lemma handleAppendEntries_post_leader_nop :
    forall h st t n pli plt es ci st' m,
      currentTerm st <> t ->
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      type st' = Leader ->
      st' = st.
  Proof using. 
    unfold handleAppendEntries.
    intros.
    repeat break_match; repeat find_inversion; auto; try discriminate.
  Qed.

  Lemma handleAppendEntries_leader_was_leader :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      type st' = Leader ->
      type st = Leader.
  Proof using. 
    unfold handleAppendEntries.
    intros.
    repeat break_match; repeat find_inversion; auto; try discriminate.
  Qed.

  Lemma lifted_no_AE_to_leader :
    forall net p t n pli plt es ci,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      type (snd (nwState net (pDst p))) = Leader ->
      currentTerm (snd (nwState net (pDst p))) = t ->
      False.
  Proof using naetli rri. 
    intros.
    pose proof (lift_prop _ no_append_entries_to_leader_invariant _ ltac:(eauto)).
    unfold no_append_entries_to_leader in *.
    find_apply_lem_hyp ghost_packet.
    match goal with
    | [ H : forall _ _ _ , _, H' : In _ _ |- _ ] => eapply H in H'; eauto
    end;
    rewrite deghost_spec;
    rewrite pDst_deghost_packet; auto.
  Qed.

  Lemma lifted_no_AE_to_self :
    forall net p t n pli plt es ci,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      pDst p = pSrc p ->
      False.
  Proof using naetsi rri. 
    intros.
    pose proof (lift_prop _ no_append_entries_to_self_invariant _ ltac:(eauto)).
    unfold no_append_entries_to_self in *.
    find_apply_lem_hyp ghost_packet.
    match goal with
    | [ H : forall _ _ _ , _, H' : In _ _ |- _ ] => eapply H in H'; eauto
    end.
  Qed.

  Lemma handleAppendEntries_message :
    forall h st t n pli plt es ci st' m,
      handleAppendEntries h st t n pli plt es ci = (st', m) ->
      exists res, m = AppendEntriesReply (currentTerm st') es res.
  Proof using. 
    unfold handleAppendEntries, advanceCurrentTerm.
    intros. repeat break_match; repeat find_inversion; simpl in *; repeat do_bool; eauto;
            eexists; f_equal; eauto using NPeano.Nat.le_antisymm.
  Qed.

  Lemma not_empty_true_elim :
    forall A (l : list A),
      not_empty l = true -> l <> nil.
  Proof using. 
    unfold not_empty.
    intros. break_match; congruence.
  Qed.

  Lemma not_empty_false_elim :
    forall A (l : list A),
      not_empty l = false -> l = nil.
  Proof using. 
    unfold not_empty.
    intros. break_match; congruence.
  Qed.

  Lemma handleAppendEntries_success_allEntries :
    forall h st t n pli plt es ci st' t',
      handleAppendEntries h st t n pli plt es ci = (st', AppendEntriesReply t' es true) ->
      es <> nil ->
      (forall e e' e'',
          In e es ->
          In e' (log st) ->
          eIndex e = eIndex e' ->
          eTerm e = eTerm e' ->
          In e'' es ->
          eIndex e'' <= eIndex e ->
          In e'' (log st)) ->
      sorted (log st) ->
      exists e, In e (log st') /\ In e es /\
                eIndex e = maxIndex es /\
                eTerm e = maxTerm es.
  Proof using. 
    unfold handleAppendEntries, haveNewEntries.
    intros.
    break_if; try find_inversion.
    break_if.
    - break_if; find_inversion; simpl;
      repeat (do_bool; repeat break_and).
      + find_apply_lem_hyp not_empty_true_elim.
        pose proof maxIndex_non_empty es ltac:(auto).
        break_exists_exists. intuition.
      + break_or_hyp.
        * find_apply_lem_hyp not_empty_false_elim. congruence.
        * break_match; try discriminate.
          do_bool. rewrite advanceCurrentTerm_log.
          find_apply_lem_hyp findAtIndex_elim. break_and.
          pose proof maxIndex_non_empty es ltac:(auto).
          break_exists_name e'. break_and.
          match goal with
          | [ H : forall _ _ _, In _ _ -> _ |- _ ] =>
            specialize (H e' e e')
          end.
          repeat find_rewrite. repeat concludes. intuition.
          assert (e = e').
          { eapply uniqueIndices_elim_eq; eauto.
            auto using sorted_uniqueIndices.
          }
          subst. eauto.
    - break_match; try find_inversion.
      break_if; try find_inversion.
      break_if; find_inversion; simpl;
      repeat (do_bool; repeat break_and).
      + find_apply_lem_hyp not_empty_true_elim.
        pose proof maxIndex_non_empty es ltac:(auto).
        break_exists_exists. intuition.
      + break_or_hyp.
        * find_apply_lem_hyp not_empty_false_elim. congruence.
        * break_match; try discriminate.
          do_bool. rewrite advanceCurrentTerm_log.
          find_apply_lem_hyp findAtIndex_elim. break_and.
          pose proof maxIndex_non_empty es ltac:(auto).
          break_exists_name e'. break_and.
          match goal with
          | [ H : forall _ _ _, In _ _ -> _ |- _ ] =>
            specialize (H e' e0 e')
          end.
          repeat find_rewrite. repeat concludes. intuition.
          assert (e0 = e').
          { eapply uniqueIndices_elim_eq; eauto.
            auto using sorted_uniqueIndices.
          }
          subst. eauto.
  Qed.

  Lemma handleAppendEntries_success_term :
    forall h st t n pli plt es ci st' t',
      handleAppendEntries h st t n pli plt es ci = (st', AppendEntriesReply t' es true) ->
      currentTerm st' = t.
  Proof using. 
    unfold handleAppendEntries, advanceCurrentTerm.
    intros. repeat break_match; repeat find_inversion; simpl; auto; repeat do_bool;
    eauto using Nat.le_antisymm.
  Qed.

  Lemma lifted_terms_and_indices_from_one_log : forall net h,
    refined_raft_intermediate_reachable net ->
    terms_and_indices_from_one (log (snd (nwState net h))).
  Proof using taifoli rri. 
    intros.
    pose proof (lift_prop _ terms_and_indices_from_one_log_invariant).
    unfold terms_and_indices_from_one_log in *.
    rewrite <- deghost_spec with (net0 := net). auto.
  Qed.

  Lemma lifted_leader_sublog_nw :
    forall net p t n pli plt es ci h e,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      type (snd (nwState net h)) = Leader ->
      eTerm e = currentTerm (snd (nwState net h)) ->
      In e es ->
      In e (log (snd (nwState net h))).
  Proof using lsi rri. 
    intros.
    pose proof (lift_prop _ leader_sublog_invariant_invariant _ ltac:(eauto)) as Hinv.
    unfold leader_sublog_invariant, leader_sublog_nw_invariant in *.
    destruct Hinv as [Hhost Hnw].
    find_apply_lem_hyp ghost_packet.
    eapply_prop_hyp In In; eauto; try find_rewrite_lem deghost_spec; try rewrite deghost_spec; eauto.
  Qed.

  Lemma appendEntries_sublog :
    forall net p t n pli plt es ci h e,
      refined_raft_intermediate_reachable net ->
      In p (nwPackets net) ->
      pBody p = AppendEntries t n pli plt es ci ->
      currentTerm (snd (nwState net h)) = t ->
      type (snd (nwState net h)) = Leader ->
      In e es ->
      In e (log (snd (nwState net h))).
  Proof using ollpti lhllsi lsi aelli rri. 
    intros.
    find_copy_eapply_lem_hyp append_entries_leaderLogs_invariant; eauto.
    break_exists. break_and.
    subst es.
    find_apply_lem_hyp in_app_or. destruct H4.
    - find_copy_apply_hyp_hyp.
      eapply lifted_leader_sublog_nw; eauto; [subst; auto|auto with datatypes].
    - find_eapply_lem_hyp leaders_have_leaderLogs_strong_invariant; auto.
      break_exists.  break_and.
      pose proof one_leaderLog_per_term_invariant _ ltac:(eauto) h x (currentTerm (snd (nwState net h))) x3 x0.
      concludes.
      subst_max.
      concludes.
      break_and. subst.
      find_rewrite. eauto using Prefix_In with *.
  Qed.

  Lemma match_index_all_entries_append_entries :
    refined_raft_net_invariant_append_entries' match_index_all_entries_inv.
  Proof using ollpti lhllsi lsi aelli laei rlmli taifoli naetsi naetli rri. 
    unfold refined_raft_net_invariant_append_entries', match_index_all_entries_inv.
    simpl. intros. break_and.
    split.
    - unfold match_index_all_entries in *. simpl. intros.
      repeat find_higher_order_rewrite.
      update_destruct_simplify_hyp.
      + assert (currentTerm (snd (nwState net (pDst p))) <> t).
        { intro.
          match goal with
          | [ H : pBody _ = AppendEntries _ _ _ _ _ _ |- _ ] =>
            eapply lifted_no_AE_to_leader with (net := net) in H; eauto
          end.
          eapply handleAppendEntries_leader_was_leader; eauto.
        }
        find_apply_lem_hyp handleAppendEntries_post_leader_nop; auto.
        subst. eapply_prop_hyp In In; eauto.
        repeat find_rewrite.
        update_destruct_simplify_hyp; auto using update_elections_data_appendEntries_preserves_allEntries.
      + eapply_prop_hyp In In; eauto. repeat find_rewrite.
        update_destruct_simplify_hyp; auto using update_elections_data_appendEntries_preserves_allEntries.
    - unfold match_index_all_entries_nw. simpl.  intros.
      find_apply_hyp_hyp. break_or_hyp.
      + unfold match_index_all_entries_nw in *.
        repeat find_higher_order_rewrite.
        update_destruct_simplify_hyp.
        * assert (currentTerm (snd (nwState net (pDst p))) <> t).
          { intro.
            match goal with
            | [ H : pBody _ = AppendEntries _ _ _ _ _ _ |- _ ] =>
              eapply lifted_no_AE_to_leader with (net := net) in H; eauto
            end.
            eapply handleAppendEntries_leader_was_leader; eauto.
          }
          match goal with
          | [ H : context [handleAppendEntries] |- _ ] =>
            apply handleAppendEntries_post_leader_nop in H; auto
          end.
          subst.
          match goal with
          | [ H : In _ (_ ++ _), H' : forall _ _ _ _, In _ _ -> _ |- _ ] =>
            eapply in_middle_insert in H; eapply H' in H; eauto; try congruence
          end.
          { update_destruct_simplify_hyp.
            - apply update_elections_data_appendEntries_preserves_allEntries.
              repeat find_rewrite. auto.
            - auto.
          }
        * match goal with
          | [ H : forall _ _ _ _, In _ _ -> _, H' : pBody _ = AppendEntriesReply _ _ _ |- _ ] =>
            eapply H in H'; eauto
          end.
          { update_destruct_simplify_hyp.
            - apply update_elections_data_appendEntries_preserves_allEntries.
              repeat find_rewrite. auto.
            - auto.
          }
      + simpl in *.
        find_copy_apply_lem_hyp handleAppendEntries_message. break_exists.
        subst. find_inversion.
        repeat find_higher_order_rewrite.
        update_destruct_simplify_hyp.
        * exfalso. eapply lifted_no_AE_to_self with (net := net); eauto.
        * unfold update_elections_data_appendEntries. repeat find_rewrite. simpl.
          { find_copy_apply_lem_hyp handleAppendEntries_success_allEntries.
            - break_exists. break_and.
              find_copy_apply_lem_hyp handleAppendEntries_success_term.
              assert (In x (log (snd (nwState net (pSrc p))))).
              { eapply appendEntries_sublog; eauto. subst. repeat find_rewrite. auto. }
              assert (entries_match (log d) (log (snd (nwState net (pSrc p))))).
              { match goal with
                | [ H : refined_raft_intermediate_reachable (mkNetwork ?a ?b) |- _ ] =>
                  let H' := fresh "H" in
                  pose proof entries_match_invariant _ (pDst p) (pSrc p) H as H';
                    simpl in H'; repeat find_higher_order_rewrite; rewrite_update;
                    simpl in H'; auto
                end.
              }
              assert (In e (log d)) as Helogd.
              { match goal with
                | [ H : entries_match _ _ |- _ ] =>
                  specialize (H x x e)
                end.
                assert (eIndex e <= eIndex x) by omega.
                repeat concludes. intuition.
              }

              match goal with
              | [ H : refined_raft_intermediate_reachable (mkNetwork ?a ?b) |- _ ] =>
                let H' := fresh "H" in
                pose proof log_all_entries_invariant _ H (pDst p) e as H';
                  simpl in H'; repeat find_higher_order_rewrite; rewrite_update;
                  simpl in H'; unfold update_elections_data_appendEntries in H';
                  repeat find_rewrite; simpl in H'
              end.
              auto.
            - find_apply_lem_hyp lifted_terms_and_indices_from_one_log; auto. break_and.
              apply maxIndex_gt_0_nonempty. omega.
            - intros.
              match goal with
              | [ H : refined_raft_intermediate_reachable (mkNetwork _ _) |- _ ] => clear H
              end.
              pose proof entries_match_nw_host_invariant _ ltac:(eauto) _ _ _ _ _ _ _ (pDst p)
                   e0 e' e'' ltac:(eauto) ltac:(eauto).
              repeat find_rewrite. auto.
            - apply entries_sorted_invariant. auto.
          }
  Qed.

  Lemma handleAppendEntriesReply_spec :
    forall n st src t es b st' l,
      handleAppendEntriesReply n st src t es b = (st', l) ->
      (type st' = type st /\
       matchIndex st' = matchIndex st /\
       currentTerm st' = currentTerm st) \/
      (currentTerm st' = t /\ type st' = Follower) \/
      (b = true /\
       t = currentTerm st' /\
       type st' = type st /\
       matchIndex st' = assoc_set name_eq_dec (matchIndex st) src
                                  (PeanoNat.Nat.max
                                     (assoc_default name_eq_dec (matchIndex st) src 0) (maxIndex es)) /\
       currentTerm st' = currentTerm st).
  Proof using. 
    unfold handleAppendEntriesReply.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; auto.
    - do_bool. intuition.
    - unfold advanceCurrentTerm. break_match; auto.
  Qed.

  Lemma update_nop_fst :
    forall A B f x (v2 : B) y,
      fst (update name_eq_dec f x (fst (f x), v2) y) = fst (A := A) (f y).
  Proof using. 
    intros.
    update_destruct_simplify_hyp; auto.
  Qed.

  Lemma match_index_all_entries_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply match_index_all_entries_inv.
  Proof using. 
    unfold refined_raft_net_invariant_append_entries_reply, match_index_all_entries_inv.
    simpl. intros. split.
    - { unfold match_index_all_entries in *. simpl. intros. break_and.
        repeat find_higher_order_rewrite.
        rewrite update_nop_fst.
        update_destruct_simplify_hyp.
        - find_copy_apply_lem_hyp handleAppendEntriesReply_spec.
          intuition.
          + match goal with
            | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) h)
            end.
            repeat find_rewrite. repeat concludes.
            find_erewrite_lem handleAppendEntriesReply_log.
            auto.
          + congruence.
          + repeat find_rewrite.
            match goal with
            | [ H : context [ assoc_default _ (assoc_set _ _ ?x _) ?y _ ]  |- _ ] =>
              destruct (name_eq_dec x y)
            end.
            * subst. rewrite get_set_same_default in *.
              find_apply_lem_hyp app_cons_in.
              find_erewrite_lem handleAppendEntriesReply_log.
              { find_apply_lem_hyp PeanoNat.Nat.max_le. break_or_hyp.
                - match goal with
                  | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) (pSrc p))
                  end. repeat find_rewrite. auto.
                - unfold match_index_all_entries_nw in *.
                  match goal with
                  | [ H : pBody _ = _, H' : _  |- _ ] => eapply H' with (e := e) in H; auto
                  end.
              }
            * rewrite get_set_diff_default in * by auto.
              match goal with
              | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) h)
              end.
              repeat find_rewrite. repeat concludes.
              find_erewrite_lem handleAppendEntriesReply_log.
              auto.
        - find_apply_hyp_hyp. congruence.
      }
    - break_and. unfold match_index_all_entries_nw in *. simpl. intros.
      repeat find_higher_order_rewrite. rewrite update_nop_fst.
      find_apply_hyp_hyp.
      break_or_hyp.
      + update_destruct_simplify_hyp.
        * find_erewrite_lem handleAppendEntriesReply_log.
          find_copy_apply_lem_hyp handleAppendEntriesReply_spec.
          { repeat break_or_hyp; break_and.
            - repeat find_rewrite. eauto using in_middle_insert.
            - congruence.
            - repeat find_rewrite. eauto using in_middle_insert.
          }
        * eauto using in_middle_insert.
      + do_in_map. find_apply_lem_hyp handleAppendEntriesReply_packets. subst.
        simpl in *. intuition.
  Qed.

  Lemma handleRequestVote_sends_RVR :
    forall st h h' t lli llt st' m,
      handleRequestVote h st t h' lli llt = (st', m) ->
      exists t b, m = RequestVoteReply t b.
  Proof using. 
    unfold handleRequestVote.
    intros.
    repeat break_match; repeat find_inversion; eauto.
  Qed.

  Lemma match_index_all_entries_request_vote :
    refined_raft_net_invariant_request_vote match_index_all_entries_inv.
  Proof using. 
    unfold refined_raft_net_invariant_request_vote, match_index_all_entries_inv.
    simpl. intros. split.
    - unfold match_index_all_entries in *. simpl. intros. break_and.
      repeat find_higher_order_rewrite.
      update_destruct_simplify_hyp.
      + find_copy_apply_lem_hyp handleRequestVote_type.
        intuition; try congruence.
        find_copy_apply_lem_hyp handleRequestVote_matchIndex_preserved.
        unfold matchIndex_preserved in *. intuition.
        update_destruct_simplify_hyp.
        * rewrite update_elections_data_requestVote_allEntries.
          repeat find_reverse_rewrite.
          match goal with
          | [ H : context [ In _ (allEntries _) ] |- _ ] =>
            apply H with (leader := pDst p)
          end; auto;
            repeat find_rewrite; auto.
        * repeat find_reverse_rewrite.
          match goal with
          | [ H : context [ In _ (allEntries _) ] |- _ ] =>
            apply H with (leader := pDst p)
          end; auto;
            repeat find_rewrite; auto.
      + update_destruct_simplify_hyp.
        * rewrite update_elections_data_requestVote_allEntries.
          repeat find_reverse_rewrite.
          match goal with
          | [ H : context [ In _ (allEntries _) ] |- _ ] =>
            eapply H; eauto
          end.
        * repeat find_reverse_rewrite.
          match goal with
          | [ H : context [ In _ (allEntries _) ] |- _ ] =>
            eapply H; eauto
          end.
    - break_and.
      unfold match_index_all_entries_nw in *.
      simpl. intros.
      find_apply_hyp_hyp. break_or_hyp.
      + repeat find_higher_order_rewrite.
        update_destruct_simplify_hyp.
        * { find_copy_apply_lem_hyp handleRequestVote_type.
            intuition; try congruence.
            find_copy_apply_lem_hyp handleRequestVote_matchIndex_preserved.
            unfold matchIndex_preserved in *. intuition.
            update_destruct_simplify_hyp.
            - rewrite update_elections_data_requestVote_allEntries.
              repeat find_rewrite.
              match goal with
              | [ H : context [ In _ (allEntries _) ] |- _ ] =>
                apply H with (es := es); auto using in_middle_insert; try congruence
              end.
            - match goal with
              | [ H : context [ In _ (allEntries _) ] |- _ ] =>
                apply H with (es := es); auto using in_middle_insert; try congruence
              end.
          }
        * { update_destruct_simplify_hyp.
            - rewrite update_elections_data_requestVote_allEntries.
              repeat find_rewrite.
              match goal with
              | [ H : context [ In _ (allEntries _) ] |- _ ] =>
                apply H with (es := es); auto using in_middle_insert; try congruence
              end.
            - match goal with
              | [ H : context [ In _ (allEntries _) ] |- _ ] =>
                apply H with (es := es); auto using in_middle_insert; try congruence
              end.
          }
      + simpl in *.
        find_apply_lem_hyp handleRequestVote_sends_RVR.
        break_exists.
        congruence.
  Qed.

  Lemma handleRequestVoteReply_spec :
    forall h st h' t r st',
      handleRequestVoteReply h st h' t r = st' ->
      type st' = Follower \/
      st' = st \/
      (log st' = log st /\
       currentTerm st' = currentTerm st /\
       matchIndex st' = assoc_set name_eq_dec nil h (maxIndex (log st))).
  Proof using. 
    unfold handleRequestVoteReply.
    intros.
    repeat break_match; repeat find_inversion; subst; simpl; intuition.
  Qed.

  Lemma handleRequestVoteReply_spec' :
    forall h st h' t r st',
      handleRequestVoteReply h st h' t r = st' ->
      type st' = Follower \/
      st' = st \/
      type st' = Candidate \/
      (type st' = Leader /\
       type st = Candidate /\
       log st' = log st /\
       r = true /\
       t = currentTerm st /\
       wonElection (dedup name_eq_dec (h' :: votesReceived st)) = true /\
       currentTerm st' = currentTerm st).
  Proof using. 
    unfold handleRequestVoteReply.
    intros.
    repeat break_match; repeat find_inversion; do_bool; subst; simpl; intuition.
  Qed.


  Lemma match_index_all_entries_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply match_index_all_entries_inv.
  Proof using cci vci cei laei taifoli rri. 
    unfold refined_raft_net_invariant_request_vote_reply, match_index_all_entries_inv.
    simpl. intros. split.
    - unfold match_index_all_entries in *. simpl. intros. break_and.
      find_apply_lem_hyp handleRequestVoteReply_spec.
      repeat find_higher_order_rewrite.
      update_destruct_simplify_hyp.
      + intuition; try congruence.
        * subst.
          { update_destruct_simplify_hyp.
            - rewrite update_elections_data_requestVoteReply_allEntries.
              repeat find_reverse_rewrite. eauto.
            - repeat find_reverse_rewrite. eauto.
          }
        * repeat find_rewrite.
          unfold assoc_default in *.
          { break_match.
            - simpl in *. break_if; try discriminate.
              match goal with
              | [ H : Some _ = Some _ |- _ ] => invc H
              end.
              rewrite_update.
              simpl.
              rewrite update_elections_data_requestVoteReply_allEntries.
              match goal with
              | [ |- In (?t, _) _ ] => replace t with (eTerm e) by congruence
              end.
              eapply log_all_entries_invariant; auto.
            - find_apply_lem_hyp lifted_terms_and_indices_from_one_log; auto.
              intuition. omega.
          }
      + update_destruct_simplify_hyp.
        * rewrite update_elections_data_requestVoteReply_allEntries.
          repeat find_reverse_rewrite. eauto.
        * repeat find_reverse_rewrite. eauto.
    - unfold match_index_all_entries_nw in *.
      simpl in *.
      intros.
      find_apply_lem_hyp handleRequestVoteReply_spec'.
      repeat find_higher_order_rewrite.
      find_apply_hyp_hyp.
      update_destruct_simplify_hyp.
      + intuition; try congruence.
        * subst.
          { update_destruct_simplify_hyp.
            - rewrite update_elections_data_requestVoteReply_allEntries.
              repeat find_rewrite.
              match goal with
              | [ H : context [ In _ (allEntries _) ] |- _ ] =>
                eapply H; eauto; congruence
              end.
            - repeat find_rewrite.
              match goal with
              | [ H : context [ In _ (allEntries _) ] |- _ ] =>
                eapply H; eauto; congruence
              end.
          }
        * subst.
          intro_refined_invariant candidate_entries_invariant.
          match goal with
          | [ H : candidateEntries_host_invariant _ |- _ ] =>
            pose proof H (pDst p) e
          end.
          unfold raft_data in *.
          conclude_using congruence.
          { find_eapply_lem_hyp wonElection_candidateEntries_rvr; eauto.
            - intuition.
            - eauto using votes_correct_invariant.
            - eauto using cronies_correct_invariant.
            - unfold raft_refined_base_params, raft_refined_multi_params in *. congruence.
            - unfold raft_refined_multi_params, raft_refined_base_params in *.
              simpl in *.
              unfold raft_data in *.
              congruence.
          }
      + { update_destruct_simplify_hyp.
            - rewrite update_elections_data_requestVoteReply_allEntries.
              repeat find_rewrite.
              match goal with
              | [ H : context [ In _ (allEntries _) ] |- _ ] =>
                eapply H; eauto; congruence
              end.
            - repeat find_rewrite.
              match goal with
              | [ H : context [ In _ (allEntries _) ] |- _ ] =>
                eapply H; eauto; congruence
              end.
          }
  Qed.

  Lemma doLeader_sends_AE :
    forall st h os st' ms m,
      doLeader st h = (os, st', ms) ->
      In m ms ->
      is_append_entries (snd m).
  Proof using. 
    unfold doLeader.
    intros.
    repeat break_match; repeat find_inversion; simpl in *; intuition.
    do_in_map.
    subst.
    unfold replicaMessage.
    repeat break_match; simpl; eauto 10.
  Qed.

  Lemma match_index_all_entries_do_leader :
    refined_raft_net_invariant_do_leader match_index_all_entries_inv.
  Proof using. 
    unfold refined_raft_net_invariant_do_leader, match_index_all_entries_inv.
    intros. break_and. split.
    - unfold match_index_all_entries in *.
      simpl in *. intros.
      repeat find_higher_order_rewrite.
      match goal with
      | [ H : nwState ?net ?h = (?x, ?y) |- _ ] =>
        replace x with (fst (nwState net h)) in * by (rewrite H; auto);
        replace y with (snd (nwState net h)) in * by (rewrite H; auto);
        clear H
      end.
      rewrite update_nop_fst.
      update_destruct_simplify_hyp.
      + repeat find_reverse_rewrite.
        find_copy_apply_lem_hyp doLeader_type. intuition.
        find_copy_apply_lem_hyp doLeader_matchIndex_preserved.
        unfold matchIndex_preserved in *. intuition.
        match goal with
        | [ H : context [ In _ (allEntries _) ] |- _ ] =>
          eapply H; eauto; try congruence
        end.
      + repeat find_reverse_rewrite.
        match goal with
        | [ H : context [ In _ (allEntries _) ] |- _ ] =>
          eapply H; eauto; try congruence
        end.
    - unfold match_index_all_entries_nw in *.
      simpl in *.
      intros.
      find_apply_hyp_hyp.
      break_or_hyp.
      + repeat find_higher_order_rewrite.
        match goal with
        | [ H : nwState ?net ?h = (?x, ?y) |- _ ] =>
          replace x with (fst (nwState net h)) in * by (rewrite H; auto);
            replace y with (snd (nwState net h)) in * by (rewrite H; auto);
            clear H
        end.
        rewrite update_nop_fst in *.
        find_copy_apply_lem_hyp doLeader_type. intuition.
        update_destruct_simplify_hyp.
        * find_copy_apply_lem_hyp doLeader_matchIndex_preserved.
          unfold matchIndex_preserved in *. intuition.
          match goal with
          | [ H : context [ In _ (allEntries _) ] |- _ ] =>
            eapply H; eauto; try congruence
          end.
        * match goal with
          | [ H : context [ In _ (allEntries _) ] |- _ ] =>
            eapply H; eauto; try congruence
          end.
      + do_in_map.
        find_eapply_lem_hyp doLeader_sends_AE; [|eauto].
        break_exists. subst.
        simpl in *. congruence.
  Qed.

  Lemma match_index_all_entries_do_generic_server :
    refined_raft_net_invariant_do_generic_server match_index_all_entries_inv.
  Proof using. 
    unfold refined_raft_net_invariant_do_generic_server, match_index_all_entries_inv.
    simpl. intros. break_and. split.
    - unfold match_index_all_entries in *.
      simpl in *. intros.
      repeat find_higher_order_rewrite.
      match goal with
      | [ H : nwState ?net ?h = (?x, ?y) |- _ ] =>
        replace x with (fst (nwState net h)) in * by (rewrite H; auto);
        replace y with (snd (nwState net h)) in * by (rewrite H; auto);
        clear H
      end.
      rewrite update_nop_fst.
      update_destruct_simplify_hyp.
      + repeat find_reverse_rewrite.
        find_copy_apply_lem_hyp doGenericServer_type. intuition.
        find_copy_apply_lem_hyp doGenericServer_matchIndex_preserved.
        unfold matchIndex_preserved in *. intuition.
        match goal with
        | [ H : context [ In _ (allEntries _) ] |- _ ] =>
          eapply H; eauto; try congruence
        end.
      + repeat find_reverse_rewrite.
        match goal with
        | [ H : context [ In _ (allEntries _) ] |- _ ] =>
          eapply H; eauto; try congruence
        end.
    - unfold match_index_all_entries_nw in *.
      simpl in *.
      intros.
      find_apply_hyp_hyp.
      break_or_hyp.
      + repeat find_higher_order_rewrite.
        match goal with
        | [ H : nwState ?net ?h = (?x, ?y) |- _ ] =>
          replace x with (fst (nwState net h)) in * by (rewrite H; auto);
            replace y with (snd (nwState net h)) in * by (rewrite H; auto);
            clear H
        end.
        rewrite update_nop_fst in *.
        find_copy_apply_lem_hyp doGenericServer_type. intuition.
        update_destruct_simplify_hyp.
        * find_copy_apply_lem_hyp doGenericServer_matchIndex_preserved.
          unfold matchIndex_preserved in *. intuition.
          match goal with
          | [ H : context [ In _ (allEntries _) ] |- _ ] =>
            eapply H; eauto; try congruence
          end.
        * match goal with
          | [ H : context [ In _ (allEntries _) ] |- _ ] =>
            eapply H; eauto; try congruence
          end.
      + do_in_map.
        find_apply_lem_hyp doGenericServer_packets.
        subst. simpl in *. intuition.
  Qed.

  Lemma match_index_all_entries_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset match_index_all_entries_inv.
  Proof using. 
    unfold refined_raft_net_invariant_state_same_packet_subset, match_index_all_entries_inv.
    simpl. intros. break_and. split.
    - unfold match_index_all_entries in *.
      intros.
      repeat find_reverse_higher_order_rewrite.
      eauto.
    - unfold match_index_all_entries_nw in *.
      intros.
      find_apply_hyp_hyp.
      repeat find_reverse_higher_order_rewrite.
      eauto.
  Qed.


  Lemma match_index_all_entries_reboot :
    refined_raft_net_invariant_reboot match_index_all_entries_inv.
  Proof using. 
    unfold refined_raft_net_invariant_reboot, match_index_all_entries_inv.
    intros. break_and. subst. split.
    - unfold match_index_all_entries in *.
      intros.
      repeat find_higher_order_rewrite.
      match goal with
      | [ H : nwState ?net ?h = (?x, ?y) |- _ ] =>
        replace x with (fst (nwState net h)) in * by (rewrite H; auto);
          replace y with (snd (nwState net h)) in * by (rewrite H; auto);
          clear H
      end.
      rewrite update_nop_fst.
      update_destruct_simplify_hyp.
      + discriminate.
      + repeat find_reverse_rewrite.
        eauto.
    - unfold match_index_all_entries_nw in *.
      intros.
      repeat find_higher_order_rewrite.
      match goal with
      | [ H : nwState ?net ?h = (?x, ?y) |- _ ] =>
        replace x with (fst (nwState net h)) in * by (rewrite H; auto);
          replace y with (snd (nwState net h)) in * by (rewrite H; auto);
          clear H
      end.
      rewrite update_nop_fst.
      update_destruct_simplify_hyp.
      + discriminate.
      + repeat find_reverse_rewrite.
        eauto.
  Qed.

  Lemma match_index_all_entries_invariant :
    forall net,
      refined_raft_intermediate_reachable net ->
      match_index_all_entries_inv net.
  Proof using cci vci cei aersi matchisi mili ollpti lhllsi lsi aelli laei rlmli taifoli naetsi naetli rri. 
    intros.
    apply refined_raft_net_invariant'; auto.
    - apply match_index_all_entries_init.
    - apply refined_raft_net_invariant_client_request'_weak.
      apply match_index_all_entries_client_request.
    - apply refined_raft_net_invariant_timeout'_weak.
      apply match_index_all_entries_timeout.
    - apply match_index_all_entries_append_entries.
    - apply refined_raft_net_invariant_append_entries_reply'_weak.
      apply match_index_all_entries_append_entries_reply.
    - apply refined_raft_net_invariant_request_vote'_weak.
      apply match_index_all_entries_request_vote.
    - apply refined_raft_net_invariant_request_vote_reply'_weak.
      apply match_index_all_entries_request_vote_reply.
    - apply refined_raft_net_invariant_do_leader'_weak.
      apply match_index_all_entries_do_leader.
    - apply refined_raft_net_invariant_do_generic_server'_weak.
      apply match_index_all_entries_do_generic_server.
    - apply match_index_all_entries_state_same_packet_subset.
    - apply refined_raft_net_invariant_reboot'_weak.
      apply match_index_all_entries_reboot.
  Qed.

  Instance miaei : match_index_all_entries_interface.
  Proof.
    constructor.
    apply match_index_all_entries_invariant.
  Qed.
End MatchIndexAllEntries.
