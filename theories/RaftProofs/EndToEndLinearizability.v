From VerdiRaft Require Import Raft.
From VerdiRaft Require Import Linearizability.

From VerdiRaft Require Import RaftLinearizableProofs.

From VerdiRaft Require Import OutputCorrectInterface.
From VerdiRaft Require Import OutputCorrectProof.

From VerdiRaft Require Import InputBeforeOutputInterface.
From VerdiRaft Require Import InputBeforeOutputProof.

From VerdiRaft Require Import CausalOrderPreservedInterface.
From VerdiRaft Require Import CausalOrderPreservedProof.

From VerdiRaft Require Import AppliedImpliesInputInterface.
From VerdiRaft Require Import AppliedImpliesInputProof.

From VerdiRaft Require Import OutputImpliesAppliedInterface.
From VerdiRaft Require Import OutputImpliesAppliedProof.

From VerdiRaft Require Import LogMatchingInterface.
From VerdiRaft Require Import LogMatchingProof.

From VerdiRaft Require Import SortedInterface.
From VerdiRaft Require Import SortedProof.

From VerdiRaft Require Import TermSanityInterface.
From VerdiRaft Require Import TermSanityProof.

From VerdiRaft Require Import LeaderSublogInterface.
From VerdiRaft Require Import LeaderSublogProof.

From VerdiRaft Require Import RaftRefinementInterface.
From VerdiRaft Require Import RaftRefinementProof.

From VerdiRaft Require Import CandidateEntriesInterface.
From VerdiRaft Require Import CandidateEntriesProof.

From VerdiRaft Require Import CroniesTermInterface.
From VerdiRaft Require Import CroniesTermProof.

From VerdiRaft Require Import CroniesCorrectInterface.
From VerdiRaft Require Import CroniesCorrectProof.

From VerdiRaft Require Import VotesLeCurrentTermInterface.
From VerdiRaft Require Import VotesLeCurrentTermProof.

From VerdiRaft Require Import VotesCorrectInterface.
From VerdiRaft Require Import VotesCorrectProof.

From VerdiRaft Require Import CandidatesVoteForSelvesInterface.
From VerdiRaft Require Import CandidatesVoteForSelvesProof.

From VerdiRaft Require Import OneLeaderPerTermInterface.
From VerdiRaft Require Import OneLeaderPerTermProof.

From VerdiRaft Require Import UniqueIndicesInterface.
From VerdiRaft Require Import UniqueIndicesProof.

From VerdiRaft Require Import AppliedEntriesMonotonicInterface.
From VerdiRaft Require Import AppliedEntriesMonotonicProof.

From VerdiRaft Require Import StateMachineSafetyInterface.
From VerdiRaft Require Import StateMachineSafetyProof.

From VerdiRaft Require Import MaxIndexSanityInterface.

From VerdiRaft Require Import LeaderCompletenessInterface.
From VerdiRaft Require Import LeaderCompletenessProof.

From VerdiRaft Require Import TransitiveCommitInterface.
From VerdiRaft Require Import TransitiveCommitProof.

From VerdiRaft Require Import AllEntriesLeaderLogsInterface.
From VerdiRaft Require Import AllEntriesLeaderLogsProof.

From VerdiRaft Require Import CommitRecordedCommittedInterface.

From VerdiRaft Require Import LeaderLogsTermSanityInterface.
From VerdiRaft Require Import LeaderLogsTermSanityProof.

From VerdiRaft Require Import AllEntriesTermSanityInterface.
From VerdiRaft Require Import AllEntriesTermSanityProof.

From VerdiRaft Require Import VotesWithLogTermSanityInterface.
From VerdiRaft Require Import VotesWithLogTermSanityProof.

From VerdiRaft Require Import LeaderLogsPreservedInterface.
From VerdiRaft Require Import LeaderLogsPreservedProof.

From VerdiRaft Require Import PrefixWithinTermInterface.
From VerdiRaft Require Import PrefixWithinTermProof.

From VerdiRaft Require Import EveryEntryWasCreatedInterface.
From VerdiRaft Require Import EveryEntryWasCreatedProof.

From VerdiRaft Require Import EveryEntryWasCreatedHostLogInterface.
From VerdiRaft Require Import EveryEntryWasCreatedHostLogProof.

From VerdiRaft Require Import LeaderLogsVotesWithLogInterface.
From VerdiRaft Require Import LeaderLogsVotesWithLogProof.

From VerdiRaft Require Import AllEntriesLogInterface.
From VerdiRaft Require Import AllEntriesLogProof.

From VerdiRaft Require Import AllEntriesVotesWithLogInterface.
From VerdiRaft Require Import AllEntriesVotesWithLogProof.

From VerdiRaft Require Import VotesWithLogSortedInterface.
From VerdiRaft Require Import VotesWithLogSortedProof.

From VerdiRaft Require Import LeaderLogsLogMatchingInterface.
From VerdiRaft Require Import LeaderLogsLogMatchingProof.

From VerdiRaft Require Import StateMachineSafetyPrimeInterface.
From VerdiRaft Require Import StateMachineSafetyPrimeProof.

From VerdiRaft Require Import AppendEntriesRequestLeaderLogsInterface.
From VerdiRaft Require Import AppendEntriesRequestLeaderLogsProof.

From VerdiRaft Require Import AppendEntriesRequestsCameFromLeadersInterface.
From VerdiRaft Require Import AppendEntriesRequestsCameFromLeadersProof.

From VerdiRaft Require Import LeaderLogsSortedInterface.
From VerdiRaft Require Import LeaderLogsSortedProof.

From VerdiRaft Require Import LeaderLogsContiguousInterface.
From VerdiRaft Require Import LeaderLogsContiguousProof.

From VerdiRaft Require Import LogsLeaderLogsInterface.
From VerdiRaft Require Import LogsLeaderLogsProof.

From VerdiRaft Require Import OneLeaderLogPerTermInterface.
From VerdiRaft Require Import OneLeaderLogPerTermProof.

From VerdiRaft Require Import LeaderLogsSublogInterface.
From VerdiRaft Require Import LeaderLogsSublogProof.

From VerdiRaft Require Import LeadersHaveLeaderLogsInterface.
From VerdiRaft Require Import LeadersHaveLeaderLogsProof.

From VerdiRaft Require Import LeadersHaveLeaderLogsStrongInterface.
From VerdiRaft Require Import LeadersHaveLeaderLogsStrongProof.

From VerdiRaft Require Import NextIndexSafetyInterface.
From VerdiRaft Require Import NextIndexSafetyProof.

From VerdiRaft Require Import RefinedLogMatchingLemmasInterface.
From VerdiRaft Require Import RefinedLogMatchingLemmasProof.

From VerdiRaft Require Import LeaderLogsCandidateEntriesInterface.
From VerdiRaft Require Import LeaderLogsCandidateEntriesProof.

From VerdiRaft Require Import AllEntriesCandidateEntriesInterface.
From VerdiRaft Require Import AllEntriesCandidateEntriesProof.

From VerdiRaft Require Import AllEntriesLogMatchingInterface.
From VerdiRaft Require Import AllEntriesLogMatchingProof.

From VerdiRaft Require Import AppendEntriesRequestTermSanityInterface.
From VerdiRaft Require Import AppendEntriesRequestTermSanityProof.

From VerdiRaft Require Import AllEntriesLeaderSublogInterface.
From VerdiRaft Require Import AllEntriesLeaderSublogProof.

From VerdiRaft Require Import LastAppliedCommitIndexMatchingInterface.
From VerdiRaft Require Import LastAppliedCommitIndexMatchingProof.

From VerdiRaft Require Import LastAppliedLeCommitIndexInterface.
From VerdiRaft Require Import LastAppliedLeCommitIndexProof.

From VerdiRaft Require Import AllEntriesLeaderLogsTermInterface.
From VerdiRaft Require Import AllEntriesLeaderLogsTermProof.

From VerdiRaft Require Import StateMachineCorrectInterface.
From VerdiRaft Require Import StateMachineCorrectProof.

From VerdiRaft Require Import OutputGreatestIdInterface.
From VerdiRaft Require Import OutputGreatestIdProof.

From VerdiRaft Require Import CurrentTermGtZeroInterface.
From VerdiRaft Require Import CurrentTermGtZeroProof.

From VerdiRaft Require Import TermsAndIndicesFromOneLogInterface.
From VerdiRaft Require Import TermsAndIndicesFromOneLogProof.

From VerdiRaft Require Import TermsAndIndicesFromOneInterface.
From VerdiRaft Require Import TermsAndIndicesFromOneProof.

From VerdiRaft Require Import CandidateTermGtLogInterface.
From VerdiRaft Require Import CandidateTermGtLogProof.

From VerdiRaft Require Import VotesVotesWithLogCorrespondInterface.
From VerdiRaft Require Import VotesVotesWithLogCorrespondProof.

From VerdiRaft Require Import PrevLogLeaderSublogInterface.
From VerdiRaft Require Import PrevLogLeaderSublogProof.

From VerdiRaft Require Import AllEntriesIndicesGt0Interface.
From VerdiRaft Require Import AllEntriesIndicesGt0Proof.

From VerdiRaft Require Import PrevLogCandidateEntriesTermInterface.
From VerdiRaft Require Import PrevLogCandidateEntriesTermProof.

From VerdiRaft Require Import MatchIndexAllEntriesInterface.
From VerdiRaft Require Import MatchIndexAllEntriesProof.

From VerdiRaft Require Import MatchIndexLeaderInterface.
From VerdiRaft Require Import MatchIndexLeaderProof.

From VerdiRaft Require Import MatchIndexSanityInterface.
From VerdiRaft Require Import MatchIndexSanityProof.

From VerdiRaft Require Import NoAppendEntriesToLeaderInterface.
From VerdiRaft Require Import NoAppendEntriesToLeaderProof.

From VerdiRaft Require Import NoAppendEntriesToSelfInterface.
From VerdiRaft Require Import NoAppendEntriesToSelfProof.

From VerdiRaft Require Import NoAppendEntriesRepliesToSelfInterface.
From VerdiRaft Require Import NoAppendEntriesRepliesToSelfProof.

From VerdiRaft Require Import LogAllEntriesInterface.
From VerdiRaft Require Import LogAllEntriesProof.

From VerdiRaft Require Import AppendEntriesReplySublogInterface.
From VerdiRaft Require Import AppendEntriesReplySublogProof.

From VerdiRaft Require Import LeaderLogsLogPropertiesInterface.
From VerdiRaft Require Import LeaderLogsLogPropertiesProof.

From VerdiRaft Require Import AppendEntriesRequestReplyCorrespondenceInterface.
From VerdiRaft Require Import AppendEntriesRequestReplyCorrespondenceProof.

From VerdiRaft Require Import AppendEntriesLeaderInterface.
From VerdiRaft Require Import AppendEntriesLeaderProof.

From VerdiRaft Require Import RequestVoteMaxIndexMaxTermInterface.
From VerdiRaft Require Import RequestVoteMaxIndexMaxTermProof.

From VerdiRaft Require Import RequestVoteReplyMoreUpToDateInterface.
From VerdiRaft Require Import RequestVoteReplyMoreUpToDateProof.

From VerdiRaft Require Import RequestVoteReplyTermSanityInterface.
From VerdiRaft Require Import RequestVoteReplyTermSanityProof.

From VerdiRaft Require Import RequestVoteTermSanityInterface.
From VerdiRaft Require Import RequestVoteTermSanityProof.

From VerdiRaft Require Import VotedForMoreUpToDateInterface.
From VerdiRaft Require Import VotedForMoreUpToDateProof.

From VerdiRaft Require Import VotedForTermSanityInterface.
From VerdiRaft Require Import VotedForTermSanityProof.

From VerdiRaft Require Import VotesReceivedMoreUpToDateInterface.
From VerdiRaft Require Import VotesReceivedMoreUpToDateProof.

From VerdiRaft Require Import RaftMsgRefinementInterface.
From VerdiRaft Require Import RaftMsgRefinementProof.

From VerdiRaft Require Import GhostLogCorrectInterface.
From VerdiRaft Require Import GhostLogCorrectProof.

From VerdiRaft Require Import GhostLogsLogPropertiesInterface.
From VerdiRaft Require Import GhostLogsLogPropertiesProof.

From VerdiRaft Require Import InLogInAllEntriesInterface.
From VerdiRaft Require Import InLogInAllEntriesProof.

From VerdiRaft Require Import GhostLogAllEntriesInterface.
From VerdiRaft Require Import GhostLogAllEntriesProof.

From VerdiRaft Require Import GhostLogLogMatchingInterface.
From VerdiRaft Require Import GhostLogLogMatchingProof.

#[global]
Hint Extern 4 (@BaseParams) => apply base_params : typeclass_instances.
#[global]
Hint Extern 4 (@MultiParams _) => apply multi_params : typeclass_instances.
#[global]
Hint Extern 4 (@FailureParams _ _) => apply failure_params : typeclass_instances.
#[global]
Hint Extern 4 (@raft_refinement_interface _ _ _) => apply rri : typeclass_instances.
#[global]
Hint Extern 4 (@raft_msg_refinement_interface _ _ _) => apply rmri : typeclass_instances.
#[global]
Hint Extern 4 (@cronies_term_interface _ _ _) => apply cti : typeclass_instances.
#[global]
Hint Extern 4 (@votes_correct_interface _ _ _) => apply vci : typeclass_instances.
#[global]
Hint Extern 4 (@votes_le_current_term_interface _ _ _) => apply vlcti : typeclass_instances.
#[global]
Hint Extern 4 (@cronies_correct_interface _ _ _) => apply cci : typeclass_instances.
#[global]
Hint Extern 4 (@candidates_vote_for_selves_interface _ _ _) => apply cvfsi : typeclass_instances.
#[global]
Hint Extern 4 (@candidate_entries_interface _ _ _) => apply cei : typeclass_instances.
#[global]
Hint Extern 4 (@one_leader_per_term_interface _ _ _) => apply olpti : typeclass_instances.
#[global]
Hint Extern 4 (@leader_sublog_interface _ _ _) => apply lsi : typeclass_instances.
#[global]
Hint Extern 4 (@unique_indices_interface _ _ _) => apply uii : typeclass_instances.
#[global]
Hint Extern 4 (@sorted_interface _ _ _) => apply si : typeclass_instances.
#[global]
Hint Extern 4 (@term_sanity_interface _ _ _) => apply tsi : typeclass_instances.
#[global]
Hint Extern 4 (@log_matching_interface _ _ _) => apply lmi : typeclass_instances.
#[global]
Hint Extern 4 (@applied_entries_monotonic_interface _ _ _) => apply aemi : typeclass_instances.
#[global]
Hint Extern 4 (@state_machine_safety_interface _ _ _) => apply smsi : typeclass_instances.
#[global]
Hint Extern 4 (@output_implies_applied_interface _ _ _) => apply oiai : typeclass_instances.
#[global]
Hint Extern 4 (@applied_implies_input_interface _ _ _) => apply aiii : typeclass_instances.
#[global]
Hint Extern 4 (@causal_order_preserved_interface _ _ _) => apply copi : typeclass_instances.
#[global]
Hint Extern 4 (@input_before_output_interface _ _ _) => apply iboi : typeclass_instances.
#[global]
Hint Extern 4 (@output_correct_interface _ _ _) => apply oci : typeclass_instances.
#[global]
Hint Extern 4 (@max_index_sanity_interface _ _ _) => apply misi : typeclass_instances.
#[global]
Hint Extern 4 (@leader_completeness_interface _ _ _) => apply lci : typeclass_instances.
#[global]
Hint Extern 4 (@transitive_commit_interface _ _ _) => apply tci : typeclass_instances.
#[global]
Hint Extern 4 (@all_entries_leader_logs_interface _ _ _) => apply aelli : typeclass_instances.
#[global]
Hint Extern 4 (@commit_recorded_committed_interface _ _ _) => apply crci : typeclass_instances.
#[global]
Hint Extern 4 (@leaderLogs_term_sanity_interface _ _ _) => apply lltsi : typeclass_instances.
#[global]
Hint Extern 4 (@allEntries_term_sanity_interface _ _ _) => apply aetsi : typeclass_instances.
#[global]
Hint Extern 4 (@votesWithLog_term_sanity_interface _ _ _) => apply vwltsi : typeclass_instances.
#[global]
Hint Extern 4 (@leaderLogs_preserved_interface _ _ _) => apply llpi : typeclass_instances.
#[global]
Hint Extern 4 (@prefix_within_term_interface _ _ _) => apply pwti : typeclass_instances.
#[global]
Hint Extern 4 (@every_entry_was_created_interface _ _ _) => apply eewci : typeclass_instances.
#[global]
Hint Extern 4 (@every_entry_was_created_host_log_interface _ _ _) => apply eewchli : typeclass_instances.
#[global]
Hint Extern 4 (@leaderLogs_votesWithLog_interface _ _ _) => apply llvwli : typeclass_instances.
#[global]
Hint Extern 4 (@allEntries_log_interface _ _ _) => apply aeli : typeclass_instances.
#[global]
Hint Extern 4 (@allEntries_votesWithLog_interface _ _ _) => apply aevwli : typeclass_instances.
#[global]
Hint Extern 4 (@votesWithLog_sorted_interface _ _ _) => apply vwlsi : typeclass_instances.
#[global]
Hint Extern 4 (@leaderLogs_entries_match_interface _ _ _) => apply lllmi : typeclass_instances.
#[global]
Hint Extern 4 (@state_machine_safety'interface _ _ _) => apply sms'i : typeclass_instances.
#[global]
Hint Extern 4 (@append_entries_leaderLogs_interface _ _ _) => apply aerlli : typeclass_instances.
#[global]
Hint Extern 4 (@append_entries_came_from_leaders_interface _ _ _) => apply aercfli : typeclass_instances.
#[global]
Hint Extern 4 (@leaderLogs_sorted_interface _ _ _) => apply llsi : typeclass_instances.
#[global]
Hint Extern 4 (@leaderLogs_contiguous_interface _ _ _) => apply llci : typeclass_instances.
#[global]
Hint Extern 4 (@logs_leaderLogs_interface _ _ _) => apply llli : typeclass_instances.
#[global]
Hint Extern 4 (@one_leaderLog_per_term_interface _ _ _) => apply ollpti : typeclass_instances.
#[global]
Hint Extern 4 (@leaderLogs_sublog_interface _ _ _) => apply llsli : typeclass_instances.
#[global]
Hint Extern 4 (@leaders_have_leaderLogs_interface _ _ _) => apply lhlli : typeclass_instances.
#[global]
Hint Extern 4 (@leaders_have_leaderLogs_strong_interface _ _ _) => apply lhllsi : typeclass_instances.
#[global]
Hint Extern 4 (@nextIndex_safety_interface _ _ _) => apply nisi : typeclass_instances.
#[global]
Hint Extern 4 (@refined_log_matching_lemmas_interface _ _ _) => apply rlmli : typeclass_instances.
#[global]
Hint Extern 4 (@leaderLogs_candidate_entries_interface _ _ _) => apply llcei : typeclass_instances.
#[global]
Hint Extern 4 (@allEntries_candidate_entries_interface _ _ _) => apply aecei : typeclass_instances.
#[global]
Hint Extern 4 (@allEntries_log_matching_interface _ _ _) => apply aelmi : typeclass_instances.
#[global]
Hint Extern 4 (@append_entries_request_term_sanity_interface _ _ _) => apply aertsi : typeclass_instances.
#[global]
Hint Extern 4 (@allEntries_leader_sublog_interface _ _ _) => apply aelsi : typeclass_instances.
#[global]
Hint Extern 4 (@lastApplied_commitIndex_match_interface _ _ _) => apply lacimi : typeclass_instances.
#[global]
Hint Extern 4 (@lastApplied_le_commitIndex_interface _ _ _) => apply lalcii : typeclass_instances.
#[global]
Hint Extern 4 (@allEntries_leaderLogs_term_interface _ _ _) => apply aellti : typeclass_instances.
#[global]
Hint Extern 4 (@state_machine_correct_interface _ _ _) => apply smci : typeclass_instances.
#[global]
Hint Extern 4 (@output_greatest_id_interface _ _ _) => apply ogii : typeclass_instances.
#[global]
Hint Extern 4 (@current_term_gt_zero_interface _ _ _) => apply ctgzi : typeclass_instances.
#[global]
Hint Extern 4 (@terms_and_indices_from_one_log_interface _ _ _) => apply taifoli : typeclass_instances.
#[global]
Hint Extern 4 (@terms_and_indices_from_one_interface _ _ _) => apply taifoi : typeclass_instances.
#[global]
Hint Extern 4 (@candidate_term_gt_log_interface _ _ _) => apply ctgli : typeclass_instances.
#[global]
Hint Extern 4 (@votes_votesWithLog_correspond_interface _ _ _) => apply vvci : typeclass_instances.
#[global]
Hint Extern 4 (@prevLog_leader_sublog_interface _ _ _) => apply pllsi : typeclass_instances.
#[global]
Hint Extern 4 (@allEntries_indices_gt_0_interface _ _ _) => apply aeigt0 : typeclass_instances.
#[global]
Hint Extern 4 (@prevLog_candidateEntriesTerm_interface _ _ _) => apply plceti : typeclass_instances.
#[global]
Hint Extern 4 (@match_index_all_entries_interface _ _ _) => apply miaei : typeclass_instances.
#[global]
Hint Extern 4 (@match_index_leader_interface _ _ _) => apply mili : typeclass_instances.
#[global]
Hint Extern 4 (@match_index_sanity_interface _ _ _) => apply matchisi : typeclass_instances.
#[global]
Hint Extern 4 (@no_append_entries_to_leader_interface _ _ _) => apply noaetli : typeclass_instances.
#[global]
Hint Extern 4 (@no_append_entries_to_self_interface _ _ _) => apply noaetsi : typeclass_instances.
#[global]
Hint Extern 4 (@no_append_entries_replies_to_self_interface _ _ _) => apply noaertsi : typeclass_instances.
#[global]
Hint Extern 4 (@log_all_entries_interface _ _ _) => apply laei : typeclass_instances.
#[global]
Hint Extern 4 (@append_entries_reply_sublog_interface _ _ _) => apply aersi : typeclass_instances.
#[global]
Hint Extern 4 (@log_properties_hold_on_leader_logs_interface _ _ _) => apply lpholli : typeclass_instances.
#[global]
Hint Extern 4 (@log_properties_hold_on_ghost_logs_interface _ _ _) => apply lphogli : typeclass_instances.
#[global]
Hint Extern 4 (@append_entries_request_reply_correspondence_interface _ _ _) => apply aerrci : typeclass_instances.
#[global]
Hint Extern 4 (@append_entries_leader_interface _ _ _) => apply appendeli : typeclass_instances.
#[global]
Hint Extern 4 (@requestVote_maxIndex_maxTerm_interface _ _ _) => apply rvmimti : typeclass_instances.
#[global]
Hint Extern 4 (@requestVoteReply_moreUpToDate_interface _ _ _) => apply rvrmutdi : typeclass_instances.
#[global]
Hint Extern 4 (@requestVoteReply_term_sanity_interface _ _ _) => apply rvrtsi : typeclass_instances.
#[global]
Hint Extern 4 (@requestVote_term_sanity_interface _ _ _) => apply rvtsi : typeclass_instances.
#[global]
Hint Extern 4 (@votedFor_moreUpToDate_interface _ _ _) => apply vfmutdi : typeclass_instances.
#[global]
Hint Extern 4 (@votedFor_term_sanity_interface _ _ _) => apply vftsi : typeclass_instances.
#[global]
Hint Extern 4 (@votesReceived_moreUpToDate_interface _ _ _) => apply vrmutdi : typeclass_instances.
#[global]
Hint Extern 4 (@ghost_log_correct_interface _ _ _) => apply glci : typeclass_instances.
#[global]
Hint Extern 4 (@in_log_in_all_entries_interface _ _ _) => apply iliaei : typeclass_instances.
#[global]
Hint Extern 4 (@ghost_log_allEntries_interface _ _ _) => apply glaei : typeclass_instances.
#[global]
Hint Extern 4 (@ghost_log_entries_match_interface _ _ _) => apply glemi : typeclass_instances.

Section EndToEndProof.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Theorem raft_linearizable :
    forall failed net tr,
      input_correct tr ->
      step_failure_star (params := failure_params) step_failure_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
  Proof using. 
    intros.
    eapply (@raft_linearizable' orig_base_params one_node_params raft_params); eauto;
    auto with typeclass_instances.
  Qed.
End EndToEndProof.

