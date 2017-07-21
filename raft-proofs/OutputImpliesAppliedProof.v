Require Import Verdi.TraceRelations.

Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.AppliedEntriesMonotonicInterface.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.TraceUtil.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Require Import VerdiRaft.SortedInterface.

Require Import VerdiRaft.OutputImpliesAppliedInterface.

Section OutputImpliesApplied.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Context {lmi : log_matching_interface}.
  Context {si : sorted_interface}.
  Context {aemi : applied_entries_monotonic_interface}.
  Context {smsi : state_machine_safety_interface}.
  Context {misi : max_index_sanity_interface}.

  Section inner.
  Variables client id : nat.

  Lemma in_output_changed :
    forall tr o,
      ~ key_in_output_trace client id tr ->
      key_in_output_trace client id (tr ++ o) ->
      key_in_output_trace client id o.
  Proof using. 
    intros. unfold key_in_output_trace in *.
    break_exists_exists.
    intuition. do_in_app; intuition.
    exfalso. eauto.
  Qed.

  Lemma key_in_output_list_split :
    forall l l',
      key_in_output_list client id (l ++ l') ->
      key_in_output_list client id l \/ key_in_output_list client id l'.
  Proof using. 
    intros.
    unfold key_in_output_list in *.
    break_exists; do_in_app; intuition eauto.
  Qed.

  Lemma key_in_output_list_empty :
    ~ key_in_output_list client id [].
  Proof using. 
    intuition.
    unfold key_in_output_list in *.
    break_exists; intuition.
  Qed.

  Lemma doLeader_key_in_output_list :
    forall st h out st' m,
      doLeader st h = (out, st', m) ->
      ~ key_in_output_list client id out.
  Proof using. 
    intros. unfold doLeader, advanceCommitIndex in *.
    repeat break_match; find_inversion; intuition eauto using key_in_output_list_empty.
  Qed.

  Lemma handleInput_key_in_output_list :
    forall st h i out st' m,
      handleInput h i st = (out, st', m) ->
      ~ key_in_output_list client id out.
  Proof using. 
    intros. unfold handleInput, handleTimeout, handleClientRequest, tryToBecomeLeader in *.
    repeat break_match; find_inversion; intuition eauto using key_in_output_list_empty;
    unfold key_in_output_list in *; break_exists; simpl in *; intuition; congruence.
  Qed.

  Lemma applyEntries_In :
    forall l h st os st' o,
      applyEntries h st l = (os, st') ->
      In (ClientResponse client id o) os ->
      exists e : entry,
        eClient e = client /\
        eId e = id /\
        In e l.
  Proof using. 
    induction l; intros.
    - simpl in *.
      find_inversion; simpl in *; intuition.
    - simpl in *. repeat break_let.
      repeat break_match; find_inversion; simpl in *; intuition;
      try find_inversion; simpl in *; try do_in_app; intuition eauto;
      try solve [find_eapply_lem_hyp IHl; eauto;
                 break_exists_exists; intuition];
      try do_in_map; find_inversion; eexists; eauto.
  Qed.

  Lemma doGenericServer_key_in_output_list :
    forall net h os st' ms,
      raft_intermediate_reachable net ->
      doGenericServer h (nwState net h) = (os, st', ms) ->
      key_in_output_list client id os ->
      exists e : entry,
        eClient e = client /\
        eId e = id /\ In e (applied_entries (update name_eq_dec (nwState net) h st')).
  Proof using misi smsi lmi. 
    intros. unfold key_in_output_list in *.
    match goal with | H : exists _, _ |- _ => destruct H as [o] end.
    unfold doGenericServer in *. break_let. simpl in *.
    find_inversion. simpl in *. 
    pose proof Heqp as Happ.
    find_eapply_lem_hyp applyEntries_In; eauto.
    use_applyEntries_spec; subst_max; simpl in *.
    eexists; intuition eauto.
    find_apply_lem_hyp In_rev.
    find_apply_lem_hyp filter_In.
    intuition. repeat (do_bool; intuition).
    break_if; simpl in *; do_bool; [|try omega].
    match goal with
      | |- context [update _ ?st ?h ?st'] =>
        pose proof applied_entries_update st h st'
    end. forwards; [simpl in *; intuition|]. concludes.
    intuition.
    - simpl in *. unfold raft_data in *. simpl in *.
      find_rewrite.
      match goal with | H : applied_entries _ = applied_entries _ |- _ => clear H end.
      break_exists. intuition.
      unfold applied_entries in *.
      find_rewrite.
      match goal with
        | |- In _ (rev ?l') => apply in_rev with (l := l')
      end.
      apply removeAfterIndex_le_In; intuition.
      find_copy_apply_lem_hyp log_matching_invariant.
      find_copy_apply_lem_hyp max_index_sanity_invariant.
      find_apply_lem_hyp state_machine_safety_invariant.
      unfold state_machine_safety, log_matching, log_matching_hosts, maxIndex_sanity in *.
      intuition.
      match goal with
        | [ e : entry, H : forall _ _, _ <= _ <= _ -> _, Hm : maxIndex_lastApplied _
                                                   |- In _ (log (_ _ ?h)) ] =>
          specialize (H h (eIndex e)); specialize (Hm h); forward H; intuition
      end. break_exists. intuition.
      find_apply_lem_hyp findGtIndex_necessary. intuition.
      match goal with
        | _ : In ?e1 (log _), _ : In ?e2 (log _) |- _ =>
          cut (e1 = e2); [intros; subst; auto|]
      end. eapply_prop state_machine_safety_host; unfold commit_recorded; intuition eauto.
      omega.
    - simpl in *. unfold raft_data in *. simpl in *.
      find_rewrite.
      match goal with
        | |- In _ (rev ?l') => apply in_rev with (l := l')
      end.
      find_apply_lem_hyp findGtIndex_necessary.
      intuition.
      eauto using removeAfterIndex_le_In.
  Qed.

  Lemma output_implies_in_applied_entries :
    forall failed net failed' net' o,
      raft_intermediate_reachable net ->
      @step_failure _ _ failure_params (failed, net) (failed', net') o ->
      key_in_output_trace client id o ->
      in_applied_entries client id net'.
  Proof using misi smsi lmi. 
    intros.
    invcs H0; simpl in *;
    try match goal with
          | _ : key_in_output_trace _ _ [] |- _ =>
            unfold key_in_output_trace in *; break_exists; simpl in *; intuition
        end.
    - unfold key_in_output_trace in *.
      break_exists; simpl in *; intuition.
      find_inversion.
      unfold in_applied_entries in *. simpl in *.
      unfold RaftNetHandler in *.
      repeat break_let. repeat find_inversion. simpl in *.
      find_eapply_lem_hyp RIR_handleMessage; eauto.
      find_apply_lem_hyp key_in_output_list_split.
      find_copy_apply_lem_hyp doLeader_key_in_output_list.
      intuition.
      match goal with
        | H : doLeader ?st ?h = _ |- _ =>
          replace st with ((update name_eq_dec (nwState net) h st) h) in H;
            [|rewrite_update; auto]
      end.
      find_eapply_lem_hyp RIR_doLeader; eauto.
      simpl in *.
      match goal with
        | _ : raft_intermediate_reachable ?net' |- context [update _ (nwState net) ?h ?d] =>
          remember net' as n;
            assert ((update name_eq_dec (nwState net) h d) = (update name_eq_dec (nwState n) h d)) by
              (subst; simpl in *; repeat rewrite update_overwrite; auto)
      end.
      unfold raft_data in *. simpl in *.
      unfold raft_data in *. simpl in *.
      repeat find_rewrite.
      eapply doGenericServer_key_in_output_list; eauto.
      simpl in *. rewrite_update; eauto.
    - unfold key_in_output_trace in *.
      break_exists; simpl in *; intuition.
      find_inversion.
      unfold in_applied_entries in *. simpl in *.
      unfold RaftInputHandler in *.
      repeat break_let. repeat find_inversion. simpl in *.
      find_copy_eapply_lem_hyp RIR_handleInput; eauto.
      find_apply_lem_hyp key_in_output_list_split.
      intuition; [exfalso; eapply handleInput_key_in_output_list; eauto|].
      find_apply_lem_hyp key_in_output_list_split.
      intuition; [exfalso; eapply doLeader_key_in_output_list; eauto|].
      match goal with
        | H : doLeader ?st ?h = _ |- _ =>
          replace st with ((update name_eq_dec (nwState net) h st) h) in H;
            [|rewrite_update; auto]
      end.
      find_eapply_lem_hyp RIR_doLeader; eauto.
      simpl in *.
      match goal with
        | _ : raft_intermediate_reachable ?net' |- context [update _ (nwState net) ?h ?d] =>
          remember net' as n;
            assert ((update name_eq_dec (nwState net) h d) = (update name_eq_dec (nwState n) h d)) by
              (subst; simpl in *; repeat rewrite update_overwrite; auto)
      end.
      unfold raft_data in *. simpl in *.
      unfold raft_data in *. simpl in *.
      repeat find_rewrite.
      eapply doGenericServer_key_in_output_list; eauto.
      simpl in *. rewrite_update; eauto.
  Qed.

  Instance TR : TraceRelation step_failure :=
    {
      init := step_failure_init;
      T := key_in_output_trace client id ;
      T_dec := key_in_output_trace_dec client id ;
      R := fun s => in_applied_entries client id (snd s)
    }.
  Proof.
  - intros.
    unfold in_applied_entries in *.
    break_exists; eexists; intuition eauto.
    destruct s; destruct s'; eapply applied_entries_monotonic; eauto.
    eauto using refl_trans_1n_n1_trace, step_failure_star_raft_intermediate_reachable.
  - unfold key_in_output_trace in *. intuition.
    break_exists; intuition.
  - intros.
    destruct s as [failed net].
    destruct s' as [failed' net']. simpl in *.
    find_apply_lem_hyp step_failure_star_raft_intermediate_reachable.
    find_apply_lem_hyp in_output_changed; auto.
    eauto using output_implies_in_applied_entries.
  Defined.

  Theorem output_implies_applied :
    forall failed net tr,
      step_failure_star step_failure_init (failed, net) tr ->
      key_in_output_trace client id tr ->
      in_applied_entries client id net.
  Proof using misi smsi aemi lmi. 
    intros. pose proof (trace_relations_work (failed, net) tr).
    concludes. intuition.
  Qed.

  End inner.

  Instance oiai : output_implies_applied_interface.
  Proof.
    split.
    intros.
    eapply output_implies_applied; eauto.
  Qed.
End OutputImpliesApplied.
