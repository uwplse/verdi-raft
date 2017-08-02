Require Import Verdi.Verdi.
Require Import Verdi.VarD.
Require Import Verdi.PartialMapSimulations.
Require Import Cheerios.Cheerios.
Require Import VerdiRaft.Raft.

Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.Linearizability.
Require Import VerdiRaft.RaftLinearizableProofs.

Require Import VerdiRaft.EndToEndLinearizability.
Require Import VerdiCheerios.SerializedMsgParamsCorrect.

Require Import VerdiRaft.VarDRaftSerialized.

Require Import mathcomp.ssreflect.ssreflect.

Section SerializedCorrect.
  Variable n : nat.

  Instance raft_params : RaftParams VarD.vard_base_params :=
    raft_params n.

  Instance base_params : BaseParams :=
    transformed_base_params n.

  Instance multi_params : MultiParams _ :=
    transformed_multi_params n.

  Instance failure_params : FailureParams _ :=
    transformed_failure_params n.

  Lemma correct_input_correct_filterMap_ptr_trace_remove_empty_out :
    forall tr,
      input_correct tr ->
      input_correct (filterMap pt_trace_remove_empty_out tr).
  Proof.
    elim => //=.
    case => nm; case.
    - move => i tr IH H_inp => /=.
      have H_inp': input_correct tr.
      move => client id i0 i1 h h' H_in H_in'.
        by eapply H_inp; right; eauto.
        apply IH in H_inp'.
        move => client id i0 i1 h h' H_in H_in'.
        case: H_in => H_in; case: H_in' => H_in'.
      * by find_injection; find_injection.
      * find_injection.
        rewrite -/(In _ _) in H_in'.
        eapply H_inp; eauto; first by left; eauto.
        right.
        apply In_filterMap in H_in'.
        break_exists.
        break_and.
        destruct x.
        move: H0.
        destruct s => //=; last by destruct l => //; find_injection.
        case => H_eq H_eq'; subst.
          by eauto.
      * find_injection.
        rewrite -/(In _ _) in H_in.
        eapply H_inp; eauto; last by left; eauto.
        right.
        apply In_filterMap in H_in.
        break_exists.
        break_and.
        destruct x.
        move: H0.
        destruct s => //=; last by destruct l => //; find_injection.
        case => H_eq H_eq'; subst.
          by eauto.
      * rewrite -/(In _ _) in H_in.
        rewrite -/(In _ _) in H_in'.
          by eapply H_inp'; eauto.     
    - case => //=.
      * move => l IH H_inp.
        apply: IH.
        move => client id i0 i1 h h' H_in H_in'.
          by eapply H_inp; right; eauto.
      * move => o l tr IH H_inp.
        have H_inp': input_correct tr.
        move => client id i0 i1 h h' H_in H_in'.
          by eapply H_inp; right; eauto.
          apply IH in H_inp'.
          move => client id i0 i1 h h'.
          case => // H_in.
          case => // H_in'.
            by eapply H_inp'; eauto.
  Qed.

  Lemma correct_filterMap_ptr_trace_remove_empty_out_input_correct :
    forall tr,
      input_correct (filterMap pt_trace_remove_empty_out tr) ->
      input_correct tr.
  Proof.
    elim => //=.
    case => nm [i|o] tr IH /=.
    - move: IH.
      set f := filterMap _ _.
      move => IH H_inp.
      have H_inp': input_correct f.
      move => client id i0 i1 h h' H_in H_in'.
        by eapply H_inp; right; eauto.
        concludes.
        move => client id i0 i1 h h' H_in H_in'.
        case: H_in => H_in; case: H_in' => H_in'.
      * by find_injection; find_injection.
      * find_injection.
        eapply H_inp; first by left.
        right.
        eapply filterMap_In; eauto.
          by rewrite /=; eauto.
      * find_injection.
        eapply H_inp; last by left.
        right.
        eapply filterMap_In; eauto.
          by rewrite /=; eauto.
      * by eapply IH; eauto.
    - case: o => [|o l] H_eq //=.
      * move => client id i0 i1 h h'.
        case => H_in //.
        case => H_in' //.
        concludes.
          by eapply IH; eauto.
      * move: IH H_eq.
        set f := filterMap _ _.
        move => IH H_inp.
        have H_inp': input_correct f.
        move => client id i0 i1 h h' H_in H_in'.
          by eapply H_inp; right; eauto.
          concludes.
          move => client id i0 i1 h h'.
          case => H_in //.
          case => H_in' //.
            by eapply IH; eauto.
  Qed.

  Lemma input_correct_filterMap_ptr_trace_remove_empty_out :
    forall tr tr',
      input_correct tr ->
      filterMap pt_trace_remove_empty_out tr = filterMap pt_trace_remove_empty_out tr' ->
      input_correct tr'.
  Proof.
    move => tr tr' H_in H_eq.
    apply correct_filterMap_ptr_trace_remove_empty_out_input_correct.
    rewrite -H_eq.
    exact: correct_input_correct_filterMap_ptr_trace_remove_empty_out.
  Qed.

  Lemma get_input_tr_filterMap_ptr_trace_remove_empty_out :
    forall tr,
      get_input tr = get_input (filterMap pt_trace_remove_empty_out tr).
  Proof.
    elim => //=.
    case => nm [i|o] l IH.
    - by rewrite /= -IH.
    - by case: o.
  Qed.

  Lemma get_output_tr_filterMap_ptr_trace_remove_empty_out :
    forall tr,
      get_output tr = get_output (filterMap pt_trace_remove_empty_out tr).
  Proof.
    elim => //=.
    case => nm [i|o] l IH /=.
    - by rewrite IH.
    - rewrite /= IH.
        by case: o.
  Qed.

  Lemma exported_filterMap_pt_trace_remove_empty_out : 
    forall tr tr' l tr1,
      exported (get_input tr') (get_output tr') l tr1 ->
      filterMap pt_trace_remove_empty_out tr = filterMap pt_trace_remove_empty_out tr' ->
      exported (get_input tr) (get_output tr) l tr1.
  Proof.
    move => tr tr' l tr1 H_exp H_eq.
    move: H_exp.
    rewrite get_input_tr_filterMap_ptr_trace_remove_empty_out get_output_tr_filterMap_ptr_trace_remove_empty_out.
    rewrite -H_eq.
      by rewrite -get_input_tr_filterMap_ptr_trace_remove_empty_out -get_output_tr_filterMap_ptr_trace_remove_empty_out.
  Qed.

  Lemma import_exported_filterMap_pt_trace_remove_empty_out : 
    forall tr,
      import tr = import (filterMap pt_trace_remove_empty_out tr).
  Proof.
    elim => //=.
    case => nm [i|o] l IH /=.
    - by rewrite -IH.
    - rewrite IH.
        by case: o.
  Qed.

  Lemma equivalent_filterMap_pt_trace_remove_empty_out :
    forall tr tr' l,
      equivalent key (import tr') l ->
      filterMap pt_trace_remove_empty_out tr = filterMap pt_trace_remove_empty_out tr' ->
      equivalent key (import tr) l.
  Proof.
    move => tr tr' l H_equ H_eq.
    rewrite import_exported_filterMap_pt_trace_remove_empty_out H_eq.
      by rewrite -import_exported_filterMap_pt_trace_remove_empty_out.
  Qed.

  Theorem serialized_raft_linearizable :
    forall failed net tr,
      input_correct tr ->
      step_failure_star step_failure_init (failed, net) tr ->
      exists l tr1 st,
        equivalent _ (import tr) l /\
        exported (get_input tr) (get_output tr) l tr1 /\
        step_1_star init st tr1.
  Proof using.
    intros.
    apply step_failure_deserialized_simulation_star in H0.
    break_exists.
    break_and.
    apply raft_linearizable in H0.
    - break_exists.
      break_and.
      exists x0.
      exists x1.
      exists x2.
      split.
      * eapply equivalent_filterMap_pt_trace_remove_empty_out; eauto.
      * split; auto. eapply exported_filterMap_pt_trace_remove_empty_out; eauto.
    - eapply input_correct_filterMap_ptr_trace_remove_empty_out; eauto.
  Qed.
End SerializedCorrect.
