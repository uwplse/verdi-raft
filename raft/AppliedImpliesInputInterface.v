Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.TraceUtil.

Section AppliedImpliesInputInterface.
  Context {orig_base_params : BaseParams}.
  Context {one_node_params : OneNodeParams orig_base_params}.
  Context {raft_params : RaftParams orig_base_params}.

  Section inner.
    Variables client id : nat.
    Variable i : input.

    Definition correct_entry (e : entry) : Prop :=
      eClient e = client /\
      eId e = id /\
      eInput e = i.

    Definition applied_implies_input_state (net : network) : Prop :=
      exists e,
        correct_entry e /\
        ((exists h, In e (log (nwState net h))) \/
         (exists p entries, In p (nwPackets net) /\
                            mEntries (pBody p) = Some entries /\
                            In e entries)).

  End inner.

  Class applied_implies_input_interface : Prop :=
    {
      applied_implies_input :
        forall client id failed net tr e,
          step_failure_star step_failure_init (failed, net) tr ->
          eClient e = client ->
          eId e = id ->
          applied_implies_input_state client id (eInput e) net ->
          in_input_trace client id (eInput e) tr
    }.
End AppliedImpliesInputInterface.
