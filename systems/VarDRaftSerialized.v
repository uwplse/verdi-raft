Require Import Cheerios.Cheerios.

Require Import VerdiRaft.VarDRaft.
Require Import VerdiRaft.EndToEndLinearizability.

Require Import VerdiCheerios.SerializedMsgParams.
Require Import VerdiCheerios.SerializedMsgParamsCorrect.

Import VarD.
Import DeserializerNotations.
Import Raft.

Section Serialized.
  Variable n : nat.

  Notation "a +++ b" := (IOStreamWriter.append (fun _ => a) (fun _ => b))
                        (at level 100, right associativity).

  Definition base_params : Net.BaseParams :=
    VarD.VarD.vard_base_params.
  
  Definition raft_params : Raft.RaftParams base_params :=
    raft_params n.
  
  Definition entry := (@Raft.entry base_params raft_params).

  Definition serialize_input (i : VarD.input) :=
    match i with
    | Put k v => serialize x00 +++ serialize k +++ serialize v
    | Get k => serialize x01 +++ serialize k
    | Del k => serialize x02 +++ serialize k
    | CAS k opt v => serialize x03 +++ serialize k +++ serialize opt +++ serialize v
    | CAD k v => serialize x04 +++ serialize k +++ serialize v
    end.

  Import ByteListReader.
  Definition deserialize_input : ByteListReader.t VarD.input :=
    tag <- deserialize;;
        match tag with
        | x00 => k <- deserialize;;
                   v <- deserialize;;
                   ret (Put k v)
        | x01 => Get <$> deserialize
        | x02 => Del <$> deserialize
        | x03 => k <- deserialize;;
                   opt <- deserialize;;
                   v <- deserialize;;
                   ret (CAS k opt v)
        | x04 => k <- deserialize;;
                   v <- deserialize;;
                   ret (CAD k v)
        | _ => error
        end.

  Lemma input_serialize_deserialize_id :
    serialize_deserialize_id_spec serialize_input deserialize_input.
  Proof.
    intros.
    unfold serialize_input, deserialize_input.
    destruct a;
      repeat (cheerios_crush; simpl).
  Qed.

  Instance input_Serializer : Serializer VarD.input.
  Proof.
    exact {| serialize := serialize_input;
             deserialize := deserialize_input;
             serialize_deserialize_id := input_serialize_deserialize_id |}.
  Qed.
  
  Definition entry_serialize (e : entry) := 
   serialize (Raft.eAt e) +++
              serialize (Raft.eClient e) +++
              serialize (Raft.eId e) +++
              serialize (Raft.eIndex e) +++
              serialize (Raft.eTerm e) +++
              serialize (Raft.eInput e).

    Definition entry_deserialize : ByteListReader.t entry := 
    At <- deserialize;;
       Client <- deserialize;;
       Id <- deserialize;;
       Index <- deserialize;;
       Term <- deserialize;;
       Input <- deserialize;;
       ret (Raft.mkEntry At Client Id Index Term Input).

  Lemma entry_serialize_deserialize_id :
    serialize_deserialize_id_spec entry_serialize entry_deserialize.
  Proof.
    intros.
    unfold entry_serialize, entry_deserialize.
    cheerios_crush.
    destruct a;
      reflexivity.
  Qed.
  
  Instance entry_Serializer : Serializer entry.
  Proof.
    exact {| serialize := entry_serialize;
             deserialize := entry_deserialize;
             serialize_deserialize_id := entry_serialize_deserialize_id |}.
  Qed.

  (* msg *)

  Definition msg := @Raft.msg base_params raft_params.
  
  Definition msg_serialize (m : msg) : IOStreamWriter.t :=
    match m with
    | RequestVote t1 n i t2 =>
      serialize x00 +++
                serialize t1 +++
                serialize n +++
                serialize i +++
                serialize t2
    | RequestVoteReply t b =>
      serialize x01 +++ serialize t +++ serialize b
    | AppendEntries t1 n i1 t2 l2 i2 =>
      serialize x02 +++
                serialize t1 +++
                serialize n +++
                serialize i1 +++
                serialize t2 +++
                serialize l2 +++
                serialize i2
    | AppendEntriesReply t l b =>
      serialize x03 +++ serialize t +++ serialize l +++ serialize b
    end.

  Definition RequestVote_deserialize : ByteListReader.t msg :=
    t1 <- deserialize;;
       n <- deserialize;;
       i <- deserialize;;
       t2 <- deserialize;;
       ret (RequestVote t1 n i t2).

  Definition RequestVoteReply_deserialize : ByteListReader.t msg :=
    t <- deserialize;;
      b <- deserialize;;
      ret (RequestVoteReply t b).

  Definition AppendEntries_deserialize : ByteListReader.t msg :=
    t1 <- deserialize;;
       n <- deserialize;;
       i1 <- deserialize;;
       t2 <- deserialize;;
       l <- deserialize;;
       i2 <- deserialize;;
       ret (AppendEntries t1 n i1 t2 l i2).
  
  Definition AppendEntriesReply_deserialize : ByteListReader.t msg :=
    t <- deserialize;;
      l <- deserialize;;
      b <- deserialize;;
      ret (AppendEntriesReply t l b).
  
  Definition msg_deserialize :=
    tag <- deserialize;;
    match tag with
    | x00 => RequestVote_deserialize
    | x01 => RequestVoteReply_deserialize
    | x02 => AppendEntries_deserialize
    | x03 => AppendEntriesReply_deserialize
    | _ => error
    end.

  Lemma msg_serialize_deserialize_id :
    serialize_deserialize_id_spec msg_serialize msg_deserialize.
  Proof.
    intros.
    unfold msg_serialize, msg_deserialize.
    destruct a;
      cheerios_crush;
      simpl;
      (unfold RequestVote_deserialize ||
       unfold RequestVoteReply_deserialize ||
       unfold AppendEntries_deserialize ||
       unfold AppendEntriesReply_deserialize);
      cheerios_crush.
  Qed.

  Instance msg_Serializer : Serializer msg.
  Proof.
    exact {| serialize := msg_serialize;
             deserialize := msg_deserialize;
             serialize_deserialize_id := msg_serialize_deserialize_id |}.
  Qed.

  Definition orig_base_params := vard_raft_base_params n.
  Definition orig_multi_params := vard_raft_multi_params n.

  Definition transformed_base_params :=
    @serialized_base_params orig_base_params.

  Definition transformed_multi_params :=
    @serialized_multi_params orig_base_params
                             orig_multi_params
                             msg_Serializer.

  Definition transformed_failure_params :=
    @serialized_failure_params orig_base_params
                               orig_multi_params
                               (vard_raft_failure_params n)
                               msg_Serializer.
End Serialized.
