From Verdi Require Import Verdi VarD.
From VerdiRaft Require Import VarDRaft.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
From Verdi Require Import ExtrOcamlBasicExt ExtrOcamlNatIntExt.
From Verdi Require Import ExtrOcamlBool ExtrOcamlList ExtrOcamlFinInt.

Extraction "VarDRaft.ml" seq vard_raft_base_params
  vard_raft_multi_params vard_raft_failure_params.
