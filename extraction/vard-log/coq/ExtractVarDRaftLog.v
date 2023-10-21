From Verdi Require Import Verdi VarD.
From Cheerios Require Import Cheerios.
From VerdiRaft Require Import VarDRaftLog.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
From Verdi Require Import ExtrOcamlBasicExt ExtrOcamlNatIntExt.
From Verdi Require Import ExtrOcamlBool ExtrOcamlList ExtrOcamlFinInt ExtrOcamlDiskOp.
From Cheerios Require Import ExtrOcamlCheeriosBasic ExtrOcamlCheeriosNatInt.
From Cheerios Require Import ExtrOcamlCheeriosString ExtrOcamlCheeriosFinInt.

Extraction "extraction/vard-log/ml/VarDRaftLog.ml" seq transformed_base_params
  transformed_multi_params transformed_failure_params.
