Require Import Verdi.Verdi.
Require Import Cheerios.Cheerios.

Require Import Verdi.VarD.
Require Import VerdiRaft.VarDRaftLog.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlNatIntExt.

Require Import Verdi.ExtrOcamlBool.
Require Import Verdi.ExtrOcamlList.
Require Import Verdi.ExtrOcamlFinInt.

Require Import Cheerios.ExtrOcamlCheeriosBasic.
Require Import Cheerios.ExtrOcamlCheeriosNatInt.
Require Import Cheerios.ExtrOcamlCheeriosString.
Require Import Cheerios.ExtrOcamlCheeriosFinInt.

Extract Inductive disk_op => "DiskOpShim.disk_op"
                        ["DiskOpShim.Append" "DiskOpShim.Write" "DiskOpShim.Delete"].


Extraction "extraction/vard-log/ml/VarDRaftLog.ml" seq transformed_base_params transformed_multi_params transformed_failure_params.
