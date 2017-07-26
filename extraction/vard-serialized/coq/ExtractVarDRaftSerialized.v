Require Import Verdi.Verdi.
Require Import Verdi.VarD.
Require Import VerdiRaft.VarDRaftSerialized.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Verdi.ExtrOcamlBasicExt.
Require Import Verdi.ExtrOcamlNatIntExt.

Require Import Verdi.ExtrOcamlBool.
Require Import Verdi.ExtrOcamlList.
Require Import Verdi.ExtrOcamlFin.

Require Import Cheerios.Cheerios.
Require Import Cheerios.ExtrCheerios.

Extract Inlined Constant nat_serialize => "(fun i -> Serializer_primitives.putInt (Int32.of_int i))".

Extract Inlined Constant nat_deserialize => "(Serializer_primitives.map Int32.to_int Serializer_primitives.getInt)".

Extract Inlined Constant ascii_serialize => "Serializer_primitives.putByte".
Extract Inlined Constant ascii_deserialize => "Serializer_primitives.getByte".

Extraction "extraction/vard-serialized/ml/VarDRaftSerialized.ml" seq transformed_base_params transformed_multi_params transformed_failure_params.
