PYTHON=python2.7

OCAMLBUILD = ocamlbuild -tag safe_string -package verdi-runtime -I ml -cflag -g
OCAMLBUILD_TEST = $(OCAMLBUILD) -package oUnit -I test

VARDRAFT = ml/VarDRaftDiskless.ml ml/VarDRaftDiskless.mli
VARD = ml/VarDDisklessArrangement.ml ml/varddiskless.ml ml/VarDDisklessSerialization.ml

default: varddiskless.native

varddiskless.native: $(VARD) $(VARDRAFT)
	$(OCAMLBUILD) varddiskless.native

$(VARDRAFT):
	+$(MAKE) -C ../.. extraction/vard-diskless/$@

test-integration: varddiskless.native test/integration.py
	$(PYTHON) test/integration.py

test: test-integration

clean:
	$(OCAMLBUILD) -clean

.PHONY: default test-integration test clean clear-data run debug bench-vard bench-etcd $(VARDRAFT)

.NOTPARALLEL: varddiskless.native
.NOTPARALLEL: $(VARDRAFT)
