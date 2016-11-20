PYTHON=python2.7

OCAMLBUILD = ocamlbuild -package uuidm -lib str -lib unix -I lib -I ml -cflag -g
OCAMLBUILD_TEST = ocamlbuild -package uuidm -package oUnit -lib str -I lib -I ml -I test -cflag -g

VARD = ml/VarDRaft.ml ml/VarDRaft.mli ml/VarDArrangement.ml ml/vard.ml ml/VarDSerialization.ml
VARD_TEST = test/TestCommon.ml test/OptsTest.ml test/VarDSerializationTest.ml test/VarDTest.ml
LIB = lib/Shim.ml lib/Util.ml lib/Opts.ml

default: vard.native

vard.native: $(LIB) $(VARD)
	$(OCAMLBUILD) vard.native

VarDTest.native: $(LIB) $(VARD) $(VARD_TEST)
	$(OCAMLBUILD_TEST) VarDTest.native

test-units: VarDTest.native
	./VarDTest.native

test-integration: vard.native test/integration.py
	$(PYTHON) test/integration.py

test: test-units test-integration

clean:
	$(OCAMLBUILD) vard.native -clean
	$(OCAMLBUILD_TEST) VarDTest.native -clean

clear-data:
	./scripts/clear-vard.sh

run: vard.native
	./scripts/start-tmux.sh

debug: vard.native
	./scripts/start-tmux-debug.sh

bench-vard: vard.native
	./scripts/bench-vard.sh
	./scripts/clear-vard.sh

bench-etcd: vard.native
	./scripts/bench-etcd.sh
	./scripts/clear-etcd.sh

.PHONY: default test-units test-integration test clean clear-data run debug bench-vard bench-etcd

.NOTPARALLEL: vard.native VarDTest.native
