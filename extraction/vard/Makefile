PYTHON=python2.7
OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -cflag -g
OCAMLBUILDTEST = ocamlbuild -package oUnit -lib str -I lib -I ml -I test -cflag -g
VARD = ml/VarDRaft.ml ml/VarDRaft.mli ml/VarDArrangement.ml ml/vard.ml
LIB = lib/Shim.ml

default: vard.native

vard.native: $(VARD) $(LIB)
	$(OCAMLBUILD) vard.native

VarDOptsTest.native: test/VarDOptsTest.ml
	$(OCAMLBUILDTEST) VarDOptsTest.native

test-units: VarDOptsTest.native
	./VarDOptsTest.native

test-integration: vard.native test/integration.py
	$(PYTHON) test/integration.py

test: test-units test-integration

clean:
	$(OCAMLBUILD) vard.native -clean
	$(OCAMLBUILDTEST) VarDOptsTest.native -clean

clear-data:
	./scripts/clear-verdi.sh

run: vard.native
	./scripts/start-tmux.sh

debug: vard.native
	./scripts/start-tmux-debug.sh

bench-vard: vard.native
	./scripts/bench-vard.sh
	./scripts/clear-verdi.sh

bench-etcd: vard.native
	./scripts/bench-etcd.sh
	./scripts/clear-etcd.sh

.PHONY: default test-units test-integration test clean clear-data run debug bench-vard bench-etcd
