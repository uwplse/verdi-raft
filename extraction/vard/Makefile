PYTHON=python2.7
OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -cflag -g
VARD = ml/VarDRaft.ml ml/VarDRaft.mli ml/VarDArrangement.ml ml/vard.ml
LIB = lib/Shim.ml

default: vard.native

vard.native: $(VARD) $(LIB)
	$(OCAMLBUILD) vard.native

test: vard.native test/integration.py
	$(PYTHON) test/integration.py

clean:
	$(OCAMLBUILD) vard.native -clean

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

.PHONY: default test clean clear-data run debug bench-vard bench-etcd
