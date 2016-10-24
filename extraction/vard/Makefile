OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -cflag -g
VARD = ml/VarDRaft.ml ml/VarDRaft.mli ml/VarDArrangement.ml ml/vard.ml
LIB = lib/Shim.ml

default: vard.native

vard.native: $(VARD) $(LIB)
	$(OCAMLBUILD) vard.native

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

.PHONY: default run clear-data
