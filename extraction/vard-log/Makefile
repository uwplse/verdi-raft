OCAMLBUILD = ocamlbuild -tag safe_string -pkgs 'verdi-runtime cheerios-runtime' -I ml -cflag -g
OCAMLBUILD_TEST := $(OCAMLBUILD) -package oUnit -I test

VARDRAFTLOG = ml/VarDRaftLog.ml ml/VarDRaftLog.mli
VARDLOG = ml/vardlog.ml ml/DiskOpShim.ml

default: vardlog.native

vardlog.native: $(VARDLOG) $(VARDRAFTLOG) scripts/remove_module.pl
	perl scripts/remove_module.pl ml/VarDRaftLog
	$(OCAMLBUILD) vardlog.native

$(VARDRAFTLOG):
	+$(MAKE) -C ../.. extraction/vard-log/$@
clean:
	ocamlbuild -clean

.PHONY: default clean $(VARDRAFTLOG)

.NOTPARALLEL: $(VARDRAFTLOG)
