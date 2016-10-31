PYTHON=python2.7
COQVERSION := $(shell coqc --version|grep "version 8.5")

ifeq "$(COQVERSION)" ""
$(error "Verdi Raft is only compatible with Coq version 8.5")
endif

COQPROJECT_EXISTS=$(wildcard _CoqProject)
ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

CHECKPATH := $(shell ./script/checkpaths.sh)

ifneq ("$(CHECKPATH)","")
$(info $(CHECKPATH))
$(warning checkpath reported an error)
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

proofalytics:
	$(MAKE) -C proofalytics clean
	$(MAKE) -C proofalytics
	$(MAKE) -C proofalytics publish

STDBUF=$(shell [ -x "$$(which gstdbuf)" ] && echo "gstdbuf" || echo "stdbuf")
proofalytics-aux: Makefile.coq
	sed "s|^TIMECMD=$$|TIMECMD=$(PWD)/proofalytics/build-timer.sh $(STDBUF) -i0 -o0|" \
	  Makefile.coq > Makefile.coq_tmp
	mv Makefile.coq_tmp Makefile.coq
	$(MAKE) -f Makefile.coq

ASSUMPTIONS_DEPS='script/assumptions.v raft-proofs/EndToEndLinearizability.vo'
ASSUMPTIONS_COMMAND='$$(COQC) $$(COQDEBUG) $$(COQFLAGS) script/assumptions.v'
VARDRAFT_DEPS='extraction/vard/coq/ExtractVarDRaft.v extraction/vard/coq/VarDRaft.vo'
VARDRAFT_COMMAND='$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/vard/coq/ExtractVarDRaft.v'
Makefile.coq: hacks _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq \
	  -extra 'script/assumptions.vo' $(ASSUMPTIONS_DEPS) $(ASSUMPTIONS_COMMAND) \
	  -extra 'script/assumptions.glob' $(ASSUMPTIONS_DEPS) $(ASSUMPTIONS_COMMAND) \
          -extra 'extraction/vard/ml/VarDRaft.ml' $(VARDRAFT_DEPS) $(VARDRAFT_COMMAND) \
          -extra 'extraction/vard/ml/VarDRaft.mli' $(VARDRAFT_DEPS) $(VARDRAFT_COMMAND) \

hacks: raft/RaftState.v

raft/RaftState.v:
	$(PYTHON) script/extract_record_notation.py raft/RaftState.v.rec raft_data > raft/RaftState.v

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq
	find . -name '*.buildtime' -delete
	$(MAKE) -C proofalytics clean

vard:
	@echo "To build everything (including vard) use the default target."
	@echo "To quickly provision vard use the vard-quick target."

vard-quick: Makefile.coq
	$(MAKE) -f Makefile.coq extraction/vard/ml/VarDRaft.ml extraction/vard/ml/VarDRaft.mli
	$(MAKE) -C extraction/vard

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject extraction/vard/lib

.PHONY: default quick clean vard vard-quick lint hacks proofalytics distclean
