PYTHON=python2.7
COQVERSION := $(shell coqc --version|grep -E "version 8.6")

ifeq "$(COQVERSION)" ""
$(error "Verdi Raft is only compatible with Coq version 8.6")
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
	+$(MAKE) -C extraction/vard

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

MLFILES = extraction/vard/ml/VarDRaft.ml extraction/vard/ml/VarDRaft.mli

Makefile.coq: raft/RaftState.v _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq -no-install \
	  -extra 'script/assumptions.vo script/assumptions.glob script/assumptions.v.d' \
	    'script/assumptions.v raft-proofs/EndToEndLinearizability.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) script/assumptions.v' \
          -extra '$(MLFILES)' \
	    'extraction/vard/coq/ExtractVarDRaft.v extraction/vard/coq/VarDRaft.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/vard/coq/ExtractVarDRaft.v' \
          -extra-phony 'distclean' 'clean' \
	    'rm -f $$(join $$(dir $$(VFILES)),$$(addprefix .,$$(notdir $$(patsubst %.v,%.aux,$$(VFILES)))))'

raft/RaftState.v:
	$(PYTHON) script/extract_record_notation.py raft/RaftState.v.rec raft_data > raft/RaftState.v

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq distclean; fi
	rm -f Makefile.coq raft/RaftState.v script/.assumptions.aux
	find . -name '*.buildtime' -delete
	$(MAKE) -C proofalytics clean
	$(MAKE) -C extraction/vard clean

vard:
	@echo "To build everything (including vard) use the default target."
	@echo "To quickly provision vard use the vard-quick target."

$(MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

vard-quick:
	+$(MAKE) -C extraction/vard

vard-test:
	+$(MAKE) -C extraction/vard test

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject

.PHONY: default quick clean vard vard-quick vard-test lint proofalytics distclean $(MLFILES)
