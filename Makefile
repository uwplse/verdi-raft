PYTHON=python2.7

# sets COQVERSION
include Makefile.detect-coq-version

ifeq (,$(filter $(COQVERSION),8.6 8.7 8.8 trunk))
$(error "Verdi Raft is only compatible with Coq version 8.6.1 or later")
endif

COQPROJECT_EXISTS := $(wildcard _CoqProject)

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

checkproofs: quick
	$(MAKE) -f Makefile.coq checkproofs

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

proofalytics:
	$(MAKE) -C proofalytics clean
	$(MAKE) -C proofalytics
	$(MAKE) -C proofalytics publish

STDBUF=$(shell [ -x "$$(which gstdbuf)" ] && echo "gstdbuf" || echo "stdbuf")
BUILDTIMER=$(PWD)/proofalytics/build-timer.sh $(STDBUF) -i0 -o0

proofalytics-aux: Makefile.coq
	$(MAKE) -f Makefile.coq TIMECMD="$(BUILDTIMER)"

VARDML = extraction/vard/ml/VarDRaft.ml extraction/vard/ml/VarDRaft.mli
VARDSERML = extraction/vard-serialized/ml/VarDRaftSerialized.ml extraction/vard-serialized/ml/VarDRaftSerialized.mli
VARDLOGML = extraction/vard-log/ml/VarDRaftLog.ml extraction/vard-log/ml/VarDRaftLog.mli
VARDSERLOGML = extraction/vard-serialized-log/ml/VarDRaftSerializedLog.ml extraction/vard-serialized-log/ml/VarDRaftSerializedLog.mli

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq \
	  -extra 'script/assumptions.vo script/assumptions.glob script/assumptions.v.d' \
	    'script/assumptions.v raft-proofs/EndToEndLinearizability.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) script/assumptions.v' \
          -extra '$(VARDML)' \
	    'extraction/vard/coq/ExtractVarDRaft.v systems/VarDRaft.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/vard/coq/ExtractVarDRaft.v' \
          -extra '$(VARDSERML)' \
	    'extraction/vard-serialized/coq/ExtractVarDRaftSerialized.v systems/VarDRaftSerialized.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/vard-serialized/coq/ExtractVarDRaftSerialized.v' \
          -extra '$(VARDLOGML)' \
	    'extraction/vard-log/coq/ExtractVarDRaftLog.v systems/VarDRaftLog.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/vard-log/coq/ExtractVarDRaftLog.v' \
          -extra '$(VARDSERLOGML)' \
	    'extraction/vard-serialized-log/coq/ExtractVarDRaftSerializedLog.v systems/VarDRaftSerializedLog.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/vard-serialized-log/coq/ExtractVarDRaftSerializedLog.v'

raft/RaftState.v: raft/RaftState.v.rec
	$(PYTHON) script/extract_record_notation.py raft/RaftState.v.rec raft_data > raft/RaftState.v

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq script/.assumptions.vo.aux script/.assumptions.aux
	find . -name '*.buildtime' -delete
	$(MAKE) -C proofalytics clean
	$(MAKE) -C extraction/vard clean
	$(MAKE) -C extraction/vard-serialized clean
	$(MAKE) -C extraction/vard-log clean
	$(MAKE) -C extraction/vard-serialized-log clean

$(VARDML) $(VARDSERML) $(VARDLOGML) $(VARDSERLOGML): Makefile.coq
	$(MAKE) -f Makefile.coq $@

vard:
	+$(MAKE) -C extraction/vard

vard-test:
	+$(MAKE) -C extraction/vard test

vard-serialized:
	+$(MAKE) -C extraction/vard-serialized

vard-serialized-test:
	+$(MAKE) -C extraction/vard-serialized test

vard-log:
	+$(MAKE) -C extraction/vard-log

vard-log-test:
	+$(MAKE) -C extraction/vard-log test

vard-serialized-log:
	+$(MAKE) -C extraction/vard-serialized-log

vard-serialized-log-test:
	+$(MAKE) -C extraction/vard-serialized-log test

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject

.PHONY: default quick install clean lint proofalytics distclean checkproofs
.PHONY: vard vard-test vard-serialized vard-serialized-test vard-log vard-log-test vard-serialized-log vard-serialized-log-test
.PHONY: $(VARDML) $(VARDSERML) $(VARDLOGML) $(VARDSERLOGML)

.NOTPARALLEL: $(VARDML)
.NOTPARALLEL: $(VARDSERML)
.NOTPARALLEL: $(VARDLOGML)
.NOTPARALLEL: $(VARDSERLOGML)
