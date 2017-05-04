Verdi Raft
==========

[![Build Status](https://api.travis-ci.org/uwplse/verdi-raft.svg?branch=master)](https://travis-ci.org/uwplse/verdi-raft)

An implementation of the [Raft](https://raft.github.io) distributed consensus protocol, verified in Coq using the Verdi framework.

Requirements
------------

Definitions and proofs:

- [`Coq 8.5`](https://coq.inria.fr/coq-85)
- [`Verdi`](https://github.com/uwplse/verdi)
- [`StructTact`](https://github.com/uwplse/StructTact)

Executable `vard` key-value store:

- [`OCaml 4.02.3`](https://coq.inria.fr/download)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`verdi-runtime`](https://github.com/DistributedComponents/verdi-runtime)

Client for `vard`:

- [`Python 2.7`](https://www.python.org/download/releases/2.7/)

Testing of unverified code in `vard`:

- [`Python 2.7`](https://www.python.org/download/releases/2.7/)
- [`OUnit 2.0.0`](http://ounit.forge.ocamlcore.org)

Building
--------

We recommend installing the dependencies of Verdi Raft via
[OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam pin add coq 8.5.3
opam install verdi StructTact verdi-runtime ocamlbuild
```

Then, run `./configure` in the Verdi Raft root directory.  This will check
for the appropriate version of Coq and ensure all necessary
Coq dependencies can be located. By default, `Verdi` and `StructTact`
are assumed to be installed in Coq's `user-contrib` directory, but
this can be overridden by setting the `Verdi_PATH` and `StructTact_PATH`
environment variables.

Finally, run `make` in the root directory. This will compile the Raft
implementation and proof interfaces, check all the proofs, and
build the `vard` key-value store.

Files
-----

The `raft` and `raft-proofs` subdirectories contain the implementation and
verification of Raft. For each proof interface file in `raft`, there is a 
corresponding proof file in `raft-proofs`. The files in the `raft` 
subdirectory include:

- `Raft.v`: an implementation of Raft in Verdi
- `RaftRefinementInterface.v`: an application of the ghost-variable transformer
  to Raft which tracks several ghost variables used in the
  verification of Raft
- `CommonTheorems.v`: several useful theorems about functions used by
  the Raft implementation
- `OneLeaderPerTermInterface`: a statement of Raft's *election
  safety* property. See also the corresponding proof file in `raft-proofs`.
    - `CandidatesVoteForSelvesInterface.v`, `VotesCorrectInterface.v`, and
      `CroniesCorrectInterface.v`: statements of properties used by the proof
      `OneLeaderPerTermProof.v`
- `LogMatchingInterface.v`: a statement of Raft's *log matching*
    property. See also `LogMatchingProof.v` in `raft-proofs`
    - `LeaderSublogInterface.v`, `SortedInterface.v`, and `UniqueIndicesInterface.v`: statements
      of properties used by `LogMatchingProof.v`

The file `EndToEndLinearizability.v` in `raft-proofs` uses the proofs of
all proof interfaces to show Raft's *linearizability* property.

The `vard` Key-Value Store
------------------------

`vard` is a simple key-value store implemented using
Verdi. `vard` is specified and verified against Verdi's state-machine
semantics in the `VarD.v` example system distributed with Verdi. When the Raft transformer
is applied, `vard` can be run as a strongly-consistent, fault-tolerant key-value store
along the lines of [`etcd`](https://github.com/coreos/etcd).

If the Raft implementation and its proofs have been compiled, all the files
necessary to run `vard` on real hardware are in `extraction/vard`. It then
suffices to run `make` in that directory to compile the extracted OCaml code, link it
against the Verdi shim and some `vard`-specific serialization/debugging code,
and produce the `vard.native` binary. Alternatively, `make vard-quick` in the
root directory produces the same result, but without compiling the Raft proofs.

Running `make bench-vard` in `extraction/vard` will produce some 
benchmark numbers, which are largely meaningless on
`localhost` (multiple processes writing and fsync-ing to the same disk
and communicating over loopback doesn't accurately model real-world
use cases). Running `make debug` will get you a `tmux` session where
you can play around with a vard cluster in debug mode; look in
`bench/vard.py` for a simple Python `vard` client.

As the name suggests, `vard` is designed to be comparable to the `etcd`
key-value store (although it currently supports many fewer
features). To that end, we include a very simple `etcd` "client" which
can be used for benchmarking. Running `make bench-etcd` will run the
vard benchmarks against `etcd` (although see above for why these results
are not particularly meaningful). See below for instructions to run
both stores on a cluster in order to get a more useful performance
comparison.

Running `vard` on a cluster
---------------------------

`vard` accepts the following command-line options:

```
-me NAME             name for this node
-port PORT           port for client commands
-dbpath DIRECTORY    directory for storing database files
-node NAME,IP:PORT   node in the cluster
-debug               run in debug mode
```

Note that `vard` node names are integers starting from 0.

For example, to run `vard` on a cluster with IP addresses
`192.168.0.1`, `192.168.0.2`, `192.168.0.3`, client (input) port 8000,
and port 9000 for inter-node communication, use the following:

    # on 192.168.0.1
    $ ./vard.native -dbpath /tmp/vard-8000 -port 8000 -me 0 -node 0,192.168.0.1:9000 \
                    -node 1,192.168.0.2:9000 -node 2,192.168.0.3:9000

    # on 192.168.0.2
    $ ./vard.native -dbpath /tmp/vard-8000 -port 8000 -me 1 -node 0,192.168.0.1:9000 \
                    -node 1,192.168.0.2:9000 -node 2,192.168.0.3:9000

    # on 192.168.0.3
    $ ./vard.native -dbpath /tmp/vard-8000 -port 8000 -me 2 -node 0,192.168.0.1:9000 \
                    -node 1,192.168.0.2:9000 -node 2,192.168.0.3:9000

When the cluster is set up, a benchmark can be run as follows:

    # on the client machine
    $ python2 bench/setup.py --service vard --keys 50 \
                             --cluster "192.168.0.1:8000,192.168.0.2:8000,192.168.0.3:8000"
    $ python2 bench/bench.py --service vard --keys 50 \
                             --cluster "192.168.0.1:8000,192.168.0.2:8000,192.168.0.3:8000" \
                             --threads 8 --requests 100


Running `etcd` on a cluster
-------------------------

We can compare `vard`'s numbers to `etcd` running on the same cluster as
follows:

    # on 192.168.0.1
    $ etcd --name=one \
     --listen-client-urls http://192.168.0.1:8000 \
     --advertise-client-urls http://192.168.0.1:8000 \
     --initial-advertise-peer-urls http://192.168.0.1:9000 \
     --listen-peer-urls http://192.168.0.1:9000 \
     --data-dir=/tmp/etcd \
     --initial-cluster "one=http://192.168.0.1:9000,two=http://192.168.0.2:9000,three=http://192.168.0.3:9000"

    # on 192.168.0.2
    $ etcd --name=two \
     --listen-client-urls http://192.168.0.2:8000 \
     --advertise-client-urls http://192.168.0.2:8000 \
     --initial-advertise-peer-urls http://192.168.0.2:9000 \
     --listen-peer-urls http://192.168.0.2:9000 \
     --data-dir=/tmp/etcd \
     --initial-cluster "one=http://192.168.0.1:9000,two=http://192.168.0.2:9000,three=http://192.168.0.3:9000"

    # on 192.168.0.3
    $ etcd --name=three \
     --listen-client-urls http://192.168.0.3:8000 \
     --advertise-client-urls http://192.168.0.3:8000 \
     --initial-advertise-peer-urls http://192.168.0.3:9000 \
     --listen-peer-urls http://192.168.0.3:9000 \
     --data-dir=/tmp/etcd \
     --initial-cluster "one=http://192.168.0.1:9000,two=http://192.168.0.2:9000,three=http://192.168.0.3:9000"

    # on the client machine
    $ python2 bench/setup.py --service etcd --keys 50 \
                             --cluster "192.168.0.1:8000,192.168.0.2:8000,192.168.0.3:8000"
    $ python2 bench/bench.py --service etcd --keys 50 \
                             --cluster "192.168.0.1:8000,192.168.0.2:8000,192.168.0.3:8000" \
                             --threads 8 --requests 100
