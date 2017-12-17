set -ev

if [ -e "/home/travis/.opam/config" ]; then
    eval $(opam config env)
else
    opam init --compiler=${COMPILER} --yes --no-setup
    eval $(opam config env)
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
fi

opam update --yes --verbose

opam pin add coq ${COQ_VERSION} --yes --verbose

opam upgrade --yes --verbose

case ${MODE} in
  proofalytics)
    opam pin add verdi-raft . --yes --verbose --no-action
    opam install verdi-raft --yes --verbose --deps-only
    ./configure
    make proofalytics &
    # Output to the screen every 9 minutes to prevent a travis timeout
    export PID=$!
    while [[ `ps -p $PID | tail -n +2` ]]; do
	echo 'proofalyzing...'
	sleep 240
    done
    opam pin remove verdi-raft --yes --verbose
    ;;
  checkproofs)
    opam pin add verdi-raft-checkproofs . --yes --verbose
    opam remove verdi-raft-checkproofs --yes --verbose
    opam pin remove verdi-raft-checkproofs --yes --verbose
    ;;
  vard)
    opam pin add vard . --yes --verbose
    opam remove vard --yes --verbose
    opam pin remove vard --yes --verbose
    ;;
  vard-serialized)
    opam pin add vard-serialized . --yes --verbose
    opam remove vard-serialized --yes --verbose
    opam pin remove vard-serialized --yes --verbose
    ;;
  vard-log)
    opam pin add vard-log . --yes --verbose
    opam remove vard-log --yes --verbose
    opam pin remove vard-log --yes --verbose
    ;;
  vard-serialized-log)
    opam pin add vard-serialized-log . --yes --verbose
    opam remove vard-serialized-log --yes --verbose
    opam pin remove vard-serialized-log --yes --verbose
    ;;
  *)
    opam pin add verdi-raft . --yes --verbose
    opam remove verdi-raft --yes --verbose
    opam pin remove verdi-raft --yes --verbose
    ;;
esac
