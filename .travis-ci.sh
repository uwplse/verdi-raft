#!/usr/bin/env bash

set -ev

export MODE=$1
export OPAMBUILDTEST=$2

opam update

case ${MODE} in
  proofalytics)
    opam pin add verdi-raft . --yes --verbose --no-action
    opam install verdi-raft --yes --verbose --deps-only
    ./configure
    make proofalytics &
    # Output to the screen every few minutes to prevent a travis timeout
    export PID=$!
    while [[ `ps -p $PID | tail -n +2` ]]; do
	echo 'proofalyzing...'
	sleep 240
    done
    ;;
  checkproofs)
    opam pin add verdi-raft-checkproofs . --yes --verbose
    ;;
  vard)
    opam pin add vard . --yes --verbose
    ;;
  vard-serialized)
    opam pin add vard-serialized . --yes --verbose
    ;;
  vard-log)
    opam pin add vard-log . --yes --verbose
    ;;
  vard-serialized-log)
    opam pin add vard-serialized-log . --yes --verbose
    ;;
  *)
    opam pin add verdi-raft . --yes --verbose
    ;;
esac
