set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add coq $COQ_VERSION --yes --verbose

case $MODE in
  proofalytics)
    opam pin add verdi-raft-proofalytics . --yes --verbose
    ;;
  vard)
    opam pin add vard . --yes --verbose
    ;;
  vard-test)
    OPAMBUILDTEST=1 opam pin add vard . --yes --verbose
    ;;
  *)
    opam pin add verdi-raft . --yes --verbose
    ;;
esac
