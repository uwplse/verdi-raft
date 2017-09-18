set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add coq $COQ_VERSION --yes --verbose

pushd ..
  git clone -b channel https://github.com/uwplse/cheerios.git
  pushd cheerios
    opam pin add cheerios . --yes --verbose
  popd
  git clone -b disk https://github.com/uwplse/verdi.git
  pushd verdi
    opam pin add verdi . --yes --verbose
  popd
popd

case $MODE in
  proofalytics)
    opam pin add verdi-raft-proofalytics . --yes --verbose
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
  *)
    opam pin add verdi-raft . --yes --verbose
    ;;
esac
