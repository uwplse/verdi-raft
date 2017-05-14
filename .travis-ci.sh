set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add coq $COQ_VERSION --yes --verbose
opam pin add coq-mathcomp-ssreflect $SSREFLECT_VERSION --yes --verbose
opam install StructTact verdi --yes --verbose

case $MODE in
  analytics)
    ./script/analytics.sh
    ;;
  vard)
    opam install verdi-runtime --yes --verbose
    ./build.sh vard
    ;;
  vard-test)
    opam install verdi-runtime ounit.2.0.0 --yes --verbose
    ./build.sh vard-test
    ;;
  *)
    ./build.sh $TARGET
    ;;
esac
