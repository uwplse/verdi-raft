set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam pin add coq $COQ_VERSION --yes --verbose
opam pin add coq-mathcomp-ssreflect $SSREFLECT_VERSION --yes --verbose
opam install StructTact InfSeqExt verdi-runtime --yes --verbose

pushd ..
  git clone -b coq-8.6 'https://github.com/uwplse/verdi.git'
  pushd verdi
    ./build.sh $TARGET
  popd
popd

case $MODE in
  analytics)
    Verdi_PATH=../verdi ./script/analytics.sh
    ;;
  vard-quick)
    Verdi_PATH=../verdi ./build.sh vard-quick
    ;;
  vard-test)
    opam install ounit.2.0.0 --yes --verbose
    Verdi_PATH=../verdi ./build.sh vard-test
    ;;
  *)
    Verdi_PATH=../verdi ./build.sh $TARGET
    ;;
esac
