opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.$COQ_VERSION coq-mathcomp-ssreflect.$SSREFLECT_VERSION ounit.2.0.0 uuidm.0.9.6 --yes --verbose

pushd ..
  git clone 'https://github.com/uwplse/StructTact.git'
  pushd StructTact
    ./build.sh $TARGET
  popd

  git clone 'https://github.com/DistributedComponents/InfSeqExt.git'
  pushd InfSeqExt
    ./build.sh $TARGET
  popd

  git clone -b coq-8.6 'https://github.com/uwplse/verdi.git'
  pushd verdi
    ./build.sh $TARGET
  popd
popd

case $MODE in
  analytics)
    ./script/analytics.sh
    ;;
  vard-quick)
    ./build.sh vard-quick
    ;;
  vard-test)
    ./build.sh vard-test
    ;;
  *)
    ./build.sh $TARGET
    ;;
esac
