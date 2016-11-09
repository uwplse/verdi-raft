opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq coq-mathcomp-ssreflect ounit --yes

pushd ..
  git clone 'http://github.com/uwplse/StructTact'
  pushd StructTact
    ./build.sh
  popd

  git clone 'http://github.com/palmskog/InfSeqExt'
  pushd InfSeqExt
    ./build.sh
  popd

  git clone 'http://github.com/uwplse/verdi'
  pushd verdi
    ./build.sh
  popd
popd

case $MODE in
  analytics)
    ./script/analytics.sh
    ;;
  vard-quick)
    ./script/vard-quick.sh
    ;;
  vard-test)
    ./script/vard-test.sh
    ;;
  *)
    ./build.sh
    ;;
esac
