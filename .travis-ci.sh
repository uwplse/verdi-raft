pushd ..
  wget 'http://homes.cs.washington.edu/~jrw12/coq-8.5-build-local.tgz'
  tar xf coq-8.5-build-local.tgz
  export PATH=$PWD/coq-8.5/bin:$PATH

  opam init --yes --no-setup
  eval $(opam config env)
  opam install ounit --yes

  git clone 'http://github.com/uwplse/StructTact'
  pushd StructTact
    ./build.sh
  popd

  git clone 'http://github.com/palmskog/InfSeqExt'
  pushd InfSeqExt
    ./build.sh
  popd

  git clone 'http://github.com/uwplse/verdi' verdi
  pushd verdi
    ./build.sh
  popd
popd

case $MODE in
  analytics)
    ./analytics.sh
    ;;
  vard-quick)
    ./vard-quick.sh
    ;;
  vard-test)
    ./vard-test.sh
    ;;
  *)
    ./build.sh
    ;;
esac
