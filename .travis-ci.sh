pushd ..
  wget 'http://homes.cs.washington.edu/~jrw12/coq-8.5-build-local.tgz'
  tar xf coq-8.5-build-local.tgz
  export PATH=$PWD/coq-8.5/bin:$PATH

  git clone 'http://github.com/uwplse/StructTact'
  pushd StructTact
    ./build.sh
  popd

  git clone -b verdi-without-raft 'http://github.com/uwplse/verdi' verdi-framework
  pushd verdi-framework
    ./build.sh
  popd
popd

case $MODE in
  analytics)
    ./analytics.sh
    ;;

  *)
      ./build.sh
      ;;
esac
