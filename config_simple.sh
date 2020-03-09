arch=$1
shift
version=`git rev-parse --short HEAD`
branch=`git rev-parse --abbrev-ref HEAD`
date=`date -I`
./configure --prefix /opt/CompCert/${branch}/${date}_${version}/$arch "$@" $arch
