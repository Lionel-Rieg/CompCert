arch=$1
shift
version=`git rev-parse --short HEAD`
branch=`git rev-parse --abbrev-ref HEAD`
date=`date -I`

if test "x$CCOMP_INSTALL_PREFIX" = "x" ;
then CCOMP_INSTALL_PREFIX=/opt/CompCert ;
fi

./configure --prefix ${CCOMP_INSTALL_PREFIX}/${branch}/${date}_${version}/$arch "$@" $arch
