# $1: c file to examine
# $2: write file

cfile="$1"
writefile="$2"

dirwritefile=$(dirname $writefile)
asmdir=$dirwritefile/../asm/gcc

if [ ! -f $cfile ]; then
	>&2 echo "ERROR: $cfile not found"
	shift; continue
fi

mkdir -p $dirwritefile
mkdir -p $asmdir

tmpbin=/tmp/k1-$(basename $1)-bin 
k1-gcc -O0 $1 -S -o $asmdir/$(basename $1).s
k1-gcc -O0 $1 -o $tmpbin
(k1-cluster -- $tmpbin; echo $? > $2)
