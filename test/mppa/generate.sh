# $1: c file to examine
# $2: write file

cfile="$1"
writefile="$2"

if [ ! -f $cfile ]; then
	>&2 echo "ERROR: $cfile not found"
	shift; continue
fi

mkdir -p $(dirname $writefile)

#sed -n "s/^.*\/\*\s*RETURN VALUE:\s*\([0-9]*\)\s*\*\//\1/p" $1 > $2
tmpbin=/tmp/k1-$(basename $1)-bin 
k1-gcc -O0 $1 -o $tmpbin
(k1-cluster -- $tmpbin; echo $? > $2)
