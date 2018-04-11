# $1: binary file to check
# $2: output check token

elffile="$1"
token="$2"

if [ ! -f $elffile ]; then
	>&2 echo "ERROR: $elffile not found"
	shift; continue
fi

dir="$(dirname $elffile)"
elf="$(basename $elffile)"

exp="$dir/../output/$elf.exp"
out="$dir/../output/$elf.out"
if [ ! -f $exp ]; then
	>&2 echo "ERROR: $exp not found"
	exit
fi

k1-cluster -- $elffile > $out
echo $? >> $out

if ! diff $exp $out; then
	>&2 echo "ERROR: $exp and $out differ"
	exit
fi

echo "PASSED: $elf"
touch $token
#shift
