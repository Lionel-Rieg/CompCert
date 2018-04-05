
while [ $# -gt 0 ]; do
	elffile="$1"
	
	if [ ! -f $elffile ]; then
		>&2 echo "ERROR: $elffile not found"
		shift; continue
	fi

	dir="$(dirname $elffile)"
	elf="$(basename $elffile)"
	exp="$dir/output/$elf.exp"
	out="$dir/output/$elf.out"
	if [ ! -f $exp ]; then
		>&2 echo "ERROR: $exp not found"
		shift; continue
	fi

	k1-cluster -- $elffile > $out
	echo $? >> $out

	if ! diff $exp $out; then
		>&2 echo "ERROR: $exp and $out differ"
		shift; continue
	fi

	echo "PASSED: $elf"
	shift
done
