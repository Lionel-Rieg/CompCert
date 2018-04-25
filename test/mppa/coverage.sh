asmdir=$1
to_cover_raw=/tmp/to_cover_raw
to_cover=/tmp/to_cover
covered_raw=/tmp/covered_raw
covered=/tmp/covered

sed -n "s/^.*fprintf oc \"	\(.*\)	.*/\1/p" ../../mppa_k1c/TargetPrinter.ml > $to_cover_raw
sed -n "s/^.*fprintf oc \"	\(.*\)\\n.*/\1/p" ../../mppa_k1c/TargetPrinter.ml >> $to_cover_raw
python2.7 coverage_helper.py $to_cover_raw > $to_cover

rm -f $covered_raw
for asm in $(ls $asmdir/*.s); do
    bash asm_coverage/asm-coverage.sh $asm >> $covered_raw
done
python2.7 coverage_helper.py $covered_raw > $covered

vimdiff $to_cover $covered
