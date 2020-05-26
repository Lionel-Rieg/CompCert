#!/bin/bash

printer=../../kvx/TargetPrinter.ml
asmdir=instr/asm/
to_cover_raw=/tmp/to_cover_raw
to_cover=/tmp/to_cover
covered_raw=/tmp/covered_raw
covered=/tmp/covered

# Stop at any error
set -e
# Pipes do not mask errors
set -o pipefail

sed -n "s/^.*fprintf\s\+oc\s*\"\s*\([a-z][^[:space:]]*\)\s.*/\1/p" $printer > $to_cover_raw
python2.7 coverage_helper.py $to_cover_raw | sort -u > $to_cover

rm -f $covered_raw
for asm in $(ls $asmdir/*.ccomp.s); do
  grep -v ":" $asm | sed -n "s/^\s*\([a-z][a-z0-9.]*\).*/\1/p" | sort -u >> $covered_raw
done
python2.7 coverage_helper.py $covered_raw | sort -u > $covered

vimdiff $to_cover $covered
