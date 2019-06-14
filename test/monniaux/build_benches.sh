TMPFILE=/tmp/1513times.txt

source benches.sh

rm -f commands.txt
rm -f $TMPFILE
for bench in $benches; do
  #echo "(cd $bench && make -j5 $1)" >> commands.txt
  (cd $bench && make -j20 $1) | grep -P "\d+: \d+\.\d+" >> $TMPFILE
done
cat $TMPFILE | sort -n -k 1 > compile_times.txt

#cat commands.txt | xargs -n1 -I{} -P4 bash -c '{}'
