
source benches.sh

rm -f commands.txt
for bench in $benches; do
  #echo "(cd $bench && make -j5 $1)" >> commands.txt
  (cd $bench && make -j20 $1)
done

#cat commands.txt | xargs -n1 -I{} -P4 bash -c '{}'
