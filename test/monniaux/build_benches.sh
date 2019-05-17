
source benches.sh

rm -f commands.txt
for bench in $benches; do
  echo "(cd $bench && make -j5 $1)" >> commands.txt
done

cat commands.txt | xargs -n1 -I{} -P4 bash -c '{}'
