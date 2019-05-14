
source benches.sh

rm -f commands.txt
for bench in $benches; do
  (cd $bench && make clean)
done
