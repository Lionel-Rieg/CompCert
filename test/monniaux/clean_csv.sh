
source benches.sh

rm -f commands.txt
for bench in $benches; do
  (cd $bench && rm *.csv)
done

rm measures.csv
