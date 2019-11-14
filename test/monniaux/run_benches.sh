
source benches.sh

rm -f commands.txt
for bench in $benches; do
  echo "(cd $bench && echo \"Running $bench..\" &&\
    make -j4 run > /dev/null && echo \"$bench DONE\")" >> commands.txt
done

cat commands.txt | xargs -n1 -I{} -P6 bash -c '{}'

##
# Gather all the CSV files
##

benches_csv=""
for bench in $benches; do
  if [ -f $bench/measures.csv ]; then
    benches_csv="$benches_csv $bench/measures.csv"
  fi
done

nawk 'FNR==1 && NR!=1{next;}{print}' $benches_csv > $1
echo "$1 done"
