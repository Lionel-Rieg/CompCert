
source benches.sh

blue="\e[34m"
default="\e[39m"

rm -f commands.txt
for bench in $benches; do
  echo -e "${blue}Cleaning $bench..${default}"
  (cd $bench && make -s clean)
done
rm -f *.o
