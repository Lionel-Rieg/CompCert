#!/usr/bin/bash

TMPFILE=/tmp/1513times.txt

source benches.sh

rm -f commands.txt
rm -f $TMPFILE
for bench in $benches; do
  if [ "$1" == "" ]; then 
    (cd $bench && make -j20)
  else
    (cd $bench && make -j20) | grep -P "\d+: \d+\.\d+" >> $TMPFILE
  fi
done

if [ "$1" != "" ]; then
  cat $TMPFILE | sort -n -k 1 > $1
fi

