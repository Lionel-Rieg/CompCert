#!/usr/bin/env bash

TMPFILE=/tmp/1513times.txt

cores=$(grep -c ^processor /proc/cpuinfo)
source benches.sh

default="\e[39m"
magenta="\e[35m"
red="\e[31m"

rm -f commands.txt
rm -f $TMPFILE
for bench in $benches; do
  echo -e "${magenta}Building $bench..${default}"
  if [ "$1" == "" ]; then 
    (cd $bench && make -s -j$cores > /dev/null &> /dev/null) || { echo -e "${red}Build failed" && break; }
  else
    (cd $bench && make -j$cores) | grep -P "\d+: \d+\.\d+" >> $TMPFILE
  fi
done

if [ "$1" != "" ]; then
  cat $TMPFILE | sort -n -k 1 > $1
fi

