#!/usr/bin/env bash

source benches.sh

for bench in $benches; do
  ./genmake.py $bench/make.proto > $bench/Makefile
done

