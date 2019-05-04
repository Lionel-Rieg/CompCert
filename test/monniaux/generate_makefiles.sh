#!/usr/bin/bash

for bench in binary_search; do
  ./genmake.py $(cat $bench/make.proto) > $bench/Makefile
done
