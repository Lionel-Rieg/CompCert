#!/bin/bash

for folder in prng mmult sort instr interop; do
  rm -f $folder/*.out
  rm -f $folder/out/*
done
