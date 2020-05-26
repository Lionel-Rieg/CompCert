#!/bin/bash
# Tests the validity of the tests, in simulator

cores=$(grep -c ^processor /proc/cpuinfo)

source do_test.sh

do_test test $cores
