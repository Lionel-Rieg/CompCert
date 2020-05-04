#!/bin/bash
# Tests the execution of the binaries produced by CompCert, by simulation

cores=$(grep -c ^processor /proc/cpuinfo)

source do_test.sh

do_test check $cores
