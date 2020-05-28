#!/bin/bash
#
# Replace an HTML comment "<!--@DATE@-->" by the current date
# in the file given by $1 (with $2 as prefix and $3 as suffix)
#
# Result on standard output

sed -e "s/<!--@DATE@-->/$2$(date +'%F')$3/g" $1
