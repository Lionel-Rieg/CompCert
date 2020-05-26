#!/usr/bin/python2.7

import argparse as ap
import sys

parser = ap.ArgumentParser()
parser.add_argument("file1", help="First file to compare")
parser.add_argument("file2", help="Second file to compare")
parser.add_argument("-reltol", help="Relative error")
parser.add_argument("-abstol", help="Absolute error")
parser.add_argument("-s", help="Silent output", action="store_true")
args = parser.parse_args()

reltol = float(args.reltol) if args.reltol else None
abstol = float(args.abstol) if args.abstol else None
silent = args.s

if silent:
    sys.stdout = open("/dev/null", "w")

import re
from math import fabs

def floatcmp(f1, f2):
    if abstol:
        if fabs(f1 - f2) > abstol:
            return False
    if reltol:
        if f2 != 0. and fabs((f1 - f2) / f2) > reltol:
            return False
    return True

class Parsed(list):
    def __eq__(self, other):
        if len(self) != len(other):
            return False
        comps = zip(self, other)
        for comp in comps:
            if all(isinstance(compElt, str) for compElt in comp):
                if comp[0] != comp[1]:
                    return False
            elif all (isinstance(compElt, float) for compElt in comp):
                if not floatcmp(comp[0], comp[1]):
                    return False
            else:
                return False
        return True
    
    def __ne__(self, other):
        return not self.__eq__(other)

parseLine = re.compile(r"\s*(\S+)")
def readline(line):
    words = parseLine.findall(line)
    parsed = Parsed([])
    for word in words:
        try:
            parse = float(word)
            parsed.append(parse)
        except ValueError:
            parsed.append(word)
    return parsed

def readfile(filename):
    L = []
    try:
        with open(filename) as f:
            for line in f:
                L.append(readline(line))
    except IOError:
        print "Unable to read {}".format(filename)
        sys.exit(2)
    return L

L1 = readfile(args.file1)
L2 = readfile(args.file2)

if len(L1) != len(L2):
    print "The files have different amount of lines"
    print "\t{}: {} lines".format(args.file1, len(L1))
    print "\t{}: {} lines".format(args.file2, len(L2))
    sys.exit(1)

cmpL = zip(L1, L2)
for i, cmpElt in enumerate(cmpL):
    if cmpElt[0] != cmpElt[1]:
        print "The files differ at line {}".format(i)
        print "\t{}: {}".format(args.file1, cmpElt[0])
        print "\t{}: {}".format(args.file2, cmpElt[1])
        sys.exit(1)

print "Comparison succeeded"
sys.exit(0)
