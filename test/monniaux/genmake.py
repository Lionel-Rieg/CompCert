#!/usr/bin/python3.4

""" Custom Makefile generator

Generates the Makefiles for the various benches, including extra rules for each different optimization options and/or compilers.

See the source for more info.
"""

from collections import namedtuple
import sys

Optim = namedtuple("Optim", ["short", "full"])
Env = namedtuple("Env", ["compiler", "optimizations", "target"])
Compiler = namedtuple("Compiler", ["short", "full"])

##
# Variables you can change.
##

# Defining the compilers and optimizations

gcc_x86 = Env(compiler = Compiler("gcc", "$(CC)"), optimizations = [Optim("", "$(CFLAGS)")], target = "host")
gcc_k1c = Env(compiler = Compiler("gcc", "$(K1C_CC)"), optimizations = [Optim("", "$(K1C_CFLAGS)"), Optim("o1", "$(K1C_CFLAGS_O1)")], target = "k1c")
ccomp_x86 = Env(compiler = Compiler("ccomp", "$(CCOMP)"), optimizations = [Optim("", "$(CCOMPFLAGS)")], target = "host")
ccomp_k1c = Env(compiler = Compiler("ccomp", "$(K1C_CCOMP)"), optimizations = [Optim("", "$(K1C_CCOMPFLAGS)")], target = "k1c")

environments = [gcc_x86, gcc_k1c, ccomp_x86, ccomp_k1c]

##
# Argument parsing
##
if len(sys.argv) != 2:
  raise Exception("Only 1 argument should be given to this script")
basename = sys.argv[1]

##
# Printing the rules
##

def make_product(env, optim):
  return basename + "." + env.compiler.short + (("." + optim.short) if optim.short != "" else "") + "." + env.target

def make_clock(env, optim):
  return "clock.gcc." + env.target

def print_rule(env, optim):
  print("{product}: {product}.o ../{clock}.o"
        .format(product = make_product(env, optim), clock = make_clock(env, optim)))
  print("	{compiler} {flags} $+ -o $@"
        .format(compiler = env.compiler.full, flags = optim.full))

products = []
for env in environments:
  for optim in env.optimizations:
    products.append(make_product(env, optim) + ".out")

print("""
include ../rules.mk

PRODUCTS?={}

all: $(PRODUCTS)
""".format(" ".join(products)))

for env in environments:
  for optim in env.optimizations:
    print_rule(env, optim)

print("""
clean:
	-rm -f *.o *.s *.k1c

.PHONY: clean
""")
