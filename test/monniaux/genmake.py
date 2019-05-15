#!/usr/bin/python3.4

""" Custom Makefile generator

Generates the Makefiles for the various benches, including extra rules for each different optimization options and/or compilers.

See the source for more info.
"""

from collections import namedtuple
import sys
import yaml

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
  raise Exception("Only 1 argument should be given to this script: the make.proto file")
yaml_file = sys.argv[1]

with open(yaml_file, "r") as f:
  settings = yaml.load(f.read())

basename = settings["target"]
objdeps = settings["objdeps"] if "objdeps" in settings else []
intro = settings["intro"] if "intro" in settings else ""
sources = settings["sources"] if "sources" in settings else None
measures = settings["measures"] if "measures" in settings else []

if sources:
  intro += "\nsrc=" + sources

for objdep in objdeps:
  if objdep["compiler"] not in ("gcc", "ccomp", "both"):
    raise Exception('Invalid compiler specified in make.proto:objdeps, should be either "gcc" or "ccomp" or "both"')

##
# Printing the rules
##

def make_product(env, optim):
  return basename + "." + env.compiler.short + (("." + optim.short) if optim.short != "" else "") + "." + env.target

def make_obj(name, env, compiler_short):
  return name + "." + compiler_short + "." + env.target + ".o"

def make_clock(env, optim):
  return "clock.gcc." + env.target

def make_sources(env, optim):
  if sources:
    return "$(src:.c=." + env.compiler.short + (("." + optim.short) if optim.short != "" else "") + "." + env.target + ".o)"
  else:
    return "{product}.o".format(product = make_product(env, optim))

def print_rule(env, optim):
  print("{product}: {sources} ../{clock}.o "
        .format(product = make_product(env, optim),
          sources = make_sources(env, optim), clock = make_clock(env, optim))
          + " ".join([make_obj(objdep["name"], env, (objdep["compiler"] if objdep["compiler"] != "both" else env.compiler.short)) for objdep in objdeps]))
  print("	{compiler} {flags} $+ -o $@"
        .format(compiler = env.compiler.full, flags = optim.full))

def make_env_list(envs):
  return ",".join([(env.compiler.short + ((" " + optim.short) if optim.short != "" else "") + " " + env.target)
                    for env in environments
                    for optim in env.optimizations])

def print_measure_rule(environments, measures):
  print("measures.csv: $(PRODUCTS_OUT)")
  print('	echo ", {}" > $@'.format(make_env_list(environments)))
  for measure in measures:
    print('	echo "{name} {measure}"'.format(name=basename, measure=measure), end="")
    for env in environments:
      for optim in env.optimizations:
        print(", $$(grep '{measure}' {outfile} | cut -d':' -f2)".format(
              measure=measure, outfile=make_product(env, optim) + ".out"), end="")
    print('>> $@')

products = []
for env in environments:
  for optim in env.optimizations:
    products.append(make_product(env, optim))

print("""
include ../rules.mk

{intro}

PRODUCTS?={prod}
PRODUCTS_OUT=$(addsuffix .out,$(PRODUCTS))

all: $(PRODUCTS)

.PHONY:
exec: measures.csv

""".format(intro=intro, prod=" ".join(products)))

for env in environments:
  for optim in env.optimizations:
    print_rule(env, optim)

print_measure_rule(environments, measures)


print("""
.PHONY:
clean:
	rm -f *.o *.s *.k1c *.csv
""")
