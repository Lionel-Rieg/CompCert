#!/usr/bin/python3.5

import numpy as np              # type: ignore
import matplotlib.pyplot as plt # type: ignore
import sys
from typing import *

##
# Reading data
##

if len(sys.argv) != 4:
  raise Exception("Three arguments are expected: the verifier times, the oracle times, and the output PDF")
_, verifier_file, oracle_file, output_file = sys.argv

def get_coords(filename: str) -> List[Tuple[int, float]]:
  coords = []
  with open(filename, "r") as f:
    for line in f:
      nb_inst_s, time_s = line.split(":")
      coords.append((int(nb_inst_s), float(time_s)))
  return coords

verifier_coords = get_coords(verifier_file)
oracle_coords = get_coords(oracle_file)

##
# Generating PDF
##

fig, ax = plt.subplots()

def do_plot(coords: List[Tuple[int, float]], style: str, label: str, color: str):
  x = [coord[0] for coord in coords]
  y = [coord[1] for coord in coords]
  plt.plot(x, y, style, label=label, color=color)

plt.xscale("log")
plt.yscale("log")
do_plot(verifier_coords, "+", "Verifier", "gray")
do_plot(oracle_coords, "+", "Oracle", "black")

ax.set_ylabel("Time x1000 (s)")
ax.set_xlabel("Size of basic blocks")
ax.legend()

plt.savefig(output_file)
