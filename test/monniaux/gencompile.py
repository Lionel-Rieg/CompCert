#!/usr/bin/python3.6

import numpy as np              # type: ignore
import matplotlib.pyplot as plt # type: ignore
import sys
from typing import *

##
# Reading data
##

if len(sys.argv) != 2:
  raise Exception("Only 1 argument should be given to this script: the file with the compile times")
data_file = sys.argv[1]

coords: List[Tuple[int, float]] = []
with open(data_file, "r") as f:
  for line in f:
    nb_inst_s, time_s = line.split(":")
    coords.append((int(nb_inst_s), float(time_s)))

##
# Generating PDF
##

fig, ax = plt.subplots()
x = [coord[0] for coord in coords]
y = [coord[1] for coord in coords]
plt.plot(x, y, "b+")

ax.set_ylabel("Time x1000 (s)")
ax.set_title("Verification time")
ax.set_xlabel("Size of basic blocks")

plt.savefig("compile-times.pdf")


#def generate_file(f: str, cols: List[str]) -> None:
#  ind = np.arange(len(df[cols[0]]))
#
#  width = 0.25  # the width of the bars
#
#  compilers = extract_compilers(cols)
#  start_inds = subdivide_interv(ind, ind+2*width, len(compilers))
#  heights: Dict[str, List[float]] = make_relative_heights(df, cols)
#
#  fig, ax = plt.subplots()
#  rects = []
#  for i, compiler in enumerate(compilers):
#    rects.append(ax.bar(start_inds[i], heights[compiler], width, color=colors[i], label=compiler))
#
#  # Add some text for labels, title and custom x-axis tick labels, etc.
#  ax.set_ylabel('Cycles (%)')
#  ax.set_yticklabels(['{:,.0%}'.format(x) for x in ax.get_yticks()])
#  ax.set_title('TITLE')
#  ax.set_xticks(ind)
#  ax.set_xticklabels(benches)
#  ax.legend()
#
#  plt.setp(ax.get_xticklabels(), rotation=30, horizontalalignment='right')
#  plt.xticks(size=5)
#
#  plt.savefig(f)
#
#generate_file("measures-host.pdf", host_measures_cols)
#generate_file("measures-k1c.pdf", k1c_measures_cols)
