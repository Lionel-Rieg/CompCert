#!/usr/bin/python3.5

import numpy as np              # type: ignore
import matplotlib.pyplot as plt # type: ignore
import pandas as pd             # type: ignore
import sys
from typing import *

##
# Reading data
##

if len(sys.argv) != 3:
  raise Exception("Arguments for this script: the csv file, the base name of the output PDF file")
_, csv_file, output_basename = sys.argv

with open(csv_file, "r") as f:
  df = pd.read_csv(csv_file)

benches = df["benches"]

host_measures_cols = [col for col in df if "host" in col]
k1c_measures_cols = [col for col in df if "k1c" in col]

colors = ["forestgreen", "darkorange", "cornflowerblue", "darkorchid", "darksalmon", "dodgerblue", "navy", "gray", "springgreen", "crimson"]

##
# Generating PDF
##

def extract_compiler(env: str) -> str:
  words = env.split()[:-1]
  return " ".join(words)

def extract_compilers(envs: List[str]) -> List[str]:
  compilers = []
  for env in envs:
    compiler = extract_compiler(env)
    if compiler not in compilers:
      compilers.append(compiler)
  return compilers

def subdivide_interv(inf: Any, sup: float, n: int) -> List[float]:
  return [inf + k*(sup-inf)/n for k in range(n)]


# df associates the environment string (e.g. "gcc host") to the cycles
# envs is the list of environments to compare
# The returned value will be a dictionnary associating the compiler (e.g. "gcc") to his relative comparison on the best result
def make_relative_heights(data: Dict[str, List[float]], envs: List[str]) -> Dict[str, List[float]]:
  #n_benches: int = len(data["benches"])
  #cols: Dict[str, List[float]] = {extract_compiler(env):data[env] for env in envs}
  n_benches = len(data["benches"])
  cols = {extract_compiler(env):data[env] for env in envs}

  #ret: Dict[str, List[float]] = {}
  ret = {}
  for compiler in cols:
    ret[compiler] = []

  for i in range(n_benches):
    #maximum: float = max([cols[compiler][i] for compiler in cols])
    maximum = max([cols[compiler][i] for compiler in cols])
    for compiler in cols:
      ret[compiler].append(cols[compiler][i] / float(maximum))

  return ret


def generate_file(f: str, cols: List[str]) -> None:
  ind = np.arange(len(df[cols[0]]))

  width = 0.25  # the width of the bars

  compilers = extract_compilers(cols)
  start_inds = subdivide_interv(ind, ind+2*width, len(compilers))
  inverse_cycles = {key:[1./x if isinstance(x, int) else x for x in list(df[key])] for key in df.columns}
  #heights: Dict[str, List[float]] = make_relative_heights(inverse_cycles, cols)
  heights = make_relative_heights(inverse_cycles, cols)

  fig, ax = plt.subplots()
  rects = []
  for i, compiler in enumerate(compilers):
    rects.append(ax.bar(start_inds[i], heights[compiler], width, color=colors[i], label=compiler))

  # Add some text for labels, title and custom x-axis tick labels, etc.
  ax.set_ylabel('1/cycles (%)')
  ax.set_yticklabels(['{:,.0%}'.format(x) for x in ax.get_yticks()])
  ax.set_title('TITLE')
  ax.set_xticks(ind)
  ax.set_xticklabels(benches)
  ax.legend()

  plt.setp(ax.get_xticklabels(), rotation=30, horizontalalignment='right')
  plt.xticks(size=5)

  plt.savefig(f)

generate_file(output_basename + ".host.pdf", host_measures_cols)
generate_file(output_basename + ".k1c.pdf", k1c_measures_cols)
