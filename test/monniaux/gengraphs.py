#!/usr/bin/python3.6

import numpy as np              # type: ignore
import matplotlib.pyplot as plt # type: ignore
import pandas as pd             # type: ignore
import sys
from typing import *

##
# Reading data
##

if len(sys.argv) != 2:
  raise Exception("Only 1 argument should be given to this script: the make.proto file")
csv_file = sys.argv[1]

with open(csv_file, "r") as f:
  df = pd.read_csv(csv_file)

benches = df["benches"]
print(benches[0])

host_measures_cols = [col for col in df if "host" in col]
k1c_measures_cols = [col for col in df if "k1c" in col]

colors = ["forestgreen", "darkorange", "cornflowerblue", "darkorchid", "darksalmon", "dodgerblue", "navy", "gray", "springgreen", "crimson"]

##
# Generating PDF
##

def extract_envs(keys: List[str]) -> List[str]:
  envs = []
  for key in keys:
    words = key.split()[:-1]
    envs.append(" ".join(words))
  return envs


def subdivide_interv(inf: float, sup: float, n: int) -> List[float]:
  return [inf + k*(sup-inf)/n for k in range(n)]


def generate_file(f: str, cols: List[str]) -> None:
  ind = np.arange(len(df[cols[0]]))

  width = 0.35  # the width of the bars

  envs = extract_envs(cols)
  start_inds = subdivide_interv(ind, ind+width, len(envs))

  fig, ax = plt.subplots()
  rects = []
  for i, env in enumerate(envs):
    for col in cols:
      if env in col:
        break
    rects.append(ax.bar(start_inds[i], df[col], width, color=colors[i], label=env))

  # Add some text for labels, title and custom x-axis tick labels, etc.
  ax.set_ylabel('Cycles')
  ax.set_title('TITLE')
  ax.set_xticks(ind)
  ax.set_xticklabels(benches)
  ax.legend()

  def autolabel(rects: List[Any], xpos='center') -> None:
      """
      Attach a text label above each bar in *rects*, displaying its height.

      *xpos* indicates which side to place the text w.r.t. the center of
      the bar. It can be one of the following {'center', 'right', 'left'}.
      """

      xpos = xpos.lower()  # normalize the case of the parameter
      ha = {'center': 'center', 'right': 'left', 'left': 'right'}
      offset = {'center': 0.5, 'right': 0.57, 'left': 0.43}  # x_txt = x + w*off

      for rect in rects:
          height = rect.get_height()
          ax.text(rect.get_x() + rect.get_width()*offset[xpos], 1.01*height,
                  '{}'.format(height), ha=ha[xpos], va='bottom')

  for rect in rects:
    autolabel(rect)

  plt.savefig(f)

generate_file("measures-host.pdf", host_measures_cols)
#generate_file("measures-k1c.pdf", k1c_measures_cols)
