#!/bin/python3

import argparse

parser = argparse.ArgumentParser(description='Print table of running times.')
parser.add_argument('file', type=str, help='filename containing timing information')

args = parser.parse_args()

with open(args.file) as f:
  stats = list()
  lines = f.readlines()
  alloy_time_line = lines[-2]
  final_time_line = lines[-1]
  try:
    alloy_time = alloy_time_line.split(" ")[4].split("\t")[0]
    final_time = final_time_line.split(" ")[-3].split("\t")[-1]
    print(f"Alloy Time: {alloy_time} | Final Time: {final_time}")
  except:
    print("N/A")

