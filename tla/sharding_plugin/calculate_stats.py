#!/usr/bin/env python

import argparse
import sys
import re 
import math
from os import listdir
from os.path import isfile, join

parser=argparse.ArgumentParser()

parser.add_argument('--results_dir', help='The directory which contains the tlc output files')

args=parser.parse_args()

result_files = [join(args.results_dir, f) for f in listdir(args.results_dir) if isfile(join(args.results_dir, f))]

print("NodeCount,TotalClients,QueueClients,PercentOk")

for result_file in result_files:
    if not result_file.endswith(".log"):
        continue

    fd = open(result_file, 'r') 
    lines = fd.readlines() 

    total_ok = 0
    total_bad = 0

    read_config = False

    for line in lines:
        
        if not read_config:
            if "CONFIG," in line:
                read_config = True
                match = re.match( r'^"CONFIG,(\d*),(\d*),(\d*)".*', line, re.M|re.I)

                if match:
                    nodes = int(match.group(1))
                    total_clients = int(match.group(2))
                    queue_clients = int(match.group(3))
                else:
                    print(line)
        else:
            is_good = line.startswith("\"RESULT,GOOD")
            is_bad = line.startswith("\"RESULT,BAD")
            if is_good:
                total_ok += 1
            elif is_bad:
                total_bad += 1

    fd.close()

    if (total_ok + total_bad) > 0:
        percent_ok = float(total_ok) / float(total_ok + total_bad)
        print(f"{nodes},{total_clients},{queue_clients},{percent_ok}")
    