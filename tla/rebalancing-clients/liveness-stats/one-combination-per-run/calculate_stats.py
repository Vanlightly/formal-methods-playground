#!/usr/bin/env python

import argparse
import sys
import re 
import math
from os import listdir
from os.path import isfile, join

def percentile(N, percent, key=lambda x:x):
    """
    Find the percentile of a list of values.

    @parameter N - is a list of values. Note N MUST BE already sorted.
    @parameter percent - a float value from 0.0 to 1.0.
    @parameter key - optional key function to compute value from each element of N.

    @return - the percentile of the values
    """
    if not N:
        return None
    k = (len(N)-1) * percent
    f = math.floor(k)
    c = math.ceil(k)
    if f == c:
        return key(N[int(k)])
    d0 = key(N[int(f)]) * (c-k)
    d1 = key(N[int(c)]) * (k-f)
    return d0+d1

def add_metric(metric_dict, match):
    value = int(match.group(1))
    app_count = int(match.group(2))
    queue_count = int(match.group(3))
    key = f"{app_count}:{queue_count}"

    if key not in total_releases:
        metric_dict[key] = list()
    
    metric_dict[key].append(value)
            
parser=argparse.ArgumentParser()

parser.add_argument('--results_dir', help='The directory which contains the tlc output files')

args=parser.parse_args()

total_releases = dict()
per_queue_releases = dict()
per_app_releases = dict()
per_app_check_cycles = dict()

result_files = [join(args.results_dir, f) for f in listdir(args.results_dir) if isfile(join(args.results_dir, f))]

for result_file in result_files:
    fd = open(result_file, 'r') 
    lines = fd.readlines() 

    for line in lines:
        total_match = re.match( r'^"total_releases,(\d*),(\d*),(\d*)".*', line, re.M|re.I)
        per_queue_match = re.match( r'^"per_queue_releases,(\d*),(\d*),(\d*)".*', line, re.M|re.I)
        per_app_match = re.match( r'^"per_app_releases,(\d*),(\d*),(\d*)".*', line, re.M|re.I)
        per_app_check_cycles_match = re.match( r'^"per_app_checks,(\d*),(\d*),(\d*)".*', line, re.M|re.I)

        if total_match:
            add_metric(total_releases, total_match)
        elif per_queue_match:
            add_metric(per_queue_releases, per_queue_match)
        elif per_app_match:
            add_metric(per_app_releases, per_app_match)
        elif per_app_check_cycles_match:
            add_metric(per_app_check_cycles, per_app_check_cycles_match)
        

print("AppCount,QueueCount,Behaviours,TotalRel min,TotalRel p50,TotalRel p75,TotalRel p95,TotalRel p99,TotalRel max,RelPerQueue min,RelPerQueue p50,RelPerQueue p75,RelPerQueue p95,RelPerQueue p99,RelPerQueue max,RelPerApp min,RelPerApp p50,RelPerApp p75,RelPerApp p95,RelPerApp p99,RelPerApp max,ChecksPerApp min,ChecksPerApp p50,ChecksPerApp p75,ChecksPerApp p95,ChecksPerApp p99,ChecksPerApp max")
for key in total_releases.keys():    
    app_count = int(key.split(":")[0])
    queue_count = int(key.split(":")[1])
    
    total_releases_of_key = total_releases[key]
    total_releases_of_key.sort()
    total_releases_50th = percentile(total_releases_of_key, 0.5)
    total_releases_75th = percentile(total_releases_of_key, 0.75)
    total_releases_95th = percentile(total_releases_of_key, 0.95)
    total_releases_99th = percentile(total_releases_of_key, 0.99)
    total_releases_min = min(total_releases_of_key)
    total_releases_max = max(total_releases_of_key)

    per_queue_releases_of_key = per_queue_releases[key]
    per_queue_releases_of_key.sort()
    per_queue_releases_50th = percentile(per_queue_releases_of_key, 0.5)
    per_queue_releases_75th = percentile(per_queue_releases_of_key, 0.75)
    per_queue_releases_95th = percentile(per_queue_releases_of_key, 0.95)
    per_queue_releases_99th = perentile(per_app_releases_of_key, 0.5)
    per_app_releases_75th = percentile(per_app_releases_of_key, 0.75)
    per_app_releases_95th = percentile(per_app_releases_of_key, 0.95)
    per_app_releases_99th = percentile(per_app_releases_of_key, 0.99)
    per_app_releases_min = min(per_app_releases_of_key)
    per_app_releases_max = max(per_app_releases_of_key)

    per_app_check_cycles_of_key = per_queue_releases[key]
    per_app_check_cycles_of_key.sort()
    per_app_check_cycles_50th = percentile(per_app_check_cycles_of_key, 0.5)
    per_app_check_cycles_75th = percentile(per_app_check_cycles_of_key, 0.75)
    per_app_check_cycles_95th = percentile(per_app_check_cycles_of_key, 0.95)
    per_app_check_cycles_99th = percentile(per_app_check_cycles_of_key, 0.99)
    per_app_check_cycles_min = min(per_app_check_cycles_of_key)
    per_app_check_cycles_max = max(per_app_check_cycles_of_key)

    print(f"{app_count},{queue_count},{len(total_releases_of_key)},{total_releases_min},{total_releases_50th},{total_releases_75th},{total_releases_95th},{total_releases_99th},{total_releases_max},{per_queue_releases_min},{per_queue_releases_50th},{per_queue_releases_75th},{per_queue_releases_95th},{per_queue_releases_99th},{per_queue_releases_max},{per_app_releases_min},{per_app_releases_50th},{per_app_releases_75th},{per_app_releases_95th},{per_app_releases_99th},{per_app_releases_max},{per_app_check_cycles_min},{per_app_check_cycles_50th},{per_app_check_cycles_75th},{per_app_check_cycles_95th},{per_app_check_cycles_99th},{per_app_check_cycles_max}")
