#!/usr/bin/env python

import sys
import re 
import math

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
            

output_file = sys.argv[1]
random_start = output_file.startswith("random")

fd = open(output_file, 'r') 
lines = fd.readlines() 

total_releases = dict()
per_queue_releases = dict()

for line in lines:
    total_match = re.match( r'^"total_releases,(\d*),(\d*),(\d*)".*', line, re.M|re.I)
    per_queue_match = re.match( r'^"per_queue_releases,(\d*),(\d*),(\d*)".*', line, re.M|re.I)

    if total_match:
        add_metric(total_releases, total_match)
    elif per_queue_match:
        add_metric(per_queue_releases, per_queue_match)

keys = list(total_releases.keys())
keys.sort()

print("AppCount,QueueCount,RandomStart,Behaviours,MinTotal,50thTotal,75thTotal,95thTotal,99thTotal,MaxTotal,MinPerQueue,50thPerQueue,75thPerQueue,95thPerQueue,99thPerQueue,MaxPerQueue")
for key in keys:    
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
    per_queue_releases_99th = percentile(per_queue_releases_of_key, 0.99)
    per_queue_releases_min = min(per_queue_releases_of_key)
    per_queue_releases_max = max(per_queue_releases_of_key)

    print(f"{app_count},{queue_count},{random_start},{len(total_releases_of_key)},{total_releases_min},{total_releases_50th},{total_releases_75th},{total_releases_95th},{total_releases_99th},{total_releases_max},{per_queue_releases_min},{per_queue_releases_50th},{per_queue_releases_75th},{per_queue_releases_95th},{per_queue_releases_99th},{per_queue_releases_max}")
