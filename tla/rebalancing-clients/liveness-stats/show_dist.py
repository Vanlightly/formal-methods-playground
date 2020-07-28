#!/usr/bin/env python

import sys
import re 
import math

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


data = list()
print("AppCount,QueueCount,RandomStart,Behaviours,MinTotal,50thTotal,75thTotal,95thTotal,99thTotal,MaxTotal,MinPerQueue,50thPerQueue,75thPerQueue,95thPerQueue,99thPerQueue,MaxPerQueue")
for key in total_releases.keys():    
    app_count = int(key.split(":")[0])
    queue_count = int(key.split(":")[1])
    total_releases_of_key = total_releases[key]
    data.append((len(total_releases_of_key),app_count,queue_count))


sorted_data = sorted(data, key=lambda tup: tup[0])

for item in sorted_data:
    print(f"Behaviours: {item[0]} Queues: {item[2]} Apps: {item[1]}")
