#!/bin/env python

import argparse, sys, os, subprocess
from pathlib import Path
import time

def generate_config(cfg_template_file, queue_count, app_count):
    # create a temporary cfg file with the desired queues and apps
    template_file = open(cfg_template_file, 'r') 
    template_file = template_file.readlines() 

    cfg_lines = list()
    for line in template_file: 
        if "[APPLICATIONS_PLACEHOLDER]" in line:
            app_set = ""
            for a in range(1, app_count+1):
                app_set = app_set + str(a)
                if a < app_count:
                    app_set = app_set + ","
                
            new_line = line.replace("[APPLICATIONS_PLACEHOLDER]", app_set)
            cfg_lines.append(new_line)
        elif "[QUEUES_PLACEHOLDER]" in line:
            queue_set = ""
            for q in range(1, queue_count+1):
                queue_set = queue_set + str(q)
                if q < queue_count:
                    queue_set = queue_set + ","

            new_line = line.replace("[QUEUES_PLACEHOLDER]", queue_set)
            cfg_lines.append(new_line)
        else:
            cfg_lines.append(line)

    new_cfg_file = f"spec.cfg"
    new_cfg_fd = open(new_cfg_file, 'w') 
    new_cfg_fd.writelines(cfg_lines)
    new_cfg_fd.close()

parser=argparse.ArgumentParser()

parser.add_argument('--spec', help='The TLA+ specification to run')
parser.add_argument('--config', help='The cfg file')
parser.add_argument('--script', help='The simulation script to run')
parser.add_argument('--behaviours', help='The number of behaviours to gather stats for per queue/app combination')
parser.add_argument('--queues', help='The maximum number of queues')
parser.add_argument('--apps', help='The maximum number of apps - only used when not using: all_perms true')
parser.add_argument('--app_ratio', help='The maximum number of apps as a ratio of queues e.g. 1.5 will create 1.5 as many apps as queues')
parser.add_argument('--output_dir', help='The output directory where tlc output is saved to')
parser.add_argument('--all_perms', help='true will generate all permuations of app and queue count')
parser.add_argument('--workers', help='The number of TLC workers')


args=parser.parse_args()


Path(f"results/{args.output_dir}").mkdir(parents=True, exist_ok=True)

print(f"Running a simulation for up to {args.behaviours} behaviours")
if args.all_perms.upper() == "TRUE":

    max_queues = int(args.queues)
    app_ratio = float(args.app_ratio)

    for queue_count in range(1, max_queues + 1):
        max_apps = int(queue_count*app_ratio)
        for app_count in range(1, max_apps + 1):
            
            generate_config(args.config, queue_count, app_count)
            start_time = time.time()
            exit_code = subprocess.call(["bash",
                            args.script, 
                            args.spec, 
                            "spec.cfg",
                            args.behaviours,
                            f"results/{args.output_dir}/{queue_count}q_{app_count}a.log",
                            args.workers], cwd=".")
            
            elapsed_time = time.time() - start_time
            print(f"Took: {elapsed_time} seconds")
            
            if exit_code != 0:
                print("Simulation failed")
                exit(1)
else:
    queue_count = int(args.queues)
    app_count = int(args.apps)
    generate_config(args.config, queue_count, app_count)

    start_time = time.time()
    exit_code = subprocess.call(["bash", "simulate2.sh", args.spec, 
                    "spec.cfg",
                    args.behaviours,
                    f"results/{args.output_dir}/{queue_count}q_{app_count}a.log",
                    args.workers], cwd=".")
    elapsed_time = time.time() - start_time
    print(f"Took: {int(elapsed_time)} seconds")

    if exit_code != 0:
        print("Simulation failed")
        exit(1)