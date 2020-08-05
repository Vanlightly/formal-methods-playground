#!/bin/env python

import argparse, sys, os, subprocess
from pathlib import Path
import time
import concurrent.futures

def generate_config(cfg_template_file, node_count, total_clients, queue_clients):
    # create a temporary cfg file with the desired queues and apps
    template_file = open(cfg_template_file, 'r') 
    template_file = template_file.readlines() 

    cfg_lines = list()
    for line in template_file: 
        if "[NODES_PLACEHOLDER]" in line:
            nodes_set = ""
            for n in range(1, node_count+1):
                nodes_set = nodes_set + "n" + str(n)
                if n < node_count:
                    nodes_set = nodes_set + ","
                
            new_line = line.replace("[NODES_PLACEHOLDER]", nodes_set)
            cfg_lines.append(new_line)
        elif "[CLIENTS_PLACEHOLDER]" in line:
            clients_set = ""
            for c in range(1, total_clients+1):
                clients_set = clients_set + "c" + str(c)
                if c < total_clients:
                    clients_set = clients_set + ","

            new_line = line.replace("[CLIENTS_PLACEHOLDER]", clients_set)
            cfg_lines.append(new_line)
        elif "[QUEUE_CLIENTS_PLACEHOLDER]" in line:
            new_line = line.replace("[QUEUE_CLIENTS_PLACEHOLDER]", str(queue_clients))
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
parser.add_argument('--behaviours', help='The number of behaviours to gather stats for per queue/app combination')
parser.add_argument('--nodes', help='The number of nodes in the cluster')
parser.add_argument('--total_clients', help='The total number of clients')
parser.add_argument('--queue_clients', help='The total number of clients of the sharded queue')
parser.add_argument('--output_dir', help='The output directory where tlc output is saved to')
parser.add_argument('--all_perms', help='true will generate all permuations of app and queue count')
parser.add_argument('--workers', help='The number of TLC workers')

args=parser.parse_args()


Path(f"results/{args.output_dir}").mkdir(parents=True, exist_ok=True)

print(f"Running a simulation for up to {args.behaviours} behaviours")
if args.all_perms.upper() == "TRUE":

    node_count = int(args.nodes)
    total_client_count = int(args.total_clients)
    queue_client_count = int(args.queue_clients)

    if total_client_count < node_count:
        print("Total client count must be >= node count")
        exit(1)
    
    for nodes in range(node_count, node_count+1):
        for total_clients in range(nodes, total_client_count + 1):
            if total_clients % 10 != 0:
                continue

            queue_client_max = min(total_clients, queue_client_count)
            for queue_clients in range(nodes, queue_client_max + 1):
                
                generate_config(args.config, nodes, total_clients, queue_clients)

                start_time = time.time()
                exit_code = subprocess.call(["bash", "simulate.sh", args.spec, 
                                "spec.cfg",
                                args.behaviours,
                                f"results/{args.output_dir}/{nodes}n_{total_clients}c_{queue_clients}qc.log",
                                args.workers], cwd=".")
                
                elapsed_time = time.time() - start_time
                print(f"Took: {elapsed_time} seconds")
                
                if exit_code != 0:
                    print("Simulation failed")
                    exit(1)
else:
    node_count = int(args.nodes)
    total_client_count = int(args.total_clients)
    queue_client_count = int(args.queue_clients)
    generate_config(args.config, node_count, total_client_count, queue_client_count)

    start_time = time.time()
    exit_code = subprocess.call(["bash", "simulate.sh", args.spec, 
                    "spec.cfg",
                    args.behaviours,
                    f"results/{args.output_dir}/{node_count}n_{total_client_count}c_{queue_client_count}qc.log",
                    args.workers], cwd=".")
    elapsed_time = time.time() - start_time
    print(f"Took: {int(elapsed_time)} seconds")

    if exit_code != 0:
        print("Simulation failed")
        exit(1)