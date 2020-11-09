#!/bin/env python

import argparse, sys, os, subprocess
from pathlib import Path
import time

# python3.6 simulate.py \
# --spec swim_stats_runner.tla \
# --config swim_stats_template.cfg \
# --script tlc-nightly \
# --behaviours 100 \
# --dimension1 none \
# --output_dir test1 \
# --workers 1 \
# --members 10 \
# --dead 1 \
# --new 0 \
# --initial_contact 0 \
# --peer_group_size 0 \
# --suspect_timeout 0 \
# --disseminations 3 \
# --max_updates 3 \
# --lose_every_nth 0 \
# --force_to_round 0

def generate_config(cfg_template_file, 
                    dead_count, 
                    new_count,
                    intial_contact_count,
                    peer_group_size,
                    suspect_timeout, 
                    dissemination_limit, 
                    max_updates,
                    lose_every_nth,
                    force_to_round):
    # create a temporary cfg file with the desired queues and apps
    template_file = open(cfg_template_file, 'r') 
    template_file = template_file.readlines() 
    
    mappings = dict()
    mappings["[PEER_GROUP_SIZE]"] = str(peer_group_size)
    mappings["[SUSPECT_TIMEOUT]"] = str(suspect_timeout)
    mappings["[DIS_LIMIT]"] = str(dissemination_limit)
    mappings["[MAX_UPDATES]"] = str(max_updates)

    if lose_every_nth == 0:
        mappings["[MESSAGE_LOSS_MODE]"] = "none"
    else:
        mappings["[MESSAGE_LOSS_MODE]"] = "probabilistic"

    mappings["[LOSE_EVERY_NTH]"] = str(lose_every_nth)
    mappings["[INITIAL_CONTACT]"] = str(intial_contact_count)
    mappings["[DEAD_MEMBERS]"] = str(dead_count)
    mappings["[NEW_MEMBERS]"] = str(new_count)
    mappings["[FORCE_TO_ROUND]"] = str(force_to_round)
    
    cfg_lines = list()
    for line in template_file: 
        for key in mappings:
            replaced = False
            if key in line:
                new_line = line.replace(key, mappings[key])
                cfg_lines.append(new_line)    
                replaced = True
                break
        
        if not replaced:
            cfg_lines.append(line)    

    new_cfg_file = f"spec.cfg"
    new_cfg_fd = open(new_cfg_file, 'w') 
    new_cfg_fd.writelines(cfg_lines)
    new_cfg_fd.close()

def generate_runner(runner_file, member_count):
    template_file = open(f"{runner_file}", 'r') 
    template_file = template_file.readlines() 

    lines = list()
    for line in template_file: 
        if "[MEMBERS_PLACEHOLDER]" in line:
            new_line = line.replace("[MEMBERS_PLACEHOLDER]", f"1..{member_count}")
            lines.append(new_line)
        else:
            lines.append(line)

    spec = runner_file.replace(".tla", "")
    new_tla_file = f"{spec}_generated.tla"
    new_tla_fd = open(new_tla_file, 'w') 
    new_tla_fd.writelines(lines)
    new_tla_fd.close()

    return new_tla_file
    

def run_one_config(args, 
                param_members,
                param_dead, 
                param_new,
                param_initial_contact,
                param_peer_group_size,
                param_suspect_timeout, 
                param_disseminations, 
                param_max_updates,
                param_lose_every_nth,
                param_force_to_round):
    print(param_dead)
    generate_config(args.config, param_dead,  param_new, param_initial_contact, param_peer_group_size,\
                    param_suspect_timeout, param_disseminations, param_max_updates, param_lose_every_nth, param_force_to_round)
    generated_spec = generate_runner(args.spec, param_members)
    start_time = time.time()
    exit_code = subprocess.call(["bash", args.script, generated_spec, 
                    "spec.cfg",
                    args.behaviours,
                    f"{args.output_dir}/{param_members}m_{param_dead}d_{param_new}n_{param_initial_contact}i_{param_peer_group_size}pg_{param_lose_every_nth}ln_{param_suspect_timeout}s_{param_disseminations}ds_{param_max_updates}u_{param_force_to_round}fr.log",
                    args.workers], cwd=".")
    elapsed_time = time.time() - start_time
    print(f"Took: {int(elapsed_time)} seconds")

    if exit_code != 0:
        print("Simulation failed")
        exit(1)

def get_parameter_val(parameter):
    if "-" in parameter:
        return int(parameter.split("-")[0])
    else:
        return int(parameter)

def get_parameter_max_val(parameter):
    return int(parameter.split("-")[1])        

parser=argparse.ArgumentParser()

parser.add_argument('--spec', help='The TLA+ specification to run')
parser.add_argument('--config', help='The cfg file')
parser.add_argument('--script', help='The simulation script to run')
parser.add_argument('--behaviours', help='The number of behaviours to gather stats for per queue/app combination')
parser.add_argument('--dimension1', help='The 1st dimension, if any')
parser.add_argument('--output_dir', help='The output directory where tlc output is saved to')
parser.add_argument('--workers', help='The number of TLC workers')

# configuration parameters of spec
parser.add_argument('--members', help='The maximum number of members')
parser.add_argument('--dead', help='The maximum number of undetected dead members in the initial state')
parser.add_argument('--new', help='The maximum number of undetected new members in the initial state')
parser.add_argument('--initial_contact', help='The maximum number of peers a joining member can probe')
parser.add_argument('--peer_group_size', help='The maximum number of peers a member can send probe requests')
parser.add_argument('--suspect_timeout', help='The maximum number of rounds until a suspect state transitions to a dead state')
parser.add_argument('--disseminations', help='The maximum number of disemminations an update can have')
parser.add_argument('--max_updates', help='The maximum number of updates piggybacked on any probe or ack')
parser.add_argument('--lose_every_nth', help='The n of 1/n probability of any given message being lost')
parser.add_argument('--force_to_round', help='Run the simulation till either everyone thinks everyone else is dead, or this number of rounds')

args=parser.parse_args()


Path(f"{args.output_dir}").mkdir(parents=True, exist_ok=True)

print(f"Running a simulation for up to {args.behaviours} behaviours")

members = get_parameter_val(args.members)
dead = get_parameter_val(args.dead)
new = get_parameter_val(args.new)
initial_contact = get_parameter_val(args.initial_contact)
peer_group_size = get_parameter_val(args.peer_group_size)
force_to_round = get_parameter_val(args.force_to_round)
suspect_timeout = get_parameter_val(args.suspect_timeout)
disseminations = get_parameter_val(args.disseminations)
max_updates = get_parameter_val(args.max_updates)
lose_every_nth = get_parameter_val(args.lose_every_nth)

if args.dimension1 == "none":
    run_one_config(args, members, dead, new, initial_contact, peer_group_size, suspect_timeout, disseminations, max_updates, lose_every_nth, force_to_round)        
elif args.dimension1 == "members":
    max_val = get_parameter_max_val(args.members)
    for members_val in range(members, max_val + 1):
        run_one_config(args, members_val, dead, new, initial_contact, peer_group_size, suspect_timeout, disseminations, max_updates, lose_every_nth, force_to_round)        
elif args.dimension1 == "dead":
    max_val = get_parameter_max_val(args.dead)
    for dead_val in range(dead, max_val + 1):
        run_one_config(args, members, dead_val, new, initial_contact, peer_group_size, suspect_timeout, disseminations, max_updates, lose_every_nth, force_to_round)        
elif args.dimension1 == "new":
    max_val = get_parameter_max_val(args.new)
    for new_val in range(new, max_val + 1):
        run_one_config(args, members, dead, new_val, initial_contact, peer_group_size, suspect_timeout, disseminations, max_updates, lose_every_nth, force_to_round)        
elif args.dimension1 == "suspect_timeout":
    max_val = get_parameter_max_val(args.suspect_timeout)
    for suspect_timeout_val in range(suspect_timeout, max_val + 1):
        run_one_config(args, members, dead, new, initial_contact, peer_group_size, suspect_timeout_val, disseminations, max_updates, lose_every_nth, force_to_round)        
elif args.dimension1 == "disseminations":
    max_val = get_parameter_max_val(args.disseminations)
    for disseminations_val in range(disseminations, max_val+1):
        run_one_config(args, members, dead, new, initial_contact, peer_group_size, suspect_timeout, disseminations_val, max_updates, lose_every_nth, force_to_round)        
elif args.dimension1 == "max_updates":
    max_val = get_parameter_max_val(args.max_updates)
    for max_updates_val in range(max_updates, max_val + 1):
        run_one_config(args, members, dead, new, initial_contact, peer_group_size, suspect_timeout, disseminations, max_updates_val, lose_every_nth, force_to_round)        
elif args.dimension1 == "lose_every_nth":
    max_val = get_parameter_max_val(args.lose_every_nth)
    for lose_every_nth_val in range(lose_every_nth, max_val + 1):
        run_one_config(args, members, dead, new, initial_contact, peer_group_size, suspect_timeout, disseminations, max_updates, lose_every_nth_val, force_to_round)                
elif args.dimension1 == "initial_contact" or args.dimension1 == "initial_contacts":
    max_val = get_parameter_max_val(args.initial_contact)
    for ic_val in range(initial_contact, max_val+1):
        run_one_config(args, members, dead, new, ic_val, peer_group_size, suspect_timeout, disseminations, max_updates, lose_every_nth, force_to_round)        
else:
    print("Invalid dimension")
    exit(1)