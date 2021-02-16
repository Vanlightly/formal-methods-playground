#!/usr/bin/env python

# python3.6 calculate_stats.py --raw_output_dir "$(pwd)/results/xyz" --analysis_dir "$(pwd)/analysis"

import argparse
import sys
import re 
import math
from os import listdir
from os.path import isfile, join, basename
from pathlib import Path
from RoundStats import RoundStats
from MemberStats import MemberStats
from ExecutionStats import ExecutionStats

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

# ToString(Cardinality(Member)) 
    # \o "," \o ToString(DeadMemberCount)
    # \o "," \o ToString(NewMemberCount)
    # \o "," \o ToString(SuspectTimeout)
    # \o "," \o ToString(DisseminationLimit)
    # \o "," \o ToString(MaxUpdatesPerPiggyBack)
    # \o "," \o ToString(LoseEveryNth)
    # \o "," \o ToString(PeerGroupSize)
    # \o "," \o ToString(InitialContacts)
    # \o "," \o ToString(MaxRound)

def ensure_rounds_metric(metric_dict, match):
    member_count = int(match.group(2))
    dead_count = int(match.group(3))
    new_count = int(match.group(4))
    suspect_timeout = int(match.group(5))
    dis_count = int(match.group(6))
    max_update_count = int(match.group(7))
    lose_every_nth = int(match.group(8))
    peer_group_size = int(match.group(9))
    initial_contacts = int(match.group(10))
    total_rounds = int(match.group(11))
    round_no = int(match.group(12))
    value = int(match.group(13))

    key = (round_no, total_rounds, member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
           lose_every_nth, peer_group_size, initial_contacts)

    if key not in metric_dict:
        metric_dict[key] = RoundStats(round_no, total_rounds, member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
           lose_every_nth, peer_group_size, initial_contacts)

    return (key, value)

def ensure_members_metric(metric_dict, match):
    member_count = int(match.group(2))
    dead_count = int(match.group(3))
    new_count = int(match.group(4))
    suspect_timeout = int(match.group(5))
    dis_count = int(match.group(6))
    max_update_count = int(match.group(7))
    lose_every_nth = int(match.group(8))
    peer_group_size = int(match.group(9))
    initial_contacts = int(match.group(10))
    member = int(match.group(12))
    value = int(match.group(13))

    key = (member, member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
           lose_every_nth, peer_group_size, initial_contacts)

    if key not in metric_dict:
        metric_dict[key] = MemberStats(member, member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
           lose_every_nth, peer_group_size, initial_contacts)

    return (key, value)

def add_metric(metric_dict, match):
    member_count = int(match.group(2))
    dead_count = int(match.group(3))
    new_count = int(match.group(4))
    suspect_timeout = int(match.group(5))
    dis_count = int(match.group(6))
    max_update_count = int(match.group(7))
    lose_every_nth = int(match.group(8))
    peer_group_size = int(match.group(9))
    initial_contacts = int(match.group(10))
    value = int(match.group(11))

    key = (member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
           lose_every_nth, peer_group_size, initial_contacts)

    if key not in metric_dict:
        metric_dict[key] = list()
    
    metric_dict[key].append(value)    

def ensure_execution_metric(executions_dict, match):
    exec_no = int(match.group(1))
    member_count = int(match.group(2))
    dead_count = int(match.group(3))
    new_count = int(match.group(4))
    suspect_timeout = int(match.group(5))
    dis_count = int(match.group(6))
    max_update_count = int(match.group(7))
    lose_every_nth = int(match.group(8))
    peer_group_size = int(match.group(9))
    initial_contacts = int(match.group(10))
    total_rounds = int(match.group(11))
    round_no = int(match.group(12))
    value = int(match.group(13))

    if exec_no not in executions_dict:
        executions_dict[exec_no] = ExecutionStats(exec_no, member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
           lose_every_nth, peer_group_size, initial_contacts)

    return (exec_no, round_no, value)

def get_percentile_fields(metric_name):
    return f"{metric_name} min,{metric_name} p50,{metric_name} p75,{metric_name} p95,{metric_name} p99,{metric_name} max"

def get_percentile_values(values):
    return str(min(values)) \
                    + "," + str(percentile(values, 0.5)) \
                    + "," + str(percentile(values, 0.75)) \
                    + "," + str(percentile(values, 0.95)) \
                    + "," + str(percentile(values, 0.99)) \
                    + "," + str(max(values))

def process_round_match(match, name, per_round_metrics, per_exec_metrics):
    (key, value) = ensure_rounds_metric(per_round_metrics, match)
    per_round_metrics[key].add_metric(name, value)
    
    (exec_no, round_no, value2) = ensure_execution_metric(per_exec_metrics, match)
    per_exec_metrics[exec_no].add_metric(round_no, name, value2)

parser=argparse.ArgumentParser()

parser.add_argument('--raw_output_dir', help='The directory which contains the tlc output files')
parser.add_argument('--analysis_dir', help='The directory to write the csv to')

args=parser.parse_args()

Path(f"{args.raw_output_dir}").mkdir(parents=True, exist_ok=True)
Path(f"{args.analysis_dir}").mkdir(parents=True, exist_ok=True)

rounds = dict()
per_round_metrics = dict()
per_member_metrics = dict()
per_exec_metrics = dict()

result_files = [join(args.raw_output_dir, f) for f in listdir(args.raw_output_dir) if isfile(join(args.raw_output_dir, f))]

for result_file in result_files:
    fd = open(result_file, 'r') 
    print(f"Reading {result_file}")
    lines = fd.readlines() 

    # ToString(Cardinality(Member)) 
    # \o "," \o ToString(exec_id)
    # \o "," \o ToString(DeadMemberCount)
    # \o "," \o ToString(NewMemberCount)
    # \o "," \o ToString(SuspectTimeout)
    # \o "," \o ToString(DisseminationLimit)
    # \o "," \o ToString(MaxUpdatesPerPiggyBack)
    # \o "," \o ToString(LoseEveryNth)
    # \o "," \o ToString(PeerGroupSize)
    # \o "," \o ToString(InitialContacts)
    # \o "," \o ToString(MaxRound)

    middle_match = "(\d*),(\d*),(\d*),(\d*),(\d*),(\d*),(\d*),(\d*),(\d*),(\d*),(\d*)"
    for line in lines:
        rounds_match = re.match( r'^"rounds,' + middle_match + ',(\d*)".*', line, re.M|re.I)
        
        if rounds_match:
            add_metric(rounds, rounds_match)
            continue

        updates_in_round_match = re.match( r'^"updates_in_round,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if updates_in_round_match:
            process_round_match(updates_in_round_match, "updates_in_round", per_round_metrics, per_exec_metrics)
            continue

        eff_updates_in_round_match = re.match( r'^"eff_updates_in_round,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if eff_updates_in_round_match:
            process_round_match(eff_updates_in_round_match, "eff_updates_in_round", per_round_metrics, per_exec_metrics)
            continue

        alive_members_count_match = re.match( r'^"alive_members_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if alive_members_count_match:
            process_round_match(alive_members_count_match, "alive_members_count", per_round_metrics, per_exec_metrics)
            continue

        suspected_members_count_match = re.match( r'^"suspected_members_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if suspected_members_count_match:
            process_round_match(suspected_members_count_match, "suspected_members_count", per_round_metrics, per_exec_metrics)
            continue

        dead_members_count_match = re.match( r'^"dead_members_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if dead_members_count_match:
            process_round_match(dead_members_count_match, "dead_members_count", per_round_metrics, per_exec_metrics)
            continue

        alive_states_count_match = re.match( r'^"alive_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if alive_states_count_match:
            process_round_match(alive_states_count_match, "alive_states_count", per_round_metrics, per_exec_metrics)
            continue
        
        suspect_states_count_match = re.match( r'^"suspect_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if suspect_states_count_match:
            process_round_match(suspect_states_count_match, "suspect_states_count", per_round_metrics, per_exec_metrics)
            continue

        dead_states_count_match = re.match( r'^"dead_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if dead_states_count_match:
            process_round_match(dead_states_count_match, "dead_states_count", per_round_metrics, per_exec_metrics)
            continue

        infective_states_count_match = re.match( r'^"infective_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if infective_states_count_match:
            process_round_match(infective_states_count_match, "infective_states_count", per_round_metrics, per_exec_metrics)
            continue

        infectivity_count_match = re.match( r'^"infectivity,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if infectivity_count_match:
            process_round_match(infectivity_count_match, "infectivity", per_round_metrics, per_exec_metrics)
            continue

        messages_count_match = re.match( r'^"messages_exchanged,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if messages_count_match:
            process_round_match(messages_count_match, "messages_exchanged", per_round_metrics, per_exec_metrics)
            continue

        direct_probes_to_dead_count_match = re.match( r'^"direct_probes_to_dead,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if direct_probes_to_dead_count_match:
            process_round_match(direct_probes_to_dead_count_match, "direct_probes_to_dead", per_round_metrics, per_exec_metrics)
            continue

        indirect_probes_to_dead_count_match = re.match( r'^"indirect_probes_to_dead,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if indirect_probes_to_dead_count_match:
            process_round_match(indirect_probes_to_dead_count_match, "indirect_probes_to_dead", per_round_metrics, per_exec_metrics)
            continue

        received_msg_count_match = re.match( r'^"received_messages,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if received_msg_count_match:
            (key, value) = ensure_members_metric(per_member_metrics, received_msg_count_match)
            per_member_metrics[key].add_metric("received_messages", value)
            continue

        received_probe_msg_count_match = re.match( r'^"received_probe_messages,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if received_probe_msg_count_match:
            (key, value) = ensure_members_metric(per_member_metrics, received_probe_msg_count_match)
            per_member_metrics[key].add_metric("received_probe_messages", value)
            continue

        received_probe_request_msg_count_match = re.match( r'^"received_probe_request_messages,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if received_probe_request_msg_count_match:
            (key, value) = ensure_members_metric(per_member_metrics, received_probe_request_msg_count_match)
            per_member_metrics[key].add_metric("received_probe_request_messages", value)
            continue

# Rounds to convergence
filepath = join(args.analysis_dir, basename(args.raw_output_dir) + "-rtc.csv")
f = open(filepath, "a")
parameter_names = "TotalMembers,DeadMembers,NewMembers,SuspectTimeout,Disseminations,MaxUpdates,MessageLoss%,PeerGroupSize,InitialContacts"        

f.write(f"{parameter_names},{get_percentile_fields('Rounds')},Behaviours\n")
for key in rounds.keys():    
    (member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
           lose_every_nth, peer_group_size, initial_contacts) = key

    rounds_of_key = rounds[key]
    rounds_of_key.sort()
    rounds_values = get_percentile_values(rounds_of_key)
    
    if lose_every_nth == 0:
        message_loss = 0
    else:
        message_loss = round(float(1.0 / lose_every_nth)*100, 1)

    behaviours = len(rounds_of_key)

    param_values = f"{member_count},{dead_count},{new_count},{suspect_timeout},{dis_count},{max_update_count},{message_loss},{peer_group_size},{initial_contacts}"

    f.write(f"{param_values},{rounds_values},{behaviours}\n")

f.close()

print("Written rounds to convergence to " + filepath)

# Rounds aggregated stats
filepath = join(args.analysis_dir, basename(args.raw_output_dir) + "-round-stats.csv")
f = open(filepath, "a")

f.write(f"TotalRounds,Round" \
        + f",{parameter_names}"
        + f",{get_percentile_fields('Updates')}" \
        + f",{get_percentile_fields('EffUpdates')}" \
        + f",{get_percentile_fields('AliveMembers')}" \
        + f",{get_percentile_fields('SuspectMembers')}" \
        + f",{get_percentile_fields('DeadMembers')}" \
        + f",{get_percentile_fields('AliveStates')}" \
        + f",{get_percentile_fields('SuspectStates')}" \
        + f",{get_percentile_fields('DeadStates')}" \
        + f",{get_percentile_fields('InfectiveStates')}" \
        + f",{get_percentile_fields('Infectivity')}" \
        + f",{get_percentile_fields('Messages')}" \
        + f",{get_percentile_fields('DirectProbesToDead')}" \
        + f",{get_percentile_fields('IndirectProbesToDead')}" \
        + ",Behaviours\n")
        
for key in per_round_metrics.keys():    
    # try:
    (round_no, total_rounds, member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
        lose_every_nth, peer_group_size, initial_contacts) = key

    if lose_every_nth == 0:
        message_loss = 0
    else:
        message_loss = round(float(1.0 / lose_every_nth)*100, 1)

    updates = per_round_metrics[key].get_metric("updates_in_round")
    updates.sort()

    eff_updates = per_round_metrics[key].get_metric("eff_updates_in_round")
    eff_updates.sort()

    alive_members_count = per_round_metrics[key].get_metric("alive_members_count")
    alive_members_count.sort()

    suspected_members_count = per_round_metrics[key].get_metric("suspected_members_count")
    suspected_members_count.sort()

    dead_members_count = per_round_metrics[key].get_metric("dead_members_count")
    dead_members_count.sort()

    alive_states_count = per_round_metrics[key].get_metric("alive_states_count")
    alive_states_count.sort()

    suspect_states_count = per_round_metrics[key].get_metric("suspect_states_count")
    suspect_states_count.sort()

    dead_states_count = per_round_metrics[key].get_metric("dead_states_count")
    dead_states_count.sort()

    infective_states_count = per_round_metrics[key].get_metric("infective_states_count")
    infective_states_count.sort()

    infectivity_count = per_round_metrics[key].get_metric("infectivity")
    infectivity_count.sort()

    messages_count = per_round_metrics[key].get_metric("messages_exchanged")
    messages_count.sort()

    direct_probes_to_dead_count = per_round_metrics[key].get_metric("direct_probes_to_dead")
    direct_probes_to_dead_count.sort()

    indirect_probes_to_dead_count = per_round_metrics[key].get_metric("indirect_probes_to_dead")
    indirect_probes_to_dead_count.sort()

    param_values = f"{member_count},{dead_count},{new_count},{suspect_timeout},{dis_count},{max_update_count},{message_loss},{peer_group_size},{initial_contacts}"
    behaviours = len(updates)

    f.write(f"{total_rounds},{round_no}" \
        + f",{param_values}" \
        + f",{get_percentile_values(updates)}" \
        + f",{get_percentile_values(eff_updates)}" \
        + f",{get_percentile_values(alive_members_count)}" \
        + f",{get_percentile_values(suspected_members_count)}" \
        + f",{get_percentile_values(dead_members_count)}" \
        + f",{get_percentile_values(alive_states_count)}" \
        + f",{get_percentile_values(suspect_states_count)}" \
        + f",{get_percentile_values(dead_states_count)}" \
        + f",{get_percentile_values(infective_states_count)}" \
        + f",{get_percentile_values(infectivity_count)}" \
        + f",{get_percentile_values(messages_count)}" \
        + f",{get_percentile_values(direct_probes_to_dead_count)}" \
        + f",{get_percentile_values(indirect_probes_to_dead_count)}" \
        + f",{behaviours}\n")

f.close()
print("Written per round stats to " + filepath)

# Rounds per execution stats
filepath = join(args.analysis_dir, basename(args.raw_output_dir) + "-per-exec-round-stats.csv")
f = open(filepath, "a")

f.write(f"ExecNo,TotalRounds,Round" \
        + f",{parameter_names}"
        + f",'Updates'" \
        + f",'EffUpdates'" \
        + f",'AliveMembers'" \
        + f",'SuspectMembers'" \
        + f",'DeadMembers'" \
        + f",'AliveStates'" \
        + f",'SuspectStates'" \
        + f",'DeadStates'" \
        + f",'InfectiveStates'" \
        + f",'Infectivity'" \
        + f",'Messages'" \
        + f",'DirectProbesToDead'" \
        + f",'IndirectProbesToDead'\n")

total_round_ctr = dict()

for exec_no in per_exec_metrics.keys():    
    # try:
    exec_stats = per_exec_metrics[exec_no]

    if exec_stats.total_rounds not in total_round_ctr:
        total_round_ctr[exec_stats.total_rounds] = 1
    else:
        total_round_ctr[exec_stats.total_rounds] = total_round_ctr[exec_stats.total_rounds] + 1

    if total_round_ctr[exec_stats.total_rounds] >= 101:
        continue

    if exec_stats.lose_every_nth == 0:
        message_loss = 0
    else:
        message_loss = round(float(1.0 / exec_stats.lose_every_nth)*100, 1)

    for round_no in range(1, exec_stats.total_rounds+1):
        if not exec_stats.has_round(round_no):
            continue

        updates = exec_stats.get_metric(round_no, "updates_in_round")
        eff_updates = exec_stats.get_metric(round_no, "eff_updates_in_round")
        alive_members_count = exec_stats.get_metric(round_no, "alive_members_count")
        suspected_members_count = exec_stats.get_metric(round_no, "suspected_members_count")
        dead_members_count = exec_stats.get_metric(round_no, "dead_members_count")
        alive_states_count = exec_stats.get_metric(round_no, "alive_states_count")
        suspect_states_count = exec_stats.get_metric(round_no, "suspect_states_count")
        dead_states_count = exec_stats.get_metric(round_no, "dead_states_count")
        infective_states_count = exec_stats.get_metric(round_no, "infective_states_count")
        infectivity_count = exec_stats.get_metric(round_no, "infectivity")
        messages_count = exec_stats.get_metric(round_no, "messages_exchanged")
        direct_probes_to_dead_count = exec_stats.get_metric(round_no, "direct_probes_to_dead")
        indirect_probes_to_dead_count = exec_stats.get_metric(round_no, "indirect_probes_to_dead")

        param_values = f"{exec_stats.member_count},{exec_stats.dead_count},{exec_stats.new_count},{exec_stats.suspect_timeout},{exec_stats.disseminations},{exec_stats.max_updates},{message_loss},{exec_stats.peer_group_size},{exec_stats.initial_contacts}"
        
        f.write(f"{exec_no},{exec_stats.total_rounds},{round_no}" \
            + f",{param_values}" \
            + f",{updates}" \
            + f",{eff_updates}" \
            + f",{alive_members_count}" \
            + f",{suspected_members_count}" \
            + f",{dead_members_count}" \
            + f",{alive_states_count}" \
            + f",{suspect_states_count}" \
            + f",{dead_states_count}" \
            + f",{infective_states_count}" \
            + f",{infectivity_count}" \
            + f",{messages_count}" \
            + f",{direct_probes_to_dead_count}" \
            + f",{indirect_probes_to_dead_count}\n")

f.close()
print("Written per execution round stats to " + filepath)

# Members stats
filepath = join(args.analysis_dir, basename(args.raw_output_dir) + "-member-stats.csv")
f = open(filepath, "a")

parameter_names = "DeadMembers,NewMembers,SuspectTimeout,Disseminations,MaxUpdates,MessageLoss%,PeerGroupSize,InitialContacts"        

f.write(f"TotalMembers,Member" \
        + f",{parameter_names}" \
        + f",TotalRecv" \
        + f",TotalProbeRecv" \
        + f",TotalProbeReqRecv" \
        + f",{get_percentile_fields('RecvMgs')}" \
        + f",{get_percentile_fields('RecvProbeMgs')}" \
        + f",{get_percentile_fields('RecvProbeReqMgs')}" \
        + ",Behaviours\n")

for key in per_member_metrics.keys():    
    # try:
    (member, member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
        lose_every_nth, peer_group_size, initial_contacts) = key

    if lose_every_nth == 0:
        message_loss = 0
    else:
        message_loss = round(float(1.0 / lose_every_nth)*100, 1)

    received_messages = per_member_metrics[key].get_metric("received_messages")
    received_messages.sort()

    received_probe_messages = per_member_metrics[key].get_metric("received_probe_messages")
    received_probe_messages.sort()

    received_probe_req_messages = per_member_metrics[key].get_metric("received_probe_request_messages")
    received_probe_req_messages.sort()

    param_values = f"{dead_count},{new_count},{suspect_timeout},{dis_count},{max_update_count},{message_loss},{peer_group_size},{initial_contacts}"
    behaviours = len(received_messages)

    recv_sum = 0
    for num in received_messages:
        recv_sum += num

    recv_probe_sum = 0
    for num in received_probe_messages:
        recv_probe_sum += num

    recv_probe_req_sum = 0
    for num in received_probe_req_messages:
        recv_probe_req_sum += num

    f.write(f"{member_count},{member}" \
        + f",{param_values}" \
        + f",{recv_sum}" \
        + f",{recv_probe_sum}" \
        + f",{recv_probe_req_sum}" \
        + f",{get_percentile_values(received_messages)}" \
        + f",{get_percentile_values(received_probe_messages)}" \
        + f",{get_percentile_values(received_probe_req_messages)}" \
        + f",{behaviours}\n")

f.close()

print("Written per member stats to " + filepath)