#!/usr/bin/env python

import argparse
import sys
import re 
import math
from os import listdir
from os.path import isfile, join, basename
from pathlib import Path
from RoundStats import RoundStats
from MemberStats import MemberStats

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

def get_percentile_fields(metric_name):
    return f"{metric_name} min,{metric_name} p50,{metric_name} p75,{metric_name} p95,{metric_name} p99,{metric_name} max"

def get_percentile_values(values):
    return str(min(values)) \
                    + "," + str(percentile(values, 0.5)) \
                    + "," + str(percentile(values, 0.75)) \
                    + "," + str(percentile(values, 0.95)) \
                    + "," + str(percentile(values, 0.99)) \
                    + "," + str(max(values))
            
parser=argparse.ArgumentParser()

parser.add_argument('--raw_output_dir', help='The directory which contains the tlc output files')
parser.add_argument('--analysis_dir', help='The directory to write the csv to')

args=parser.parse_args()

Path(f"{args.raw_output_dir}").mkdir(parents=True, exist_ok=True)
Path(f"{args.analysis_dir}").mkdir(parents=True, exist_ok=True)

rounds = dict()
per_round_metrics = dict()
per_member_metrics = dict()

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
            (key, value) = ensure_rounds_metric(per_round_metrics, updates_in_round_match)
            #per_round_metrics[key].add_updates_in_round(value)
            per_round_metrics[key].add_metric("updates_in_round", value)
            continue

        eff_updates_in_round_match = re.match( r'^"eff_updates_in_round,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if eff_updates_in_round_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, eff_updates_in_round_match)
            #per_round_metrics[key].add_eff_updates_in_round(value)
            per_round_metrics[key].add_metric("eff_updates_in_round", value)
            continue

        alive_members_count_match = re.match( r'^"alive_members_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if alive_members_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, alive_members_count_match)
            #per_round_metrics[key].add_alive_members_count(value)
            per_round_metrics[key].add_metric("alive_members_count", value)
            continue

        suspected_members_count_match = re.match( r'^"suspected_members_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if suspected_members_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, suspected_members_count_match)
            #per_round_metrics[key].add_suspected_members_count(value)
            per_round_metrics[key].add_metric("suspected_members_count", value)
            continue

        dead_members_count_match = re.match( r'^"dead_members_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if dead_members_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, dead_members_count_match)
            #per_round_metrics[key].add_dead_members_count(value)
            per_round_metrics[key].add_metric("dead_members_count", value)
            continue

        alive_states_count_match = re.match( r'^"alive_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if alive_states_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, alive_states_count_match)
            #per_round_metrics[key].add_alive_states_count(value)
            per_round_metrics[key].add_metric("alive_states_count", value)
            continue
        
        suspect_states_count_match = re.match( r'^"suspect_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if suspect_states_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, suspect_states_count_match)
            #per_round_metrics[key].add_suspect_states_count(value)
            per_round_metrics[key].add_metric("suspect_states_count", value)
            continue

        dead_states_count_match = re.match( r'^"dead_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if dead_states_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, dead_states_count_match)
            #per_round_metrics[key].add_dead_states_count(value)
            per_round_metrics[key].add_metric("dead_states_count", value)
            continue

        infective_states_count_match = re.match( r'^"infective_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if infective_states_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, infective_states_count_match)
            #per_round_metrics[key].add_infective_states_count(value)
            per_round_metrics[key].add_metric("infective_states_count", value)
            continue

        infectivity_count_match = re.match( r'^"infectivity,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if infectivity_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, infectivity_count_match)
            #per_round_metrics[key].add_infectivity_count(value)
            per_round_metrics[key].add_metric("infectivity", value)
            continue

        messages_count_match = re.match( r'^"messages_exchanged,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if messages_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, messages_count_match)
            #per_round_metrics[key].add_messages_exchanged_count(value)
            per_round_metrics[key].add_metric("messages_exchanged", value)
            continue

        direct_probes_to_dead_count_match = re.match( r'^"direct_probes_to_dead,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if direct_probes_to_dead_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, direct_probes_to_dead_count_match)
            per_round_metrics[key].add_metric("direct_probes_to_dead", value)
            continue

        indirect_probes_to_dead_count_match = re.match( r'^"indirect_probes_to_dead,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if indirect_probes_to_dead_count_match:
            (key, value) = ensure_rounds_metric(per_round_metrics, indirect_probes_to_dead_count_match)
            per_round_metrics[key].add_metric("indirect_probes_to_dead", value)
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

# Rounds stats
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

print("Written Rounds to Converge stats to " + filepath)
        
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