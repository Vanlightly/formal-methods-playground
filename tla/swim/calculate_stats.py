#!/usr/bin/env python

import argparse
import sys
import re 
import math
from os import listdir
from os.path import isfile, join
from RoundStats import RoundStats

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

def ensure_metric(metric_dict, match):
    member_count = int(match.group(1))
    dead_count = int(match.group(2))
    new_count = int(match.group(3))
    suspect_timeout = int(match.group(4))
    dis_count = int(match.group(5))
    max_update_count = int(match.group(6))
    lose_every_nth = int(match.group(7))
    peer_group_size = int(match.group(8))
    initial_contacts = int(match.group(9))
    total_rounds = int(match.group(10))
    round_no = int(match.group(11))
    value = int(match.group(12))

    key = (round_no, total_rounds, member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
           lose_every_nth, peer_group_size, initial_contacts)

    if key not in metric_dict:
        metric_dict[key] = RoundStats(round_no, total_rounds, member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
           lose_every_nth, peer_group_size, initial_contacts)

    return (key, value)

def add_metric(metric_dict, match):
    member_count = int(match.group(1))
    dead_count = int(match.group(2))
    new_count = int(match.group(3))
    suspect_timeout = int(match.group(4))
    dis_count = int(match.group(5))
    max_update_count = int(match.group(6))
    lose_every_nth = int(match.group(7))
    peer_group_size = int(match.group(8))
    initial_contacts = int(match.group(9))
    value = int(match.group(10))

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

parser.add_argument('--results_dir', help='The directory which contains the tlc output files')

args=parser.parse_args()

rounds = dict()
per_round_metrics = dict()

result_files = [join(args.results_dir, f) for f in listdir(args.results_dir) if isfile(join(args.results_dir, f))]

for result_file in result_files:
    fd = open(result_file, 'r') 
    print(f"Reading {result_file}")
    lines = fd.readlines() 

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

    middle_match = "(\d*),(\d*),(\d*),(\d*),(\d*),(\d*),(\d*),(\d*),(\d*),(\d*)"
    for line in lines:
        rounds_match = re.match( r'^"rounds,' + middle_match + ',(\d*)".*', line, re.M|re.I)
        
        if rounds_match:
            add_metric(rounds, rounds_match)
            continue

        updates_in_round_match = re.match( r'^"updates_in_round,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if updates_in_round_match:
            (key, value) = ensure_metric(per_round_metrics, updates_in_round_match)
            per_round_metrics[key].add_updates_in_round(value)
            continue

        eff_updates_in_round_match = re.match( r'^"eff_updates_in_round,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if eff_updates_in_round_match:
            (key, value) = ensure_metric(per_round_metrics, eff_updates_in_round_match)
            per_round_metrics[key].add_eff_updates_in_round(value)
            continue

        alive_members_count_match = re.match( r'^"alive_members_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if alive_members_count_match:
            (key, value) = ensure_metric(per_round_metrics, alive_members_count_match)
            per_round_metrics[key].add_alive_members_count(value)
            continue

        suspected_members_count_match = re.match( r'^"suspected_members_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if suspected_members_count_match:
            (key, value) = ensure_metric(per_round_metrics, suspected_members_count_match)
            per_round_metrics[key].add_suspected_members_count(value)
            continue

        dead_members_count_match = re.match( r'^"dead_members_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if dead_members_count_match:
            (key, value) = ensure_metric(per_round_metrics, dead_members_count_match)
            per_round_metrics[key].add_dead_members_count(value)
            continue

        alive_states_count_match = re.match( r'^"alive_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if alive_states_count_match:
            (key, value) = ensure_metric(per_round_metrics, alive_states_count_match)
            per_round_metrics[key].add_alive_states_count(value)
            continue
        
        suspect_states_count_match = re.match( r'^"suspect_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if suspect_states_count_match:
            (key, value) = ensure_metric(per_round_metrics, suspect_states_count_match)
            per_round_metrics[key].add_suspect_states_count(value)
            continue

        dead_states_count_match = re.match( r'^"dead_states_count,' + middle_match + ',(\d*),(\d*)".*', line, re.M|re.I)
        if dead_states_count_match:
            (key, value) = ensure_metric(per_round_metrics, dead_states_count_match)
            per_round_metrics[key].add_dead_states_count(value)
            continue
        
parameter_names = "TotalMembers,DeadMembers,NewMembers,SuspectTimeout,Disseminations,MaxUpdates,MessageLoss%,PeerGroupSize,InitialContacts"        

print(f"{parameter_names},{get_percentile_fields('Rounds')},Behaviours")
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

    print(f"{param_values},{rounds_values},{behaviours}")


print(" ")

print(f"TotalRounds,Round" \
        + f",{parameter_names}"
        + f",{get_percentile_fields('Updates')}" \
        + f",{get_percentile_fields('EffUpdates')}" \
        + f",{get_percentile_fields('AliveMembers')}" \
        + f",{get_percentile_fields('SuspectMembers')}" \
        + f",{get_percentile_fields('DeadMembers')}" \
        + f",{get_percentile_fields('AliveStates')}" \
        + f",{get_percentile_fields('SuspectStates')}" \
        + f",{get_percentile_fields('DeadStates')}" \
        + ",Behaviours")
        
for key in per_round_metrics.keys():    
    (round_no, total_rounds, member_count, dead_count, new_count, suspect_timeout, dis_count, max_update_count,\
           lose_every_nth, peer_group_size, initial_contacts) = key

    if lose_every_nth == 0:
        message_loss = 0
    else:
        message_loss = round(float(1.0 / lose_every_nth)*100, 1)

    updates = per_round_metrics[key].get_updates_in_round()
    updates.sort()

    eff_updates = per_round_metrics[key].get_eff_updates_in_round()
    eff_updates.sort()

    alive_members_count = per_round_metrics[key].get_alive_members_count()
    alive_members_count.sort()

    suspected_members_count = per_round_metrics[key].get_suspected_members_count()
    suspected_members_count.sort()

    dead_members_count = per_round_metrics[key].get_dead_members_count()
    dead_members_count.sort()

    alive_states_count = per_round_metrics[key].get_alive_states_count()
    alive_states_count.sort()

    suspect_states_count = per_round_metrics[key].get_suspect_states_count()
    suspect_states_count.sort()

    dead_states_count = per_round_metrics[key].get_dead_states_count()
    dead_states_count.sort()

    param_values = f"{member_count},{dead_count},{new_count},{suspect_timeout},{dis_count},{max_update_count},{message_loss},{peer_group_size},{initial_contacts}"
    behaviours = len(updates)

    print(f"{total_rounds},{round_no}" \
        + f",{param_values}" \
        + f",{get_percentile_values(updates)}" \
        + f",{get_percentile_values(eff_updates)}" \
        + f",{get_percentile_values(alive_members_count)}" \
        + f",{get_percentile_values(suspected_members_count)}" \
        + f",{get_percentile_values(dead_members_count)}" \
        + f",{get_percentile_values(alive_states_count)}" \
        + f",{get_percentile_values(suspect_states_count)}" \
        + f",{get_percentile_values(dead_states_count)}" \
        + f",{behaviours}")
