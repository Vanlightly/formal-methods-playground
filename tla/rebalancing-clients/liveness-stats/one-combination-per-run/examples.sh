#!/bin/bash

## Example 1 -Uses variables to store stats, calculate all permutations of queue and app count
# python3.6 simulate.py --spec rebalancing_client_stats_as_vars.tla \
# --config random_template.cfg \
# --script simulate.sh \
# --behaviours 100 \
# --queues 20 \
# --app-ratio 1.5 \
# --output_dir more_stats_10 \
# --all_perms true \
# --workers 4

## Example 2 -Uses TLCGet/Set to store stats, calculate all permutations of queue and app count
# python3.6 simulate.py --spec rebalancing_client_stats_as_tlcgetset.tla \
# --config random_template.cfg \
# --script simulate-stats-nightly.sh \
# --behaviours 100 \
# --queues 20 \
# --app-ratio 1.5 \
# --output_dir more_stats_10 \
# --all_perms true \
# --workers 4

