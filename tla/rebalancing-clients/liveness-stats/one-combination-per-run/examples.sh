#!/bin/bash

## Example 1 - Non-determinism - 50 queues, 50 apps
#python3.6 simulate.py --spec rabbit_leaderless_rebalancing_stats.tla \
# --config random_template.cfg \
# --behaviours 100 \
# --queues 50 \
# --apps 50 \
# --output_dir non-det-50x50 \
# --all_perms false

## Example 2 - RandomElement - 5 queues, 5 apps (really slow right now)
#python3.6 simulate.py --spec rabbit_leaderless_rebalancing_stats_random_element.tla \
# --config random_template.cfg \
# --behaviours 100 \
# --queues 5 \
# --apps 5 \
# --output_dir random-element-5x5 \
# --all_perms false

## Example 3 - Non-determinism - All permutations of queue and app count (with app count as a ratio of queues)
#python3.6 simulate.py --spec rabbit_leaderless_rebalancing_stats.tla \
# --config random_template.cfg \
# --behaviours 100 \
# --queues 10 \
# --app-ratio 1.5 \
# --output_dir non-det-all-perms-10x15 \
# --all_perms true

## Example 2 - RandomElement - All permuations of 5 queues, 5 apps (really slow right now)
#python3.6 simulate.py --spec rabbit_leaderless_rebalancing_stats_random_element.tla \
# --config random_template.cfg \
# --behaviours 100 \
# --queues 5 \
# --apps 5 \
# --output_dir random-element-5x5 \
# --all_perms true