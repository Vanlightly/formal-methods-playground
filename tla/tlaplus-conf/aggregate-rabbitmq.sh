#!/bin/bash
SUFFIX=$1

python3 CalculatePercentiles.py -g QueueCount,AppCount \
    -v TotalReleases \
    -i ./rabbitmq/results/raw/TotalReleases${SUFFIX}.csv \
    -o ./rabbitmq/results/aggregated/agg_TotalReleases${SUFFIX}.csv

python3 CalculatePercentiles.py -g QueueCount,AppCount \
    -v PerAppReleases \
    -i ./rabbitmq/results/raw/PerAppReleases${SUFFIX}.csv \
    -o ./rabbitmq/results/aggregated/agg_PerAppReleases${SUFFIX}.csv

python3 CalculatePercentiles.py -g QueueCount,AppCount \
    -v PerAppRounds \
    -i ./rabbitmq/results/raw/PerAppRounds${SUFFIX}.csv \
    -o ./rabbitmq/results/aggregated/agg_PerAppRounds${SUFFIX}.csv

python3 CalculatePercentiles.py -g QueueCount,AppCount \
    -v PerQueueReleases \
    -i ./rabbitmq/results/raw/PerQueueReleases${SUFFIX}.csv \
    -o ./rabbitmq/results/aggregated/agg_PerQueueReleases${SUFFIX}.csv