#!/bin/bash

CONFIG=$1
WORKERS=$2

tlc-nightly -simulate RebalancingClientsWithStatsVariants.tla -config $CONFIG -deadlock -generate -workers $WORKERS -depth 10000