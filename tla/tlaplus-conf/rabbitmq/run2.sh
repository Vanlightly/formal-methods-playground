#!/bin/bash

CONFIG=$1
WORKERS=$2

tlc-nightly -simulate RebalancingClientsWithStatsVariants2.tla -config $CONFIG -deadlock -generate -workers $WORKERS -depth 10000