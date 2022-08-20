#!/bin/bash

CONFIG=$1
WORKERS=$2

# ensure there is a script called tlc that will run tlc

tlc -generate RebalancingClientsWithStatsVariants2.tla -config $CONFIG -deadlock -workers $WORKERS -depth 10000