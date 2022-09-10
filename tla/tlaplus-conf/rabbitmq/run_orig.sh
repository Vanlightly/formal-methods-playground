#!/bin/bash

CONFIG=$1
WORKERS=$2

# ensure there is a script called tlc that will run tlc

tlc-nightly -generate RebalancingClientsWithStats.tla -config $CONFIG -deadlock -workers $WORKERS -depth 10000