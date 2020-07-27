#!/bin/bash

SPEC=$1
ORDERING=$2
BEHAVIOURS=$3
OUTPUT=$4


trap kill_tlc INT

function kill_tlc() {
    kill $PID
    echo "Stopped simulation with pid $PID"
    exit 0
}

if [ $ORDERING == "random" ]; then
    CONFIG=rabbit_leaderless_rebalancing_stats_random.cfg
else
    CONFIG=rabbit_leaderless_rebalancing_stats_sequential.cfg
fi

echo "Running $ORDERING simulation for up to $BEHAVIOURS behaviours"
tlc -simulate $SPEC -deadlock -workers 4 -depth $BEHAVIOURS -config $CONFIG -maxSetSize 100000000 > "$OUTPUT" 2>&1 &
PID=$!

echo "Simulation run with $SPEC up to $BEHAVIOURS behaviours, outputting to $OUTPUT, with pid=$PID"

LAST_PRINTED=$(date +%s)
while sleep 1
do
    BEHAVIOURS_COMPUTED=$(grep -c total_releases "$OUTPUT")
    if [[ $BEHAVIOURS_COMPUTED -ge $BEHAVIOURS ]]
    then
        echo "Computed $BEHAVIOURS_COMPUTED behaviours"
        kill $PID
        echo "Stopped simulation with pid $PID"
        exit 0
    fi

    if ps -p $PID > /dev/null
    then
        NOW=$(date +%s)
        if [[ $(($NOW - $LAST_PRINTED)) -ge 10 ]]
        then
            echo "$(date +"%H:%M"): Computed $BEHAVIOURS_COMPUTED behaviours"
            LAST_PRINTED=$NOW
        fi
    else
        echo "TLC has exited"
        echo "Computed $BEHAVIOURS_COMPUTED behaviours"
        exit 0
    fi
    
done