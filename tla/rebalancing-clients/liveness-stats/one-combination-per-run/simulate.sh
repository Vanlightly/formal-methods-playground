#!/bin/bash

SPEC=$1
CONFIG=$2
BEHAVIOURS=$3
OUTPUT=$4
WORKERS=$5

trap kill_tlc INT

function kill_tlc() {
    #kill $PID
    #echo "Stopped simulation with pid $PID"

    pkill -f tlc
    exit 0
}

#echo "Running simulation for up to $BEHAVIOURS behaviours"
pkill -f tlc

tlc -simulate $SPEC -deadlock -workers $5 -depth 50000 -config $CONFIG -maxSetSize 10000000 > "$OUTPUT" 2>&1 &
PID=$!

echo "Simulation outputting to $OUTPUT, with pid=$PID"

LAST_PRINTED=$(date +%s)
while sleep 1
do
    ERRORS=$(grep -c Exception "$OUTPUT")
    if [[ $BEHAVIOURS_COMPUTED -ge $BEHAVIOURS ]]
    then
        echo "Error detected, stopping. Computed $BEHAVIOURS_COMPUTED behaviours."
        pkill -f tlc
        exit 1
    fi

    BEHAVIOURS_COMPUTED=$(grep -c total_releases "$OUTPUT")
    if [[ $BEHAVIOURS_COMPUTED -ge $BEHAVIOURS ]]
    then
        echo "Computed $BEHAVIOURS_COMPUTED behaviours"
        #kill $PID
        #echo "Stopped simulation with pid $PID"
        pkill -f tlc

        exit 0
    fi

    if ps -p $PID > /dev/null
    then
        NOW=$(date +%s)
        if [[ $(($NOW - $LAST_PRINTED)) -ge 5 ]]
        then
            echo "$(date +"%H:%M:%S"): Computed $BEHAVIOURS_COMPUTED behaviours"
            LAST_PRINTED=$NOW
        fi
    else
        echo "TLC has exited"
        echo "Computed $BEHAVIOURS_COMPUTED behaviours"
        exit 1
    fi
    
done