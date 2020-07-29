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

start_time="$(date -u +%s)"
tlc -simulate $SPEC -deadlock -workers $5 -depth 50000 -config $CONFIG -maxSetSize 10000000 > "$OUTPUT" 2>&1 &
PID=$!

echo "Simulation outputting to $OUTPUT, with pid=$PID"

LAST_PRINTED=$(date +%s)
while sleep 1
do
    ERRORS=$(grep -c Exception "$OUTPUT")
    if [[ $COMPLETED -ge $BEHAVIOURS ]]
    then
        echo "Error detected, stopping. Completed $COMPLETED behaviours. Not completed $NOT_COMPLETED behaviours."
        pkill -f tlc
        exit 1
    fi

    COMPLETED=$(grep -c started "$OUTPUT")
    NOT_COMPLETED=$(grep -c stopped "$OUTPUT")
    if [[ $COMPLETED -ge $BEHAVIOURS ]]
    then
        echo "Completed $COMPLETED behaviours"
        echo "Not completed $NOT_COMPLETED behaviours"
        #kill $PID
        #echo "Stopped simulation with pid $PID"
        end_time="$(date -u +%s)"
        elapsed="$(($end_time-$start_time))"
        echo "Total of $elapsed seconds elapsed for process"

        pkill -f tlc

        exit 0
    fi

    if ps -p $PID > /dev/null
    then
        NOW=$(date +%s)
        if [[ $(($NOW - $LAST_PRINTED)) -ge 5 ]]
        then
            echo "$(date +"%H:%M:%S"): Completed $COMPLETED behaviours"
            echo "$(date +"%H:%M:%S"): Not completed $NOT_COMPLETED behaviours"
            LAST_PRINTED=$NOW
        fi
    else
        echo "TLC has exited"
        echo "Completed $COMPLETED behaviours"
        echo "Not completed $NOT_COMPLETED behaviours"
        exit 1
    fi
    
done