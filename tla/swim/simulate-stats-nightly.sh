#!/bin/bash

SPEC=$1
CONFIG=$2
BEHAVIOURS=$3
OUTPUT=$4
WORKERS=$5

trap terminate INT

function ensure_no_tlc() {
    COUNT=$(ps aux | grep -v grep | grep tlc2 | wc -l)
    if (( $COUNT > 0 )) ; then
        kill $(ps aux | grep tlc2 | grep -v grep | awk '{ print $2 }')
    fi
}

function terminate() {
    ensure_no_tlc
    exit 0
}

ensure_no_tlc

tlc-nightly -simulate $SPEC -deadlock -workers $5 -depth 100000 -config $CONFIG -maxSetSize 10000000 > "$OUTPUT" 2>&1 &
PID=$!

echo "Simulation outputting to $OUTPUT, with pid=$PID"

LAST_PRINTED=$(date +%s)
while sleep 1
do
    ERRORS=$(grep Exception $OUTPUT | grep -v throws | wc -l)
    if (( $ERRORS > 0 ))
    then
        echo "Error detected, stopping. Computed $BEHAVIOURS_COMPUTED behaviours."
        ensure_no_tlc
        sleep 1
        exit 1
    fi

    BEHAVIOURS_COMPUTED=$(grep -c result "$OUTPUT")
    if [[ $BEHAVIOURS_COMPUTED -ge $BEHAVIOURS ]]
    then
        echo "Computed $BEHAVIOURS_COMPUTED behaviours"
        ensure_no_tlc
        sleep 1
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