#!/bin/bash

set -e

while getopts ":k:e:w:o:b:s:c:t:M:D:S:N:U:I:" opt; do
  case $opt in
    k) KEY_PAIR="$OPTARG"
    ;;
    e) EC2_TAG="$OPTARG"
    ;;
    w) WORKERS="$OPTARG"
    ;;
    o) OUTPUT_DIR="$OPTARG"
    ;;
    b) BEHAVIOURS="$OPTARG"
    ;;
    s) SPEC_NAME="$OPTARG"
    ;;
    c) CONFIG="$OPTARG"
    ;;
    t) TLC_SCRIPT="$OPTARG"
    ;;
    M) MEMBERS="$OPTARG"
    ;;
    D) DEAD="$OPTARG"
    ;;
    S) SUSPECT_TIMEOUT="$OPTARG"
    ;;
    N) DISSEMINATIONS="$OPTARG"
    ;;
    U) MAX_UPDATES_PER_GOSSIP="$OPTARG"
    ;;
    I) DIMENSION="$OPTARG"
    ;;
    \?) echo "Invalid option -$OPTARG" >&2
    ;;
  esac
done


INSTANCE_IP=$(aws ec2 describe-instances --filters "Name=tag:inventorygroup,Values=$EC2_TAG" --query "Reservations[*].Instances[*].PublicIpAddress" --output=text)

SPEC="${SPEC_NAME}.tla"
RUNNER_SPEC="${SPEC_NAME}_runner.tla"
SPEC_OVERRIDES="${SPEC_NAME}.class"

scp -i "~/.ssh/${KEY_PAIR}.pem" "../simulate.py" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "$SPEC_OVERRIDES" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" ${SPEC} ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" ${RUNNER_SPEC} ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" $CONFIG ubuntu@$INSTANCE_IP:.

SPEC_FILE="$(basename -- ${RUNNER_SPEC})"
CFG_FILE="$(basename -- $CONFIG)"
SCRIPT_FILE="$(basename -- $TLC_SCRIPT)"

echo "Running $SPEC_FILE"

ssh -i "~/.ssh/${KEY_PAIR}.pem" ubuntu@$INSTANCE_IP python3 -u simulate.py \
--spec $SPEC_FILE \
--config $CFG_FILE \
--script $SCRIPT_FILE \
--behaviours $BEHAVIOURS \
--output_dir $OUTPUT_DIR \
--workers $WORKERS \
--members $MEMBERS \
--dead $DEAD \
--suspect_timeout $SUSPECT_TIMEOUT \
--disseminations $DISSEMINATIONS \
--max_updates $MAX_UPDATES_PER_GOSSIP \
--dimension $DIMENSION

bash get-results.sh -k $KEY_PAIR -o $OUTPUT_DIR -t $EC2_TAG