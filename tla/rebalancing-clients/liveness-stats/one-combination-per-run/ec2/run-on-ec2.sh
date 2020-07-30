#!/bin/bash

set -e

while getopts ":k:t:w:o:q:a:b:s:c:p:" opt; do
  case $opt in
    k) KEY_PAIR="$OPTARG"
    ;;
    t) TAG="$OPTARG"
    ;;
    w) WORKERS="$OPTARG"
    ;;
    o) OUTPUT_DIR="$OPTARG"
    ;;
    q) QUEUES="$OPTARG"
    ;;
    a) APPS="$OPTARG"
    ;;
    b) BEHAVIOURS="$OPTARG"
    ;;
    s) SPEC="$OPTARG"
    ;;
    c) CONFIG="$OPTARG"
    ;;
    p) ALL_PERMS="$OPTARG"
    ;;
    \?) echo "Invalid option -$OPTARG" >&2
    ;;
  esac
done


INSTANCE_IP=$(aws ec2 describe-instances --filters "Name=tag:inventorygroup,Values=$TAG" --query "Reservations[*].Instances[*].PublicIpAddress" --output=text)

scp -i "~/.ssh/${KEY_PAIR}.pem" $SPEC ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" $CONFIG ubuntu@$INSTANCE_IP:.

SPEC_FILE="$(basename -- $SPEC)"
CFG_FILE="$(basename -- $CONFIG)"

if [[ $ALL_PERMS == "true" ]]
then
    echo "Running with all permuations"

    ssh -i "~/.ssh/${KEY_PAIR}.pem" ubuntu@$INSTANCE_IP python3 -u simulate.py \
    --spec $SPEC_FILE \
    --config $CFG_FILE \
    --behaviours $BEHAVIOURS \
    --queues $QUEUES \
    --app_ratio $APPS \
    --output_dir $OUTPUT_DIR \
    --all_perms $ALL_PERMS \
    --workers $WORKERS 
else
    echo "Running with with $QUEUES queues and $APPS apps" 

    ssh -i "~/.ssh/${KEY_PAIR}.pem" ubuntu@$INSTANCE_IP python3 -u simulate.py \
    --spec $SPEC_FILE \
    --config $CFG_FILE \
    --behaviours $BEHAVIOURS \
    --queues $QUEUES \
    --apps $APPS \
    --output_dir $OUTPUT_DIR \
    --all_perms $ALL_PERMS \
    --workers $WORKERS 
fi

bash get-results.sh -k $KEY_PAIR -o $OUTPUT_DIR -t $TAG