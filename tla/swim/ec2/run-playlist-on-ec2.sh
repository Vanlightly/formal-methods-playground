#!/bin/bash

set -e

while getopts ":k:e:w:o:b:s:c:t:p:" opt; do
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
    p) EC2_PROFILE="$OPTARG"
    ;;
    \?) echo "Invalid option -$OPTARG" >&2
    ;;
  esac
done


INSTANCE_IP=$(aws ec2 describe-instances --profile $EC2_PROFILE --filters "Name=tag:inventorygroup,Values=$EC2_TAG" --query "Reservations[*].Instances[*].PublicIpAddress" --output=text)

SPEC="${SPEC_NAME}.tla"
RUNNER_SPEC="${SPEC_NAME}_runner.tla"
SPEC_OVERRIDES="${SPEC_NAME}.class"

scp -i "~/.ssh/${KEY_PAIR}.pem" "../simulate.py" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../${SPEC_OVERRIDES}" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../${SPEC}" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../${RUNNER_SPEC}" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../${CONFIG}" ubuntu@$INSTANCE_IP:.

SPEC_FILE="$(basename -- ${RUNNER_SPEC})"
CFG_FILE="$(basename -- $CONFIG)"
SCRIPT_FILE="$(basename -- $TLC_SCRIPT)"

echo "Running $SPEC_FILE"

ssh -i "~/.ssh/${KEY_PAIR}.pem" ubuntu@$INSTANCE_IP bash playlist.sh \
$SPEC_FILE \
$CFG_FILE \
$SCRIPT_FILE \
$OUTPUT_DIR \
$BEHAVIOURS \
$WORKERS

bash get-results.sh -k $KEY_PAIR -o $OUTPUT_DIR -t $EC2_TAG -p $EC2_PROFILE