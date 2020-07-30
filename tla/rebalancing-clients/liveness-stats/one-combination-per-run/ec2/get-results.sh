#!/bin/bash

while getopts ":k:t:o:" opt; do
  case $opt in
    k) KEY_PAIR="$OPTARG"
    ;;
    t) TAG="$OPTARG"
    ;;
    o) OUTPUT_DIR="$OPTARG"
    ;;
    \?) echo "Invalid option -$OPTARG" >&2
    ;;
  esac
done


INSTANCE_IP=$(aws ec2 describe-instances --filters "Name=tag:inventorygroup,Values=$TAG" --query "Reservations[*].Instances[*].PublicIpAddress" --output=text)

ssh -i "~/.ssh/${KEY_PAIR}.pem" ubuntu@$INSTANCE_IP python3 calculate_stats.py --results_dir results/$OUTPUT_DIR > ${OUTPUT_DIR}.csv

echo "Results in ${OUTPUT_DIR}.csv"