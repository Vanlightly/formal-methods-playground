#!/bin/bash

while getopts ":k:t:o:p:" opt; do
  case $opt in
    k) KEY_PAIR="$OPTARG"
    ;;
    t) TAG="$OPTARG"
    ;;
    o) OUTPUT_DIR="$OPTARG"
    ;;
    p) EC2_PROFILE="$OPTARG"
    ;;
    \?) echo "Invalid option -$OPTARG" >&2
    ;;
  esac
done


INSTANCE_IP=$(aws ec2 describe-instances --profile $EC2_PROFILE --filters "Name=tag:inventorygroup,Values=$TAG" --query "Reservations[*].Instances[*].PublicIpAddress" --output=text)

scp -i "~/.ssh/${KEY_PAIR}.pem" "../calculate_stats.py" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../RoundStats.py" ubuntu@$INSTANCE_IP:.

ssh -i "~/.ssh/${KEY_PAIR}.pem" ubuntu@$INSTANCE_IP tar -zcvf results.tar.gz results/$OUTPUT_DIR
scp -i "~/.ssh/${KEY_PAIR}.pem" ubuntu@$INSTANCE_IP:results.tar.gz ./results.tar.gz
ssh -i "~/.ssh/${KEY_PAIR}.pem" ubuntu@$INSTANCE_IP python3 calculate_stats.py --results_dir results/$OUTPUT_DIR > ${OUTPUT_DIR}.csv

echo "Results in ${OUTPUT_DIR}.csv"