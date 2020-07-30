#!/bin/bash

# Assumes you have your aws cli already configured
# You'll need a security group, subnet already
# This assumes ubuntu 20.04, so get an AMI ID for that in your chosen region
# Make sure your tag is unique for this deployment

while getopts ":a:i:k:s:n:t:" opt; do
  case $opt in
    a) AMI="$OPTARG"
    ;;
    i) INSTANCE_TYPE="$OPTARG"
    ;;
    k) KEY_PAIR="$OPTARG"
    ;;
    s) SG="$OPTARG"
    ;;
    n) SN="$OPTARG"
    ;;
    t) TAG="$OPTARG"
    ;;
    \?) echo "Invalid option -$OPTARG" >&2
    ;;
  esac
done

echo "TAG=$TAG. Use this tag for running the simulation and deleting the instance."

aws ec2 run-instances \
        --image-id "$AMI" \
        --count 1 \
        --instance-type "$INSTANCE_TYPE" \
        --key-name "$KEY_PAIR" \
        --security-group-ids "$SG" \
        --subnet-id "$SN" \
        --tag-specifications "ResourceType=instance,Tags=[{Key=Name,Value=$TAG},{Key=inventorygroup,Value=$TAG}]" "ResourceType=volume,Tags=[{Key=Name,Value=$TAG},{Key=inventorygroup,Value=$TAG}]"

RUNNING="$(aws ec2 describe-instances --filters "Name=tag:inventorygroup,Values=$TAG" "Name=instance-state-name,Values=running" --query "Reservations[*].Instances[*].InstanceId" --output=text)"
while [ -z $RUNNING ]
do
    echo "Instance not ready yet, waiting 5 seconds"
    sleep 5
    RUNNING="$(aws ec2 describe-instances --filters "Name=tag:inventorygroup,Values=$TAG" "Name=instance-state-name,Values=running" --query "Reservations[*].Instances[*].InstanceId" --output=text)"
    echo InstanceID=$RUNNING
done

sleep 30

INSTANCE_IP=$(aws ec2 describe-instances --filters "Name=tag:inventorygroup,Values=$TAG" "Name=instance-state-name,Values=running" --query "Reservations[*].Instances[*].PublicIpAddress" --output=text)

scp -i "~/.ssh/${KEY_PAIR}.pem" "install.sh" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../simulate.sh" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../simulate.py" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../calculate_stats.py" ubuntu@$INSTANCE_IP:.

ssh -i "~/.ssh/${KEY_PAIR}.pem" ubuntu@$INSTANCE_IP bash install.sh