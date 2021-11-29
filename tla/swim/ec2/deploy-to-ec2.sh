#!/bin/bash

# Assumes you have your aws cli already configured
# You'll need a security group, subnet already
# This assumes ubuntu 20.04, so get an AMI ID for that in your chosen region
# Make sure your tag is unique for this deployment

while getopts ":a:i:H:S:k:s:n:e:p:" opt; do
  case $opt in
    a) AMI="$OPTARG"
    ;;
    i) INSTANCE_TYPE="$OPTARG"
    ;;
    H) JAVA_HEAP_GB="$OPTARG"
    ;;
    S) JAVA_STACK_MB="$OPTARG"
    ;;
    k) KEY_PAIR="$OPTARG"
    ;;
    s) SG="$OPTARG"
    ;;
    n) SN="$OPTARG"
    ;;
    e) EC2_TAG="$OPTARG"
    ;;
    p) EC2_PROFILE="$OPTARG"
    ;;
    \?) echo "Invalid option -$OPTARG" >&2
    ;;
  esac
done

echo "EC2_TAG=$EC2_TAG. Use this tag for running the simulation and deleting the instance."

aws ec2 run-instances --profile $EC2_PROFILE \
        --image-id "$AMI" \
        --count 1 \
        --instance-type "$INSTANCE_TYPE" \
        --key-name "$KEY_PAIR" \
        --security-group-ids "$SG" \
        --subnet-id "$SN" \
        --tag-specifications "ResourceType=instance,Tags=[{Key=Name,Value=$EC2_TAG},{Key=inventorygroup,Value=$EC2_TAG}]" "ResourceType=volume,Tags=[{Key=Name,Value=$EC2_TAG},{Key=inventorygroup,Value=$EC2_TAG}]"

RUNNING="$(aws ec2 describe-instances --profile $EC2_PROFILE --filters "Name=tag:inventorygroup,Values=$EC2_TAG" "Name=instance-state-name,Values=running" --query "Reservations[*].Instances[*].InstanceId" --output=text)"
while [ -z $RUNNING ]
do
    echo "Instance not ready yet, waiting 5 seconds"
    sleep 5
    RUNNING="$(aws ec2 describe-instances --profile $EC2_PROFILE --filters "Name=tag:inventorygroup,Values=$EC2_TAG" "Name=instance-state-name,Values=running" --query "Reservations[*].Instances[*].InstanceId" --output=text)"
    echo InstanceID=$RUNNING
done

sleep 60

INSTANCE_IP=$(aws ec2 describe-instances --profile $EC2_PROFILE --filters "Name=tag:inventorygroup,Values=$EC2_TAG" "Name=instance-state-name,Values=running" --query "Reservations[*].Instances[*].PublicIpAddress" --output=text)

scp -i "~/.ssh/${KEY_PAIR}.pem" "install.sh" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../simulate.sh" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../simulate-stats-nightly.sh" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../simulate.py" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "../calculate_stats.py" ubuntu@$INSTANCE_IP:.
scp -i "~/.ssh/${KEY_PAIR}.pem" "playlist.sh" ubuntu@$INSTANCE_IP:.

echo "IP=$INSTANCE_IP"
ssh -i "~/.ssh/${KEY_PAIR}.pem" ubuntu@$INSTANCE_IP bash install.sh -Xmx${JAVA_HEAP_GB}G -Xss${JAVA_STACK_MB}M