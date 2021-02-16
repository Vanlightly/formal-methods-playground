#!/bin/bash

while getopts ":t:p:" opt; do
  case $opt in
    t) TAG="$OPTARG"
    ;;
    p) EC2_PROFILE="$OPTARG"
    ;;
    \?) echo "Invalid option -$OPTARG" >&2
    ;;
  esac
done

INSTANCE_ID=$(aws ec2 describe-instances --profile $EC2_PROFILE --filters "Name=tag:inventorygroup,Values=$TAG" --query "Reservations[*].Instances[*].InstanceId" --output=text)
aws ec2 terminate-instances --instance-ids $INSTANCE_ID