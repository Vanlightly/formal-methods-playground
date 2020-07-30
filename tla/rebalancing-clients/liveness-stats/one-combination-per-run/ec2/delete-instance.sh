#!/bin/bash

while getopts ":t:" opt; do
  case $opt in
    t) TAG="$OPTARG"
    ;;
    \?) echo "Invalid option -$OPTARG" >&2
    ;;
  esac
done

INSTANCE_ID=$(aws ec2 describe-instances --filters "Name=tag:inventorygroup,Values=$TAG" --query "Reservations[*].Instances[*].InstanceId" --output=text)
aws ec2 terminate-instances --instance-ids $INSTANCE_ID