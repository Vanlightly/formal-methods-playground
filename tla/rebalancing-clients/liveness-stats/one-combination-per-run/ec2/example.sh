#!/bin/bash

# set the variables for SG and SN or replace in this file

# ubuntu 20.04 in eu-west-1
AMI=ami-0dad359ff462124ca

bash deploy-to-ec2.sh -k my-pem -t TLA -i c5.4xlarge -s $SG -n $SN -a $AMI

bash run-on-ec2.sh \
-k my-pem \
-t TLA \
-w 12 \
-o run1 \
-q 20 \
-a 1.5 \
-b 1000 \
-s ../rabbit_leaderless_rebalancing_stats.tla \
-c ../random_template.cfg