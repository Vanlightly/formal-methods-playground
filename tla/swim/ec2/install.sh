#!/bin/bash

sudo apt update
sudo apt install default-jre -y

git clone https://github.com/vanlightly/tla-bin.git
cd tla-bin
bash download_or_update_tla.sh

echo "Extra Java options: $1 $2"
sudo bash install.sh $1 $2