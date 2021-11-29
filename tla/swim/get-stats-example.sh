#!/bin/bash

set -e

SPEC_FILE="swim_stats_runner.tla"
CFG_FILE="swim_stats_template.cfg"
SCRIPT_FILE="simulate-stats-nightly.sh"
RAW_OUTPUT_DIR="$(pwd)/results"
ANALYSIS_OUTPUT_DIR="$(pwd)/analysis"
BEHAVIOURS=1000
WORKERS=4

python3 -u simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
--behaviours $BEHAVIOURS --dimension1 none --output_dir $RAW_OUTPUT_DIR/dead_v2_pg1_mem4 --workers $WORKERS --members 4 --dead 1 \
--new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 \
--force_to_round 0

python3 -u calculate_stats.py --raw_output_dir $RAW_OUTPUT_DIR/dead_v2_pg1_mem4 --analysis_dir $ANALYSIS_OUTPUT_DIR