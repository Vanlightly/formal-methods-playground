#!/bin/bash

set -e

SPEC_FILE=$1
CFG_FILE=$2
SCRIPT_FILE=$3
OUTPUT_DIR=$4
BEHAVIOURS=$5
WORKERS=$6

# echo ""
# echo "-----------------------------------------"
# echo "# Detection of dead members"
# echo "-----------------------------------------"
# echo "## Experiment 1: Number of undetected dead as dimension"
# echo "### Variant 2 - Peer Group Size=1"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 dead --output_dir $OUTPUT_DIR/dead_dim_dead_v2_pg1 --workers $WORKERS --members 20 --dead 18 \
# --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 \
# --force_to_round 0

# echo "### Variant 2 - Peer Group Size=2"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 dead --output_dir $OUTPUT_DIR/dead_dim_dead_v2_pg2 --workers $WORKERS --members 20 --dead 18 \
# --new 0 --initial_contact 0 --peer_group_size 2 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 \
# --force_to_round 0

# echo "### Variant 2 - Peer Group Size=3"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 dead --output_dir $OUTPUT_DIR/dead_dim_dead_v2_pg3 --workers $WORKERS --members 20 --dead 18 \
# --new 0 --initial_contact 0 --peer_group_size 2 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 \
# --force_to_round 0

# echo "### Variant 3 - Peer Group Size=1, Suspect timeout=10"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 dead --output_dir $OUTPUT_DIR/dead_dim_dead_v3_pg1_st10 --workers $WORKERS --members 20 --dead 18 \
# --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 10 --disseminations 4 --max_updates 6 --lose_every_nth 0 \
# --force_to_round 0


# echo "## Experiment 2: Ensemble size as dimension"
# echo "### Variant 2 - Peer Group Size=1, Dead=1"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 members --output_dir $OUTPUT_DIR/dead_dim_members_v2_pg1 --workers $WORKERS --members 20 --dead 1 \
# --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 \
# --force_to_round 0

# echo "### Variant 3 - Peer Group Size=1"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 members --output_dir $OUTPUT_DIR/dead_dim_members_v3_pg1_st10 --workers $WORKERS --members 20 \
# --dead 1 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 10 --disseminations 4 --max_updates 6 \
# --lose_every_nth 0 --force_to_round 0

# echo "## Experiment 3: Max disseminations as dimension"
# echo "### Variant 2 - Peer Group Size=1, Dead=10"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 disseminations --output_dir $OUTPUT_DIR/dead_dim_disseminations_v2_pg1 --workers $WORKERS \
# --members 20 --dead 10 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 10 \
# --max_updates 6 --lose_every_nth 0 --force_to_round 0

# echo "### Variant 3 - Peer Group Size=1, Dead=10"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 disseminations --output_dir $OUTPUT_DIR/dead_dim_disseminations_v3_pg1_st10 --workers $WORKERS \
# --members 20 --dead 10 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 10 --disseminations 10 \
# --max_updates 6 --lose_every_nth 0 --force_to_round 0

# echo "## Experiment 4: Max updates per message as dimension"
# echo "### Variant 2 - Peer Group Size=1, Dead=10"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 max_updates --output_dir $OUTPUT_DIR/dead_dim_max_updates_v2_pg1 --workers $WORKERS --members 20 \
# --dead 10 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 10 \
# --lose_every_nth 0 --force_to_round 0

# echo "### Variant 3 - Peer Group Size=1, Dead=10"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 max_updates --output_dir $OUTPUT_DIR/dead_dim_max_updates_v3_pg1_st10 --workers $WORKERS \
# --members 20 --dead 10 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 10 --disseminations 4 \
# --max_updates 10 --lose_every_nth 0 --force_to_round 0

# echo ""
# echo "-----------------------------------------"
# echo "# Detection of joining members"
# echo "-----------------------------------------"
# echo "## Experiment 1: Number of undetected new as dimension"
# echo "### Variant 2/3 - Initial contacts=1"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 new --output_dir $OUTPUT_DIR/new_dim_new_ic1 --workers $WORKERS --members 20 --dead 0 --new 18 \
# --initial_contact 1 --peer_group_size 1 --suspect_timeout 0 --disseminations 20 --max_updates 6 --lose_every_nth 0 \
# --force_to_round 0

# echo "## Experiment 2: Ensemble size as dimension"
# echo "### Variant 2/3 - Initial contacts=1"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 members --output_dir $OUTPUT_DIR/new_dim_members_ic1 --workers $WORKERS --members 20 --dead 0 \
# --new 1 --initial_contact 1 --peer_group_size 1 --suspect_timeout 0 --disseminations 20 --max_updates 6 --lose_every_nth 0 \
# --force_to_round 0

# echo "## Experiment 3: Max disseminations as dimension"
# echo "### Variant 2/3 - Initial contacts=1, New=1"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 disseminations --output_dir $OUTPUT_DIR/new_dim_disseminations_ic1_new1 --workers $WORKERS \
# --members 20 --dead 0 --new 1 --initial_contact 1 --peer_group_size 1 --suspect_timeout 0 --disseminations 20 \
# --max_updates 6 --lose_every_nth 0 --force_to_round 0

# echo "### Variant 2/3 - Initial contacts=1, New=10"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 disseminations --output_dir $OUTPUT_DIR/new_dim_disseminations_ic1_new10 --workers $WORKERS \
# --members 20 --dead 0 --new 10 --initial_contact 1 --peer_group_size 1 --suspect_timeout 0 --disseminations 15 \
# --max_updates 6 --lose_every_nth 0 --force_to_round 0

# echo "## Experiment 4: Max updates per message as dimension"
# echo "### Variant 2/3 - Initial contacts=1, New=10"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 max_updates --output_dir $OUTPUT_DIR/new_dim_max_updates_ic1 --workers $WORKERS --members 20 \
# --dead 0 --new 10 --initial_contact 1 --peer_group_size 1 --suspect_timeout 0 --disseminations 20 --max_updates 10 \
# --lose_every_nth 0 --force_to_round 0

# echo "## Experiment 5: Initial contacts as dimension"
# echo "### Variant 2/3 - New=1, Disseminations=5"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 initial_contact --output_dir $OUTPUT_DIR/new_dim_initial_contact_ic19_dis5 --workers $WORKERS \
# --members 20 --dead 0 --new 1 --initial_contact 19 --peer_group_size 1 --suspect_timeout 0 --disseminations 5 \
# --max_updates 6 --lose_every_nth 0 --force_to_round 0

# echo "### Variant 2/3 - New=1, Disseminations=20"
# python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
# --behaviours $BEHAVIOURS --dimension1 initial_contact --output_dir $OUTPUT_DIR/new_dim_initial_contact_ic19_dis20 --workers $WORKERS \
# --members 20 --dead 0 --new 1 --initial_contact 19 --peer_group_size 1 --suspect_timeout 0 --disseminations 20 \
# --max_updates 6 --lose_every_nth 0 --force_to_round 0

echo ""
echo "-----------------------------------------"
echo "# Propagation of false state"
echo "-----------------------------------------"
echo "## Experiment 1 - Impact of message loss"
echo "### Variant 2 - Peer Group Size=1, dimension=lose-every-nth"
python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
--behaviours $BEHAVIOURS --dimension1 lose_every_nth --output_dir $OUTPUT_DIR/false_dead_dim_lose_v2_pg1 --workers $WORKERS \
--members 20 --dead 0 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 \
--max_updates 6 --lose_every_nth 20-3 --force_to_round 40

echo "### Variant 2 - Peer Group Size=2, dimension=lose-every-nth"
python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
--behaviours $BEHAVIOURS --dimension1 lose_every_nth --output_dir $OUTPUT_DIR/false_dead_dim_lose_v2_pg2 --workers $WORKERS \
--members 20 --dead 0 --new 0 --initial_contact 0 --peer_group_size 2 --suspect_timeout 0 --disseminations 4 \
--max_updates 6 --lose_every_nth 20-3 --force_to_round 40

echo "### Variant 2 - Peer Group Size=3, dimension=lose-every-nth"
python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
--behaviours $BEHAVIOURS --dimension1 lose_every_nth --output_dir $OUTPUT_DIR/false_dead_dim_lose_v2_pg3 --workers $WORKERS \
--members 20 --dead 0 --new 0 --initial_contact 0 --peer_group_size 3 --suspect_timeout 0 --disseminations 4 --max_updates 6 \
--lose_every_nth 20-3 --force_to_round 40

echo "### Variant 3 - Peer Group Size=1, Suspect Timeout=10, dimension=lose-every-nth"
python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
--behaviours $BEHAVIOURS --dimension1 lose_every_nth --output_dir $OUTPUT_DIR/false_dead_dim_lose_v3_pg1_st10 --workers $WORKERS \
--members 20 --dead 0 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 10 --disseminations 4 \
--max_updates 6 --lose_every_nth 20-3 --force_to_round 40

echo "## Experiment 2 - Impact of suspect timeout"
echo "### Variant 3 - Peer Group Size=1, Lose-every-nth=5, dimension=suspect-timeout"
python3 -u  simulate.py --spec $SPEC_FILE --config $CFG_FILE --script $SCRIPT_FILE \
--behaviours $BEHAVIOURS --dimension1 suspect_timeout --output_dir $OUTPUT_DIR/false_dead_dim_suspect_v3_pg1 --workers $WORKERS \
--members 20 --dead 0 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 20 --disseminations 4 \
--max_updates 6 --lose_every_nth 5 --force_to_round 40