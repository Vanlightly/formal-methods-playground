# Obtaining statistical properties of the SWIM protocol variants 2 and 3

## Metrics:

- Number of rounds of the protocol
- By round
    - Number of messages per protocol period
    - Number of updates
    - Number of effective updates (when an update is new to the recipient)
    - Number of members that are considered alive by at least one peer
    - Number of members that are considered suspect by at least one peer
    - Number of members that are considered dead by at least one peer
    - Number of suspected states (for example, with 1 dead member and 9 live members, there can be up to 9 suspected states)
    - Number of dead states
    - Number of alive states

## Configurable Parameters

### Common

- Ensemble size
- Max disseminations (when an item of information stops being infective)
- Max updates per message
- Peer group size (the number of peers to send probe requests)
- Suspect timeout. Variant 2 uses value of 0. Variant 3 uses value > 0.
- Message loss mode.
    - none = no message loss
    - exhaustive = For model checking mode where every message is both delivered and lost
    - probabilistic = Configurable probability of each message being lost

### Specific to an analysis

- Number of undetected dead members in initial state (for dead detection analysis)
- Number of undetected new members in initial state (for membership join detection analysis)
- Message loss mode and probability (for false state propagation analysis)


## Analyses

### Message load

The number of messages sent per round.

Experiment 1: All alive, no message loss
Experiment 2: All alive, message loss
Experiment 3: Some dead, no message loss
Experiment 4: Some new, no message loss

### Detection of dead members

Run until to convergence - collect metrics.

#### Experiment 1: Number of undetected dead as dimension

20 members, with 1-18 dead as the dimension.

##### Variant 2 - Peer Group Size=1
python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 dead --output_dir dead_dim_dead_v2_pg1 --workers $WORKERS --members 20 --dead 18 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 --force_to_round 0

##### Variant 2 - Peer Group Size=2
python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 dead --output_dir dead_dim_dead_v2_pg2 --workers $WORKERS --members 20 --dead 18 --new 0 --initial_contact 0 --peer_group_size 2 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 --force_to_round 0

##### Variant 2 - Peer Group Size=3
python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 dead --output_dir dead_dim_dead_v2_pg3 --workers $WORKERS --members 20 --dead 18 --new 0 --initial_contact 0 --peer_group_size 2 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 --force_to_round 0

##### Variant 3 - Peer Group Size=1, Suspect timeout=10
python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 dead --output_dir dead_dim_dead_v3_pg1_st10 --workers $WORKERS --members 20 --dead 18 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 10 --disseminations 4 --max_updates 6 --lose_every_nth 0 --force_to_round 0


#### Experiment 2: Ensemble size as dimension

##### Variant 2 - Peer Group Size=1, Dead=1
python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 members --output_dir dead_dim_members_v2_pg1 --workers $WORKERS --members 20 --dead 1 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 --force_to_round 0

##### Variant 3 - Peer Group Size=1
python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 members --output_dir dead_dim_members_v3_pg1_st10 --workers $WORKERS --members 20 --dead 1 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 10 --disseminations 4 --max_updates 6 --lose_every_nth 0 --force_to_round 0

#### Experiment 3: Max disseminations as dimension

##### Variant 2 - Peer Group Size=1, Dead=10

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 disseminations --output_dir dead_dim_disseminations_v2_pg1 --workers $WORKERS --members 20 --dead 10 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 10 --max_updates 6 --lose_every_nth 0 --force_to_round 0

##### Variant 3 - Peer Group Size=1, Dead=10

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 disseminations --output_dir dead_dim_disseminations_v3_pg1_st10 --workers $WORKERS --members 20 --dead 10 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 10 --disseminations 10 --max_updates 6 --lose_every_nth 0 --force_to_round 0

#### Experiment 4: Max updates per message as dimension

##### Variant 2 - Peer Group Size=1, Dead=10

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 max_updates --output_dir dead_dim_max_updates_v2_pg1 --workers $WORKERS --members 20 --dead 10 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 10 --lose_every_nth 0 --force_to_round 0

##### Variant 3 - Peer Group Size=1, Dead=10

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 max_updates --output_dir dead_dim_max_updates_v3_pg1_st10 --workers $WORKERS --members 20 --dead 10 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 10 --disseminations 4 --max_updates 10 --lose_every_nth 0 --force_to_round 0

### Detection of joining members

#### Experiment 1: Number of undetected new as dimension

20 members, with 1-18 new as the dimension.

##### Variant 2/3 - Initial contacts=1

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 new --output_dir new_dim_new_ic1 --workers $WORKERS --members 20 --dead 0 --new 18 --initial_contact 1 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 --force_to_round 0

#### Experiment 2: Ensemble size as dimension

##### Variant 2/3 - Initial contacts=1

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 members --output_dir new_dim_members_ic1 --workers $WORKERS --members 20 --dead 0 --new 1 --initial_contact 1 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 --force_to_round 0

#### Experiment 3: Max disseminations as dimension

##### Variant 2/3 - Initial contacts=1, New=10

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 disseminations --output_dir new_dim_disseminations_ic1 --workers $WORKERS --members 20 --dead 0 --new 10 --initial_contact 1 --peer_group_size 1 --suspect_timeout 0 --disseminations 10 --max_updates 6 --lose_every_nth 0 --force_to_round 0

#### Experiment 4: Max updates per message as dimension

##### Variant 2/3 - Initial contacts=1, New=10

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 max_updates --output_dir new_dim_max_updates_ic1 --workers $WORKERS --members 20 --dead 0 --new 10 --initial_contact 1 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 10 --lose_every_nth 0 --force_to_round 0

#### Experiment 5: Initial contacts as dimension

##### Variant 2/3 - New=10

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 initial_contact --output_dir new_dim_initial_contact_ic10 --workers $WORKERS --members 20 --dead 0 --new 10 --initial_contact 10 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 0 --force_to_round 0

### Propagation of false state

Run until to convergence on false dead states or a maximum round count.

#### Experiment 1 - Impact of message loss

##### Variant 2 - Peer Group Size=1, dimension=lose-every-nth

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 lose_every_nth --output_dir false_dead_dim_lose_v2_pg1 --workers $WORKERS --members 20 --dead 0 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 20-3 --force_to_round 40

##### Variant 2 - Peer Group Size=2, dimension=lose-every-nth

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 lose_every_nth --output_dir false_dead_dim_lose_v2_pg2 --workers $WORKERS --members 20 --dead 0 --new 0 --initial_contact 0 --peer_group_size 2 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 20-3 --force_to_round 40

##### Variant 2 - Peer Group Size=3, dimension=lose-every-nth

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 lose_every_nth --output_dir false_dead_dim_lose_v2_pg3 --workers $WORKERS --members 20 --dead 0 --new 0 --initial_contact 0 --peer_group_size 3 --suspect_timeout 0 --disseminations 4 --max_updates 6 --lose_every_nth 20-3 --force_to_round 40

##### Variant 3 - Peer Group Size=1, Suspect Timeout=10, dimension=lose-every-nth

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 lose_every_nth --output_dir false_dead_dim_lose_v3_pg1_st10 --workers $WORKERS --members 20 --dead 0 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 10 --disseminations 4 --max_updates 6 --lose_every_nth 20-3 --force_to_round 40

#### Experiment 2 - Impact of suspect timeout

##### Variant 3 - Peer Group Size=1, Lose-every-nth=5, dimension=suspect-timeout

python3.6 simulate.py --spec swim_stats_runner.tla --config swim_stats_template.cfg --script simulate-stats-nightly.sh --behaviours $BEHAVIOURS --dimension1 suspect_timeout --output_dir false_dead_dim_suspect_v3_pg1 --workers $WORKERS --members 20 --dead 0 --new 0 --initial_contact 0 --peer_group_size 1 --suspect_timeout 20 --disseminations 4 --max_updates 6 --lose_every_nth 5 --force_to_round 40