For the specs under:

- `combinations-from-cfg`
- `combinations-from-filtered-subsets`
- `combinations-from-subsets`

use the `simulate.sh` script.

Example generated metrics from 10000 behaviours across the queue-app combinations in cfg:

```
bash simulate.sh combinations-from-cfg/rabbit_leaderless_rebalancing_stats.tla combinations-from-cfg/random.cfg 10000 results.log
```

For the specs under `one-combination-per-run` see the readme there.