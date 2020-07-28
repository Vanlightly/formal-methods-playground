Strategy to gather stats from all combinations of queue and app count is to randomly pick one set per cardinality of queue and app sets.

This also produces a flat distribution of combinations which is what we want.

## Non-determinism

Tried using RandomElement but having issues with "operator not defined".