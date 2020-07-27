#!/bin/bash

# we add the deadlock flag because this spec is designed to run
# until balance is achieved (which is when it will deadlock)

tlc rabbit_leaderless_rebalancing.tla -deadlock