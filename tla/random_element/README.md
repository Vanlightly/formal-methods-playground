# Testing RandomElement vs non-determinism in simulation mode

Testing shows that using RandomElement with model checking mode can greatly reduce running time by reducing the state space of any given execution.

However, when run in simulation mode, it is much slower than using a non-deterministic approach.

Two examples:

1. Single variable test - Applications start until all are started. 
    - `test_non_det.tla` uses non-determinism (`\E a \in A : cond etc`)
    - `test_random_element.tla` uses RandomElement to choose the next app to start.
2. Two dependent variables - Applications start until all are started and assignments are made to started applications
    - `test_dependent_vars_non_det.tla` uses non-determinism (`\E a \in A : cond etc`)
    - `test_dependent_vars_random_element.tla` uses RandomElement to choose either the next app to start, or the next assignment.

You can run all 4 specs with the `run.sh` script. Example output:

```
Runs specs with simulation mode until 100000 behaviours have been generated.
Each behaviour is either completed, or not completed.
Improper use of RandomElement can cause behaviours to terminate before successfully completing

---------------------------------------------------------------------
SINGLE VARIABLE TEST ----------------------------------------
SIMULATION MODE WITH NON-DETERMINISM
Simulation outputting to test_tmp, with pid=10423
06:37:58: Completed 49141 behaviours
06:37:58: Not completed 0 behaviours
Completed 104464 behaviours
Not completed 0 behaviours
Total of 9 seconds elapsed for process

SIMULATION MODE WITH RandomElement
Simulation outputting to test_tmp, with pid=10727
06:38:08: Completed 18913 behaviours
06:38:08: Not completed 0 behaviours
06:38:13: Completed 44491 behaviours
06:38:13: Not completed 0 behaviours
06:38:18: Completed 70421 behaviours
06:38:18: Not completed 0 behaviours
06:38:23: Completed 96083 behaviours
06:38:23: Not completed 0 behaviours
Completed 101293 behaviours
Not completed 0 behaviours
Total of 22 seconds elapsed for process

---------------------------------------------------------------------
TWO DEPENDENT VARIABLES TEST ----------------------------------------
SIMULATION MODE WITH NON-DETERMINISM
Simulation outputting to test_tmp, with pid=11022
06:38:29: Completed 5849 behaviours
06:38:29: Not completed 0 behaviours
06:38:34: Completed 12751 behaviours
06:38:34: Not completed 0 behaviours
06:38:39: Completed 20262 behaviours
06:38:39: Not completed 0 behaviours
...omitted lines
06:39:19: Completed 78424 behaviours
06:39:19: Not completed 0 behaviours
06:39:24: Completed 85775 behaviours
06:39:24: Not completed 0 behaviours
06:39:29: Completed 93104 behaviours
06:39:29: Not completed 0 behaviours
06:39:34: Completed 98987 behaviours
06:39:34: Not completed 0 behaviours
Completed 100491 behaviours
Not completed 0 behaviours
Total of 71 seconds elapsed for process

SIMULATION MODE WITH RandomElement
Simulation outputting to test_tmp, with pid=12379
06:39:40: Completed 1453 behaviours
06:39:40: Not completed 0 behaviours
06:39:45: Completed 3389 behaviours
06:39:45: Not completed 0 behaviours
06:39:50: Completed 5290 behaviours
06:39:50: Not completed 0 behaviours
06:39:55: Completed 7217 behaviours
06:39:55: Not completed 0 behaviours
06:40:00: Completed 9146 behaviours
06:40:00: Not completed 0 behaviours
...omitted lines
06:43:47: Completed 94308 behaviours
06:43:47: Not completed 0 behaviours
06:43:52: Completed 96235 behaviours
06:43:52: Not completed 0 behaviours
06:43:57: Completed 97763 behaviours
06:43:57: Not completed 0 behaviours
06:44:02: Completed 99689 behaviours
06:44:02: Not completed 0 behaviours
Completed 100064 behaviours
Not completed 0 behaviours
Total of 268 seconds elapsed for process

```