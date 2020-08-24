# Stats to add

Metrics:

- Number of rounds of the protocol
- By round
    - Number of updates
    - Number of effective updates
    - Number of members that are suspected
    - Number of members that are considered to be dead
    - Number of suspected states (for example, with 1 dead member and 9 live members, there can be up to 9 suspected state)
    - Number of dead states

As a function of:

- Ensemble size
- Number of failed members
- Max disseminations
- Max updates per gossip
- Suspect timeout


TODO
Probe failure false positives:

- With/without ping req
- Propagation of false state