# Analysis of a RabbitMQ Rebalancing Clients Algorithm

## Problem (Domain)

How to get a group of A applications to consume from a group of Q queues, in such a way that:

- each queue is only consumed by one application at a time
- the balance of app->queue assignment is balanced

RabbitMQ does not offer this functionality, but it does have Single-Active-Consumer (SAC). A queue with SAC enabled will allow multiple applications to subscribe at a time, but only one will be actively consuming messages at a time. This feature can be leveraged by cooperating applications to achieve balance.

The completion time of this algorithm can be problematic.

## Simple Algorithm Description

- Each application has the membership of the group of queues and is always ensuring it is subscribed to each queue in that group.
- Each application monitors:
    - How many queues it is active on
    - How many other applications there are.

  With that information, the application calculates the ideal number of queues it should be active on. If it is active on too many queues, it releases queues until it reaches its ideal number.
- Releasing a queue involves cancelling its subscription and resubscribing.
- Each SAC enabled queue will assign active status in First Subscribe, First Active order

## Objective with TLA+


### Objective 1 - Standard Liveness

Ensure it always completes (given that applications don't restart forever). Standard liveness property.

### Objective 2 - Statistical properties as a function of queue and app count

As a function of queue count and app count, calculate statistical properties regarding the number of:

    - total queue releases necessary to achieve balance
    - number of releases per queue necessary to achieve balance

Use simulation mode to generate these metrics that can be turned into csvs with min, max and percentiles per queue/app count combination that can be visualised as charts.

Example charts with 10 queues and variable number of apps:
![](https://github.com/Vanlightly/formal-methods-playground/blob/master/tla/rebalancing-clients/metrics_as_function_of_queue_app_count.png)

## Current state of work

Only the standard liveness variant is truthworthy at this point in folder `standard-liveness`. Various lines of investigation regarding metrics collection are WIP under `liveness-stats`.
