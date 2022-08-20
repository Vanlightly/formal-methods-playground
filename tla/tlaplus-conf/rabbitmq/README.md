TODO

Example with default values of a sequential start.

Run the simulation for a while. It has 118 initial states so you'll want at least 118,000 traces for decent plots. It prints out the trace count as it goes.

```
cd rabbitmq
./run.sh ConfigSequentialStart.cfg <number of workers>
```

Do some aggregations for the percentiles plots.

```
cd ..
./aggregate-rabbitmq-variants.sh Sequential20
```

Run the notebook RabbitMQNotebookVariants.Rmd to see the plots.

You may need to ensure that the directories `rabbitmq/results/raw` and `rabbitmq/results/aggregated` exist.