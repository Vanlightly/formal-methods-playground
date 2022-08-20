# Notes

Ignore this.

tlc-nightly -simulate KafkaRebalancingProtocol3.tla -deadlock -generate -workers 1 -depth 1000

tlc-nightly -simulate KafkaRebalancingProtocol3.tla -config KafkaRebalancingProtocol3Sim.cfg -deadlock -generate -workers 15 -depth 1000

venv/bin/python /home/jack/PycharmProjects/BalancingQueues/CalculatePercentiles.py -g InitNumCts,InitNumCoordMbrs,InitNumRes,InitNumCoordRes,Strategy,StrategyParam,AddRes,RemRes -v Revocations -c ~/stats/kafka/protocol3.csv

venv/bin/python /home/jack/PycharmProjects/BalancingQueues/CreatePercentilesPlot.py -f agg_Revocations__protocol3.csv -s stickyfairsimple -r 40

Next steps:
1. Env vars for parameters instead of constants
2. Run with ranges of parameters
3. Produce aggregated CSVs with percentiles
4. Create charts

1 {1,2,3,4}
2 {5,6,7}
3 {8,9,10}
4 {11,12,13}
5 {14,15,16}
6 {17,18,19}

1 {1,2}
2 {5,6,7}
3 {8,9,10}
4 {11,12,13}
5 {14,15,16}
6 {17,18,19}
7 {3,4}


1 {1,2}      
2 {3,4}
3 {5,6} 
4 {7,8} 
5 {9,10} 
6 {11}
7 {12} 

1 {1,2}
2 {3,4}
3 {5,6}
4 {7,8}
5 {9,10}
6 {11}
7 {12}
8 {2}