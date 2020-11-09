import java.util.HashMap;
import java.util.Map;

import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.Value;

public class swim_stats {

	/*
	IsConverged(inc, pstates, nil, dead_state, alive_state) ==
		\A member \in Member :
			\A peer \in Member :
				\/ inc[peer] = nil
				\/ member = peer
				\/ /\ member # peer
				   /\ \/ pstates[peer][member].state = RealStateOfMember(member, nil, dead_state, alive_state)
					  \/ pstates[peer][member].state = DeadState
	 */
	public static Value IsConverged(final FcnRcdValue inc,
									final FcnRcdValue tps,
									final IntValue nil,
									final IntValue deadState,
									final IntValue aliveState) {
		assert inc.isNormalized();
		assert tps.isNormalized();

		final Value[] domain = tps.domain;
		for (int member = 0; member < domain.length; member++) {
			final int realState = inc.values[member].equals(nil) ? deadState.val : aliveState.val;
			int real = 0;
			int dead = 0;
			int livePeers = 0;

			for (int peer = 0; peer < domain.length; peer++) {
				if(member == peer)
					continue;

				final IntValue incarn = (IntValue) inc.values[peer];
				if(incarn.equals(nil))
					continue;

				livePeers++;

				final FcnRcdValue frv = (FcnRcdValue) tps.values[peer];
				final RecordValue rv = (RecordValue) frv.values[member];
				int stateIndex = 0;
				for (int n=0; n< rv.names.length; n++) {
					if(rv.names[n].equals("state")) {
						stateIndex = n;
						break;
					}
				}

				final IntValue s = (IntValue) rv.values[stateIndex];
				if (s.val == realState)
					real++;
				else if (s.val == deadState.val)
					dead++;
			}

			boolean convergedForMember = (real == livePeers && dead == 0) || (real == 0 && dead == livePeers);
			if(!convergedForMember)
				return new BoolValue(false);
		}

		return new BoolValue(true);
	}

	/*
StateCount(state, target_peer_states) ==
    LET pairs == { s \in SUBSET Member : Cardinality(s) = 2 }
    IN
    LET lower_to_higher == Cardinality({s \in pairs :
                                            \E m1, m2 \in s : 
                                                /\ target_peer_states[m1][m2].state = state
                                                /\ m1 < m2})
        higher_to_lower == Cardinality({s \in pairs :
                                            \E m1, m2 \in s : 
                                                /\ target_peer_states[m1][m2].state = state
                                                /\ m1 > m2})
    IN lower_to_higher + higher_to_lower
	 */
	public static Value StateCount(final IntValue state, final FcnRcdValue tps) {
		assert tps.isNormalized();

		int lowToHigh = 0;
		int highToLow = 0;

		final Value[] domain = tps.domain;
		for (int i = 0; i < domain.length; i++) {
			final IntValue di = (IntValue) domain[i];
			for (int j = 0; j < domain.length; j++) {
				final IntValue dj = (IntValue) domain[j];
				int compare = Integer.compare(di.val, dj.val);
				if (compare < 0) {
					final FcnRcdValue frv = (FcnRcdValue) tps.values[i];
					final RecordValue rv = (RecordValue) frv.values[j];

					int stateIndex = 0;
					for (int n=0; n< rv.names.length; n++) {
						if(rv.names[n].equals("state")) {
							stateIndex = n;
							break;
						}
					}

					final IntValue s = (IntValue) rv.values[stateIndex];
					if (s.val == state.val) {
						lowToHigh++;
					}
				} else if (compare > 0) {
					final FcnRcdValue frv = (FcnRcdValue) tps.values[i];
					final RecordValue rv = (RecordValue) frv.values[j];

					int stateIndex = 0;
					for (int n=0; n< rv.names.length; n++) {
						if(rv.names[n].equals("state")) {
							stateIndex = n;
							break;
						}
					}

					final IntValue s = (IntValue) rv.values[stateIndex];
					if (s.val == state.val) {
						highToLow++;
					}
				}
			}
		}
		return IntValue.gen(lowToHigh + highToLow);
	}

	/*
MemberCount(state, target_peer_states) ==
    Cardinality({dest \in Member :
        \E source \in Member :
            target_peer_states[source][dest].state = state})
	 */
	public static Value MemberCount(final IntValue state, final FcnRcdValue tps) {
		assert tps.isNormalized();

		int count = 0;

		final Value[] domain = tps.domain;
		for (int member = 0; member < domain.length; member++) {
			for (int peer = 0; peer < domain.length; peer++) {
				if(member == peer)
					continue;
				final FcnRcdValue frv = (FcnRcdValue) tps.values[peer];
				final RecordValue rv = (RecordValue) frv.values[member];
				int stateIndex = 0;
				for (int n=0; n< rv.names.length; n++) {
					if(rv.names[n].equals("state")) {
						stateIndex = n;
						break;
					}
				}

				final IntValue s = (IntValue) rv.values[stateIndex];
				if (s.val == state.val) {
					count++;
					break; // we just need at least one peer to believe the member is in this state
				}
			}
		}

		return IntValue.gen(count);
	}


	/*
MemberThinksEveryoneIsDead(member, mem, pstates, dead_state) ==
	\A m1 \in mem : m1 = member \/ pstates[member][m1].state = dead_state

IsNewRoundTransitionStep(inc, r1, r2, nil, mem, pstates, dead_state) ==
    /\ \E m \in mem : r1[m] # r2[m]
    /\ \/ Cardinality({m \in mem : ~MemberThinksEveryoneIsDead(m, mem, pstates, dead_state)}) = 1
       \/ /\ \E m1, m2 \in mem: /\ inc[m1] # nil
                                /\ inc[m2] # nil
                                /\ ~MemberThinksEveryoneIsDead(m1, mem, pstates, dead_state)
                                /\ ~MemberThinksEveryoneIsDead(m2, mem, pstates, dead_state)
                                /\ r1[m1] # r1[m2]
          /\ \A m3, m4 \in mem:
            \/ inc[m3] = Nil
            \/ inc[m4] = Nil
            \/ MemberThinksEveryoneIsDead(m3, mem, pstates, dead_state)
            \/ MemberThinksEveryoneIsDead(m4, mem, pstates, dead_state)
            \/ /\ inc[m3] # nil
               /\ inc[m4] # nil
               /\ ~MemberThinksEveryoneIsDead(m3, mem, pstates, dead_state)
               /\ ~MemberThinksEveryoneIsDead(m4, mem, pstates, dead_state)
               /\ r2[m3] = r2[m4]
	 */
	public static Value IsNewRoundTransitionStep(final FcnRcdValue inc,
												 final FcnRcdValue r1,
												 final FcnRcdValue r2,
												 final IntValue nil,
												 final IntervalValue mem,
												 final FcnRcdValue pstates,
												 final IntValue deadState) {
		assert inc.isNormalized();
		assert r2.isNormalized();
		assert r1.isNormalized();
		assert mem.isNormalized();
		assert r1.size() == r2.size() && mem.size() == r1.size() && pstates.size() == r1.size();

		BoolValue res = BoolValue.ValFalse;
		int size = mem.size();

		// check 1 - was there a round that was completed at all? If not then cannot be a transition
		boolean atLeastOneRoundComplete = false;
		for(int i=0; i<size; i++) {
			if (!r1.values[i].equals(r2.values[i])) {
				atLeastOneRoundComplete = true;
			}
		}

		if(!atLeastOneRoundComplete)
			return BoolValue.ValFalse;

		// Check 2 - Is there just a single member left that does not believe everyone else
		//           is dead and there was a round completed (we know because of check 1)
		//           then this is a transition
		int thinkAllIsDeadCount = 0;
		Map<Integer, Boolean> deadBeliefs = new HashMap<>();
		for(int i=0; i<size; i++) {
			final FcnRcdValue frv = (FcnRcdValue) pstates.values[i];
			boolean foundNotDead = false;
			for(int j=0; j<size; j++) {
				if( i==j)
					continue;

				final RecordValue rv = (RecordValue) frv.values[j];
				int stateIndex = 0;
				for (int n=0; n< rv.names.length; n++) {
					if(rv.names[n].equals("state")) {
						stateIndex = n;
						break;
					}
				}

				final IntValue s = (IntValue) rv.values[stateIndex];
				if (s.val != deadState.val) {
					foundNotDead = true;
					break;
				}
			}

			if(foundNotDead) {
				deadBeliefs.put(i, false);
			} else {
				thinkAllIsDeadCount++;
				deadBeliefs.put(i, true);
			}
		}

		if(thinkAllIsDeadCount == size-1) {
			return BoolValue.ValTrue;
		}

		// check 3 - Check if in the next round (r2) that all valid members have the same round
		//			 but that in the current round (r1) that there is one member that has a different round
		//			 this indicates that there was a round completed that led to a transition.
		//           Valid members are those that are alive and do not believe all other members are dead

		// use two pointer technique to jump over dead members, that can exist anywhere,
		// not just at the beginning.
		int m1 = 0;
		int m2 = 1;
		while (m1 < size && m2 < size) {
			if(inc.values[m1].equals(nil) || deadBeliefs.get(m1) == true) {
				m1++;
				continue;
			}

			if(m2 <= m1 || inc.values[m2].equals(nil) || deadBeliefs.get(m2) == true) {
				m2++;
				continue;
			}

			if(m1 >= size || m2 >= size)
				return res;

			if (!r2.values[m1].equals(r2.values[m2])) {
				return BoolValue.ValFalse;
			}

			if (!r1.values[m1].equals(r1.values[m2])) {
				res = BoolValue.ValTrue;
			}

			m1++;
			m2++;
		}

		return res;
	}


	public static Value TotalInfectivity(final IntValue disseminationsLimit, final FcnRcdValue tps) {
		assert tps.isNormalized();

		int total = 0;

		final Value[] domain = tps.domain;
		for (int i = 0; i < domain.length; i++) {
			for (int j = 0; j < domain.length; j++) {
				final FcnRcdValue frv = (FcnRcdValue) tps.values[i];
				final RecordValue rv = (RecordValue) frv.values[j];

				int dissIndex = 0;
				for (int n=0; n< rv.names.length; n++) {
					if(rv.names[n].equals("disseminations")) {
						dissIndex = n;
						break;
					}
				}

				final IntValue disseminations = (IntValue)rv.values[dissIndex];
				total += (disseminationsLimit.val - disseminations.val);
   			}
		}
		return IntValue.gen(total);
	}

	public static Value TotalInfectiveStates(final IntValue disseminationsLimit, final FcnRcdValue tps) {
		assert tps.isNormalized();

		int total = 0;

		final Value[] domain = tps.domain;
		for (int i = 0; i < domain.length; i++) {
			for (int j = 0; j < domain.length; j++) {
				final FcnRcdValue frv = (FcnRcdValue) tps.values[i];
				final RecordValue rv = (RecordValue) frv.values[j];

				int dissIndex = 0;
				for (int n=0; n< rv.names.length; n++) {
					if(rv.names[n].equals("disseminations")) {
						dissIndex = n;
						break;
					}
				}

				final IntValue disseminations = (IntValue)rv.values[dissIndex];
				if (disseminationsLimit.val - disseminations.val > 0 )
					total++;
			}
		}
		return IntValue.gen(total);
	}
}
