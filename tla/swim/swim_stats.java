import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.Value;

public class swim_stats {

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
IsNewRoundTransitionStep(i, r1, r2, nil, mem) ==
    /\ \E m1, m2 \in mem: i[m1] # nil /\ i[m2] # nil /\ r1[m1] # r1[m2] 
    /\ \A m3, m4 \in mem:
    	\/ i[m3] = Nil
    	\/ i[m4] = Nil
    	\/ /\ i[m3] # nil
    	   /\ i[m4] # nil
    	   /\ r2[m3] = r2[m4]
	 */
	public static Value IsNewRoundTransitionStep(final FcnRcdValue i, final FcnRcdValue r1, final FcnRcdValue r2,
			final ModelValue nil, final IntervalValue mem) {
		assert i.isNormalized();
		assert r2.isNormalized();
		assert r1.isNormalized();
		assert mem.isNormalized();
		assert r1.size() == r2.size() && mem.size() == r1.size();

		BoolValue res = BoolValue.ValFalse;
		
		// use two pointer technique to jump over dead members, that can exist anywhere,
		// not just at the beginning.
     	int m1 = 0;
		int m2 = 1;
		int size = mem.size();
		while (m1 < size && m2 < size) {
			if(i.values[m1].equals(nil)) {
				m1++;
				continue;
			}

			if(m2 <= m1 || i.values[m2].equals(nil)) {
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
}
