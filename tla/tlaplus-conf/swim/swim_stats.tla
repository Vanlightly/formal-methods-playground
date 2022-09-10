    -------------------------------- MODULE swim_stats --------------------------------

(*
Originally based on the Atomix SWIM TLA+ specification (https://github.com/atomix/atomix-tlaplus/blob/master/SWIM/SWIM.tla) 
but now heavily modified. The original spec was a subset of the SWIM protocol that focused on safety only, and only verifying that
the state a member has on its peer, for a given incarnation can only go from alive to suspect to dead.
  
This specification implements the variants 2 (SWIM+Inf.) and 3 (SWIM+Inf.+Susp.) of the SWIM paper. It can be run in TLC as v2 or v3
via the constants.
Summary of modifications:
- As per the SWIM paper:
    - Indirect probing via probe requests
    - Gossip messages (peer states) are piggybacked on probe, probe request and ack messages.
    - The number of gossiped peer states per probe/probeReq/ack is limited
    - When there are more infective peer states than can fit, those with the fewest disseminations are prioritised.
    - Suspected members are marked as dead after a timeout (number of protocol rounds). This can be deactivated to make it v2.
    - each member randomly picks another member to probe, but with guaranteed bounds 
      (i.e. cannot randomly pick the same member over and over again)
- For simulation/stats
    - The initial state can be configured such that some members start out dead, or ready to join, but
      that state is undetected by the rest of the members. 
      The aim is to measure the number of protocol rounds, and other metrics, in order for the ensemble 
      to converge on this new state. Shortly after reaching convergence, the spec will deadlock. 
      This is by design as it helps simulation by halting when we reach the objective. On deadlocking, 
      any statistical properties being tracked are printed out in a csv format.
      
    - Fair scheduling is modelled to ensure that the probe rate of each member is balanced. Each member 
      is always within 1 protocol round of each other

NOTE:
- current stat counter implemenation limits the number of members to 90 

*)

EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, TLC, TLCExt, Integers, Randomization, CSV, IOUtils


CONSTANTS Nil,                      \* Empty numeric value
          
          AliveState,               \* Numeric member state 
          SuspectState,             \* Numeric member state
          DeadState,                \* Numeric member state
          UnknownState,             \* Numeric member state
          
          ProbeMessage,             \* Message type: probe
          AckMessage,               \* Message type: ack
          ProbeRequestMessage,      \* Message type: probe request
          ForwardedAckMessage,      \* Message type: indirect ack forwarded
          
          \* CONFIGURABLE PARAMETERS
          \* The set of possible members
          NumMembersMin, NumMembersMax,     
          \* The number of peers to send probe requests when a direct probe fails
          PeerGroupSizeMin, PeerGroupSizeMax,   
          \* The number of protocol rounds before a suspected node is made dead
          SuspectTimeoutMin, SuspectTimeoutMax,      
          \* The lambda log n value (the maximum number of times a given update can be piggybacked)
          DisseminationLimitMin, DisseminationLimitMax,
          \* The maximum  number of state updates to be included in any given piggybacked gossip message
          MaxUpdatesPerPiggyBackMin, MaxUpdatesPerPiggyBackMax, 
          \* Each message has a 1/n chance of being lost. For use in simulation.
          LoseEveryNthMin, LoseEveryNthMax,             
          \* The number of members that newly added members know of used to bootstrap the new member into the cluster
          InitialContactsMin, InitialContactsMax,          
          \* The number of new members the ensemble need to detect
          NewMembersMin, NewMembersMax, 
          \* The number of dead members the ensemble need to detect
          DeadMembersMin, DeadMembersMax,         
          \* The number of members yet to join
          UnjoinedMembersMin, UnjoinedMembersMax,      
          DynamicSuspectTimeoutEnabled, \* Whether or not to set suspect timeout dynamically to 3*(log(n+1))
          MemberLeavesEnabled,          \* TRUE or FALSE as to the MemberLeaves action is enabled
          MessageLossMode,              \* "none" = no message loss
                                        \* "probabilistic" randomly drops messages, based on LoseEveryNth 
                                        \* "exhaustive" chooses both (model checking mode)     
          ForceRunToRound,              \* For use in simulation. When 0, the simulation will stop at convergence
                                        \* When > 0, the simulation will run to this number of rounds
          PrintStatsOnDeadlock,         \* For use in simulation. TRUE/FALSE as to whether to print the obtained stats when the simulation ends.
          PrintStatsWithoutConvergence, \* For use in simulation. TRUE/FALSE as to whether to print the obtained stats when the simulation ends without convergence.
          RoundStatsCSV,
          MemberStatsCSV,
          MemberMessageLoadStatsCSV

\* Precedence of the different states
ASSUME AliveState > SuspectState /\ SuspectState > DeadState /\ DeadState > UnknownState

ASSUME DeadMembersMin \in Nat
ASSUME DeadMembersMax \in Nat
ASSUME DeadMembersMin <= DeadMembersMax
ASSUME InitialContactsMin \in Nat
ASSUME InitialContactsMax \in Nat
ASSUME InitialContactsMin <= InitialContactsMax
ASSUME SuspectTimeoutMin \in Nat
ASSUME SuspectTimeoutMax \in Nat
ASSUME SuspectTimeoutMin <= SuspectTimeoutMax
ASSUME MaxUpdatesPerPiggyBackMin \in (Nat \ {0})
ASSUME MaxUpdatesPerPiggyBackMax \in (Nat \ {0})
ASSUME MaxUpdatesPerPiggyBackMin <= MaxUpdatesPerPiggyBackMax
ASSUME DisseminationLimitMin \in Nat
ASSUME DisseminationLimitMax \in Nat
ASSUME DisseminationLimitMin <= DisseminationLimitMax
ASSUME LoseEveryNthMin \in Nat
ASSUME LoseEveryNthMax \in Nat
ASSUME LoseEveryNthMin <= LoseEveryNthMax
ASSUME DeadMembersMin \in Nat
ASSUME DeadMembersMax \in Nat
ASSUME DeadMembersMin <= DeadMembersMax
ASSUME NewMembersMin \in Nat
ASSUME NewMembersMax \in Nat
ASSUME NewMembersMin <= NewMembersMax
ASSUME UnjoinedMembersMin \in Nat
ASSUME UnjoinedMembersMax \in Nat
ASSUME UnjoinedMembersMin <= UnjoinedMembersMax

ASSUME PrintStatsOnDeadlock \in BOOLEAN
ASSUME PrintStatsWithoutConvergence \in BOOLEAN
ASSUME MessageLossMode \in {"none", "exhaustive", "probabilistic"}
ASSUME ForceRunToRound \in Nat
ASSUME MemberLeavesEnabled \in BOOLEAN
ASSUME DynamicSuspectTimeoutEnabled \in BOOLEAN

\* ASSUME DeadMemberCount + NewMemberCount + InitialContacts <= NumMembers - UnjoinedMemberCount

ASSUME 
    IOExec(
        <<"bash", "-c", "echo \"Behaviour,Round,MessagesExchanged,DirectProbesToDead,IndirectProbesToDead,UpdatesInRound,EffectiveUpdatesInRound,AliveMembersCount,SuspectMembersCount,DeadMembersCount,AliveStatesCount,SuspectStatesCount,DeadStatesCount,InfectiveStatesCount,Infectivity,NumMembers,NumDead,NumNew,SuspectTimeout,DisseminationLimit,MaxUpdatesPerPiggyBack,LoseEveryNth,PeerGroupSize,InitialContacts,MaxRound\" > " \o RoundStatsCSV>>
        ).exitValue = 0 \* Fail fast if RoundStatsCSV was not created.

ASSUME 
    IOExec(
        <<"bash", "-c", "echo \"Behaviour,Member,ReceivedMessages,ReceivedProbeMessages,ReceivedProbeRequestMessages,NumMembers,NumDead,NumNew,SuspectTimeout,DisseminationLimit,MaxUpdatesPerPiggyBack,LoseEveryNth,PeerGroupSize,InitialContacts,MaxRound\" > " \o MemberStatsCSV>>
        ).exitValue = 0 \* Fail fast if MemberStatsCSV was not created.

ASSUME 
    IOExec(
        <<"bash", "-c", "echo \"Behaviour,Round,Member,AllMessages,IncomingMessages,OutgoingMessages,DeadStates,NumMembers,NumDead,NumNew,SuspectTimeout,DisseminationLimit,MaxUpdatesPerPiggyBack,LoseEveryNth,PeerGroupSize,InitialContacts,MaxRound\" > " \o MemberMessageLoadStatsCSV>>
        ).exitValue = 0 \* Fail fast if MemberMessageLoadStatsCSV was not created.        
            
VARIABLES \* actual state in the protocol
          incarnation,          \* Member incarnation numbers
          peer_states,          \* The known state that each member has on its peers
          round,                \* Each member keeps track of which round of the protocol it is in
          pending_direct_ack,   \* Each member keeps track of members it is pending a direct ack from
          pending_indirect_ack, \* Each member keeps track of members it is pending an idirect ack from
          probe_ctr,            \* Each member keeps track of how many probes it has sent to each peer
                                \* It randomly selects peers, but keeps the number of probes balanced
          \* messaging passing
          messages,             \* a function of all messages
          
          \* required for detecting some situations where convergence is not attainable
          initial_state_joined,
          initial_state_dead,
          initial_state_unjoined,
          
          \* for simulation and stats
          sim_status,
          initial_state_stats,

          \* config
          cfg_num_members,
          cfg_peer_group_size,
          cfg_suspect_timeout,
          cfg_dis_limit,
          cfg_max_updates,
          cfg_lose_nth,
          cfg_initial_contacts,
          cfg_new_members,
          cfg_dead_members,
          cfg_unjoined_members

initial_state_vars == <<initial_state_joined, initial_state_dead, initial_state_stats, initial_state_unjoined>>
configVars == <<cfg_num_members, cfg_peer_group_size, cfg_suspect_timeout, cfg_dis_limit,
             cfg_max_updates, cfg_lose_nth, cfg_initial_contacts, cfg_new_members,
             cfg_dead_members, cfg_unjoined_members>>
vars == <<incarnation, peer_states, messages, pending_direct_ack, pending_indirect_ack, probe_ctr, round, 
          sim_status, initial_state_stats, initial_state_vars, configVars>>

Member == 1..cfg_num_members
LiveMember == Member \ initial_state_dead

(*****************************************************)
(*************** Messaging passing *******************)
(*****************************************************)

\* if the dest is dead, it never gets delivered
\* or if the dest thinks the source is dead, it ignores it (SWIM makes no provision for dead members playing an active role)
\* else if we have turned on message loss, then there are two modes:
\*  'probabilistic' is a random chance of losing the message
\*  'exhaustive' is for model checking where both options are explored
GetDeliveredCount(msg) ==
    IF incarnation[msg.dest] = Nil \/ peer_states[msg.dest][msg.source].state = DeadState 
    THEN {0}
    ELSE
        CASE MessageLossMode = "probabilistic" -> IF RandomElement(1..cfg_lose_nth) = cfg_lose_nth THEN {0} ELSE {1}
          [] MessageLossMode = "exhaustive"    -> {0,1}
          [] OTHER                             -> {1}

\* Send a message only if the message has not already been sent
SendMessage(msg) ==
    /\ msg \notin DOMAIN messages
    /\ \E delivered_count \in GetDeliveredCount(msg) :
        messages' = messages @@ (msg :> delivered_count)

\* Mark one message as processed and send a new message   
ProcessedOneAndSendAnother(received_msg, send_msg) ==
    /\ received_msg \in DOMAIN messages
    /\ send_msg \notin DOMAIN messages
    /\ messages[received_msg] >= 1
    /\ \E delivered_count \in GetDeliveredCount(send_msg) :
        messages' = [messages EXCEPT ![received_msg] = @-1] @@ (send_msg :> delivered_count)

\* Mark one message as processed   
MessageProcessed(msg) ==
    /\ msg \in DOMAIN messages
    /\ messages[msg] >= 1
    /\ messages' = [messages EXCEPT ![msg] = @ - 1]

\* Can only receive message if not received yet and the receipient is alive
\* Also SWIM paper makes no provision for communication from a peer a member considers to be dead already
\* so we ignore it.
CanReceiveMessage(msg, message_type) ==
    /\ msg.type = message_type
    /\ messages[msg] >= 1
    /\ incarnation[msg.dest] # Nil
    /\ peer_states[msg.dest][msg.source].state # DeadState


MessageIgnored ==
    \E msg \in DOMAIN messages : 
        /\ messages[msg] >= 1
        /\ \/ incarnation[msg.dest] = Nil
           \/ peer_states[msg.dest][msg.source].state = DeadState
        /\ messages' = [messages EXCEPT ![msg] = 0]
        /\ UNCHANGED <<configVars, incarnation, peer_states, pending_direct_ack, pending_indirect_ack, 
                        probe_ctr, round, sim_status, initial_state_vars >>

\* When a member sends a probe to a peer, it needs to keep track of that
\* and additionally increment its probe_ctr (required for balanced probing)
RegisterPendingDirectAck(member, peer) ==
    /\ pending_direct_ack' = [pending_direct_ack EXCEPT ![member] = peer]
    /\ probe_ctr' = [probe_ctr EXCEPT ![member][peer] = @ + 1]

RegisterReceivedDirectAck(member) ==
    pending_direct_ack' = [pending_direct_ack EXCEPT ![member] = Nil]

(*****************************************************)
(*************** Helper operators ********************)
(*****************************************************)

3LogNLookup(n) ==
    CASE n = 1 -> 1
      [] n < 4 -> 2
      [] n < 10 -> 3
      [] n < 21 -> 4
      [] n < 46 -> 5
      [] OTHER -> 6

DisseminationLimit ==
    IF cfg_dis_limit = 0
    THEN 3LogNLookup(cfg_num_members)
    ELSE cfg_dis_limit

SuspectTimeout ==
    IF DynamicSuspectTimeoutEnabled = TRUE
    THEN IF cfg_suspect_timeout = 0
         THEN 3LogNLookup(cfg_num_members)
         ELSE cfg_suspect_timeout    
    ELSE cfg_suspect_timeout

UnknownStateRecord ==
    [incarnation    |-> 0, 
     state          |-> UnknownState, 
     round          |-> 0, 
     disseminations |-> DisseminationLimit]
     
KnownAliveStateRecord ==
    [incarnation    |-> 1, 
     state          |-> AliveState, 
     round          |-> 1, 
     disseminations |-> DisseminationLimit]
     
InitialContactStateRecord ==
    [incarnation    |-> 1, 
     state          |-> AliveState, 
     round          |-> 1, 
     disseminations |-> 0]     

\* What is the highest protocol round of the ensemble
MaxRound ==
    LET highest == CHOOSE m1 \in Member :
        \A m2 \in Member: round[m1] >= round[m2]
    IN round[highest]

IncrementRound(m) ==
    round' = [round EXCEPT ![m] = @ + 1]
    
\* The real state being either dead or alive. The real state of a member 
\* cannot be "suspected".
RealStateOfMember(member, nil, dead_state, alive_state) ==
    IF incarnation[member] = nil THEN dead_state ELSE alive_state

\* TRUE when:
\* for each member, it's live peers all agree on the same thing, specifically that:
\*    - either they see the true state
\*    - or they (falsely) think that it is dead
\* SWIM does not prevent false positives (just mitigates them)
\* and makes no provision for coming back from the dead - once you a member thinks you're dead 
\* they cannot be convinced otherwise (deadness is monotonic).
IsConverged(inc, pstates, members, nil, dead_state, alive_state) ==
    \A member \in members :
        \A peer \in members :
            \/ inc[peer] = nil
            \/ member = peer
            \/ /\ member # peer
               /\ \/ pstates[peer][member].state = RealStateOfMember(member, nil, dead_state, alive_state)
                  \/ pstates[peer][member].state = DeadState                      

\* There can be a situation, where a joinee does not know of a peer
\* and the peer does not know of the joinee, and no other members
\* have infective state on the joinee to share with this peer.
\* In this case, convergence is impossible.
CannotConvergeOnJoined ==
    /\ initial_state_joined # {}
    /\ \A msg \in DOMAIN messages : messages[msg] = 0
    /\ \E joined \in initial_state_joined :
        \* a) If a peer that the joined member knows of does not know of it yet,
        \*    it just means that the joined member has not yet successfully sent it a probe
        /\ ~\E peer \in Member :
            /\ peer_states[joined][peer].state = AliveState
            /\ peer_states[peer][joined].state = UnknownState
        \* b) There are peers that could inform the other peers that do not know of the joined peer
        \*    yet, but their state on the joined member is not infective anymore 
        /\ \E peer \in Member :
            /\ joined # peer
            /\ incarnation[joined] # Nil
            /\ incarnation[peer] # Nil
            /\ peer_states[joined][peer].state = UnknownState
            /\ peer_states[peer][joined].state = UnknownState
            \* there is another member that knows the joined member is alive
            /\ \E m \in Member : 
                /\ m # joined
                /\ m # peer
                /\ peer_states[m][joined].state = AliveState
            \* but it cannot gossip about it because its state is not infective anymore
            /\ ~\E m \in Member : 
                /\ m # joined
                /\ m # peer
                /\ peer_states[m][joined].state = AliveState
                /\ peer_states[m][joined].disseminations < DisseminationLimit
            
WillBeConverged ==
    IsConverged(incarnation, peer_states', Member, Nil, DeadState, AliveState)
    
MemberThinksEveryoneIsDead(member, mem, pstates, dead_state) ==
    \A m1 \in mem : m1 = member \/ pstates[member][m1].state = dead_state    
    
AllMembersThinkEveryoneIsDead ==
    \A member \in Member: MemberThinksEveryoneIsDead(member, Member, peer_states, DeadState) 

StopConditionReached ==
    \/ sim_status > 0
    \/ IF ForceRunToRound > 0
       THEN IF \A member \in Member : round[member] <= ForceRunToRound 
            THEN IF AllMembersThinkEveryoneIsDead THEN TRUE ELSE FALSE
            ELSE TRUE
       ELSE IF IsConverged(incarnation, peer_states, Member, Nil, DeadState, AliveState) 
            THEN TRUE 
            ELSE IF CannotConvergeOnJoined
                 THEN TRUE
                 ELSE FALSE
    

\* Returns TRUE or FALSE as to whether an individual peer state is new for this member
\* It is new only if:
\* - its incarnation number is > than the known incarnation number of the target member
\*   and the member is not considered dead (once dead, there is no coming back according to SWIM paper)
\* - its incarnation number equals the known incarnation number of the target member but its state has higher precedence
IsNewInformation(member, peer, peer_state) ==
    \/ /\ peer_state.incarnation > peer_states[member][peer].incarnation
       /\ peer_states[member][peer].state # DeadState
    \/ /\ peer_state.incarnation = peer_states[member][peer].incarnation
       /\ peer_state.state < peer_states[member][peer].state

(************************************************************************) 
(******************** RECORD STATISTICS *********************************)
(************************************************************************)

(* Notes
Records various metrics using TLCSet and TLCGet. Some metrics are already available in the variables
such as round and messages.
At the end of a simulation, the statistics are gathered from the counters and variables and printed
in CSV format.
*)

updates_pr_ctr(r) ==
    (r * 100)

eff_updates_pr_ctr(r) ==
    (r * 100) + 1

suspect_ctr(r) ==
    (r * 100) + 2
    
suspect_states_ctr(r) ==
    (r * 100) + 3
    
dead_ctr(r) ==
    (r * 100) + 4
    
dead_states_ctr(r) ==
    (r * 100) + 5    
    
alive_ctr(r) ==
    (r * 100) + 6
    
alive_states_ctr(r) ==
    (r * 100) + 7

infective_states_ctr(r) ==
    (r * 100) + 8
    
infectivity_ctr(r) ==
    (r * 100) + 9
    
dead_states_of_member_ctr(r, member) ==
    (r * 100) + 10 + member  

ResetStats(max_round) ==
    \A r \in 1..max_round :
        /\ TLCSet(updates_pr_ctr(r), 0)
        /\ TLCSet(eff_updates_pr_ctr(r), 0)
        /\ IF r = 1 
           THEN /\ TLCSet(alive_ctr(r), initial_state_stats.alive_members)
                /\ TLCSet(alive_states_ctr(r), initial_state_stats.alive_states)
           ELSE /\ TLCSet(alive_ctr(r), 0)
                /\ TLCSet(alive_states_ctr(r), 0)        
        /\ TLCSet(suspect_ctr(r), 0)
        /\ TLCSet(suspect_states_ctr(r), 0)
        /\ TLCSet(dead_ctr(r), 0)
        /\ TLCSet(dead_states_ctr(r), 0)
        /\ TLCSet(infective_states_ctr(r), 0)
        /\ TLCSet(infectivity_ctr(r), 0)
        /\ \A m \in Member :
            TLCSet(dead_states_of_member_ctr(r, m), 0)

MemberCount(state, target_peer_states, members) ==
    Cardinality({dest \in members : 
        \E source \in members :
            target_peer_states[source][dest].state = state})
            
CurrentMemberCount(state) == MemberCount(state, peer_states, Member)
NextStateMemberCount(state) == MemberCount(state, peer_states', Member)  

StateCountOfMember(state, target_peer_states, members, member) ==
    Quantify(members, LAMBDA m : target_peer_states[member][m].state = state)

StateCount(state, target_peer_states, members) ==
    LET pairs == { s \in SUBSET members : Cardinality(s) = 2 }
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

CurrentStateCount(state) == StateCount(state, peer_states, Member)
NextStateStateCount(state) == StateCount(state, peer_states', Member)

TotalInfectivity(disseminationsLimit, target_peer_states, members) ==
    0 \* requires the override
    
    
TotalInfectiveStates(disseminationsLimit, target_peer_states, members) ==
    Cardinality({ pair \in SeqOf(members, 2) : 
                    /\ Len(pair) = 2
                    /\ target_peer_states[pair[1]][pair[2]].disseminations < disseminationsLimit
                })
                
\* Does the step increment the round for one member such that now all members are on the same round?
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

MayBeRecordMemberCounts ==
    \* Is this is a step that leads to all members being on the same round then record the member count stats
    IF  IsNewRoundTransitionStep(incarnation, round, round', Nil, Member, peer_states, DeadState)
    THEN
        LET r == MaxRound
        IN
            /\ TLCSet(suspect_ctr(r), NextStateMemberCount(SuspectState))
            /\ TLCSet(dead_ctr(r), NextStateMemberCount(DeadState))
            /\ TLCSet(alive_ctr(r), NextStateMemberCount(AliveState))
            /\ TLCSet(suspect_states_ctr(r), NextStateStateCount(SuspectState))
            /\ TLCSet(dead_states_ctr(r), NextStateStateCount(DeadState))
            /\ TLCSet(alive_states_ctr(r), NextStateStateCount(AliveState))
            /\ TLCSet(infective_states_ctr(r), TotalInfectiveStates(DisseminationLimit, peer_states, Member))
            /\ TLCSet(infectivity_ctr(r), TotalInfectivity(DisseminationLimit, peer_states, Member))
            /\ \A m \in Member :
                TLCSet(dead_states_of_member_ctr(r, m), StateCountOfMember(DeadState, peer_states, Member, m))
    ELSE TRUE

RecordIncomingGossipStats(member, gossip_source, incoming_peer_states, end_of_round) ==
    LET updates_ctr_id     == updates_pr_ctr(round[gossip_source])
        eff_updates_ctr_id == eff_updates_pr_ctr(round[gossip_source])
    IN 
       \* gossip counts
       /\ TLCSet(updates_ctr_id, TLCGet(updates_ctr_id) + Cardinality(DOMAIN incoming_peer_states))
       \* effective gossip counts
       /\ LET effective_count == Quantify(DOMAIN incoming_peer_states, 
                                          LAMBDA m : IsNewInformation(member, m, incoming_peer_states[m])) 
          IN TLCSet(eff_updates_ctr_id, TLCGet(eff_updates_ctr_id) + effective_count)
       \* suspect and dead counts
       /\ IF end_of_round THEN MayBeRecordMemberCounts ELSE TRUE         

RoundMessageLoad(r) ==
    Quantify(DOMAIN messages, LAMBDA msg : msg.round = r)

IsMessageOfMemberInRound(msg, r, member) ==
    /\ \/ msg.source = member
       \/ msg.dest = member
    /\ msg.round = r

MessageLoad(r, member) ==
    Quantify(DOMAIN messages, LAMBDA msg : IsMessageOfMemberInRound(msg, r, member))

IsIncomingMessageOfMemberInRound(msg, r, member) ==
    /\ msg.dest = member
    /\ msg.round = r
    
IncomingMessageLoad(r, member) ==
    Quantify(DOMAIN messages, LAMBDA msg : IsIncomingMessageOfMemberInRound(msg, r, member))
    
ReceivedMessageLoad(member) ==
    Quantify(DOMAIN messages, LAMBDA msg : msg.dest = member)
    
ReceivedProbeMessageLoad(member) ==
    Quantify(DOMAIN messages, LAMBDA msg : msg.dest = member /\ msg.type = ProbeMessage /\ msg.on_behalf_of = Nil)
    
ReceivedProbeRequestMessageLoad(member) ==
    Quantify(DOMAIN messages, LAMBDA msg : msg.dest = member /\ msg.type = ProbeRequestMessage)    
    
IsOutgoingMessageOfMemberInRound(msg, r, member) ==
    /\ msg.dest = member
    /\ msg.round = r
    
OutgoingMessageLoad(r, member) ==
    Quantify(DOMAIN messages, LAMBDA msg : IsOutgoingMessageOfMemberInRound(msg, r, member))

DirectProbeDeadMessageLoad(r) ==
    Quantify(DOMAIN messages, LAMBDA msg : 
        /\ msg.round = r
        /\ msg.type = ProbeMessage
        /\ msg.on_behalf_of = Nil
        /\ incarnation[msg.dest] = Nil)
        
IndirectProbeDeadMessageLoad(r) ==
    Quantify(DOMAIN messages, LAMBDA msg : 
        /\ msg.round = r
        /\ msg.type = ProbeMessage
        /\ msg.on_behalf_of # Nil
        /\ incarnation[msg.dest] = Nil)        

PrintStatsToCSV ==
    \* \E behaviour_id \in {RandomElement(1..1000000)} :
    LET max_stats_round == MaxRound
        behaviour_id    == TLCGet("stats").behavior.id
    IN
        /\ \A member \in LiveMember : 
            CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s,%7$s,%8$s,%9$s,%10$s,%11$s,%12$s,%13$s,%14$s,%15$s",
                <<behaviour_id, 
                    member, ReceivedMessageLoad(member), ReceivedProbeMessageLoad(member),
                    ReceivedProbeRequestMessageLoad(member),
                    cfg_num_members, cfg_dead_members, cfg_new_members, SuspectTimeout,
                    DisseminationLimit, cfg_max_updates, cfg_lose_nth, cfg_peer_group_size, 
                    cfg_initial_contacts, MaxRound>>,
                MemberStatsCSV)
        /\ \A r \in 1..max_stats_round : 
            LET alive_count          == IF r = max_stats_round 
                                        THEN CurrentMemberCount(AliveState)
                                        ELSE TLCGet(alive_ctr(r))
                suspect_count        == IF r = max_stats_round 
                                        THEN CurrentMemberCount(SuspectState)
                                        ELSE TLCGet(suspect_ctr(r))
                dead_count           == IF r = max_stats_round 
                                        THEN CurrentMemberCount(DeadState)
                                        ELSE TLCGet(dead_ctr(r))
                alive_states_count   == IF r = max_stats_round 
                                        THEN CurrentStateCount(AliveState)
                                        ELSE TLCGet(alive_states_ctr(r))
                suspect_states_count == IF r = max_stats_round 
                                        THEN CurrentStateCount(SuspectState)
                                        ELSE TLCGet(suspect_states_ctr(r))
                dead_states_count    == IF r = max_stats_round 
                                        THEN CurrentStateCount(DeadState)
                                        ELSE TLCGet(dead_states_ctr(r))
                infective_states_count == IF r = max_stats_round 
                                          THEN TotalInfectiveStates(DisseminationLimit, peer_states, Member)
                                          ELSE TLCGet(infective_states_ctr(r))
                infectivity          == IF r = max_stats_round 
                                        THEN TotalInfectivity(DisseminationLimit, peer_states, Member)
                                        ELSE TLCGet(infectivity_ctr(r))
            IN
                /\ CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s,%7$s,%8$s,%9$s,%10$s,%11$s,%12$s,%13$s,%14$s,%15$s,%16$s,%17$s,%18$s,%19$s,%20$s,%21$s,%22$s,%23$s,%24$s,%25$s",
                    <<behaviour_id, 
                        r, RoundMessageLoad(r), DirectProbeDeadMessageLoad(r), IndirectProbeDeadMessageLoad(r), TLCGet(updates_pr_ctr(r)),
                        TLCGet(eff_updates_pr_ctr(r)), alive_count, suspect_count, dead_count,
                        alive_states_count, suspect_states_count, dead_states_count,
                        infective_states_count, infectivity,
                        cfg_num_members, cfg_dead_members, cfg_new_members, SuspectTimeout,
                        DisseminationLimit, cfg_max_updates, cfg_lose_nth, cfg_peer_group_size, 
                        cfg_initial_contacts, MaxRound>>,
                    RoundStatsCSV)
                /\ \A member \in LiveMember : 
                    LET dead_states_of_member == IF r = max_stats_round 
                                                 THEN StateCountOfMember(DeadState, peer_states, Member, member)
                                                 ELSE TLCGet(dead_states_of_member_ctr(r, member))
                    IN
                        CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s,%7$s,%8$s,%9$s,%10$s,%11$s,%12$s,%13$s,%14$s,%15$s,%16$s,%17$s",
                            <<behaviour_id, 
                                r, member, MessageLoad(r, member), IncomingMessageLoad(r, member),
                                OutgoingMessageLoad(r, member), dead_states_of_member,
                                cfg_num_members, cfg_dead_members, cfg_new_members, SuspectTimeout,
                                DisseminationLimit, cfg_max_updates, cfg_lose_nth, cfg_peer_group_size, 
                                cfg_initial_contacts, MaxRound>>,
                            MemberMessageLoadStatsCSV)
        /\ PrintT(<<"result", TLCGet("stats").traces>>)
        /\ ResetStats(max_stats_round)

PrintNoConvergence ==
    /\ LET max_stats_round == MaxRound
           cfg_str == "," \o ToString(cfg_num_members) 
                        \o "," \o ToString(cfg_dead_members)
                        \o "," \o ToString(cfg_new_members)
                        \o "," \o ToString(SuspectTimeout)
                        \o "," \o ToString(DisseminationLimit)
                        \o "," \o ToString(cfg_max_updates)
                        \o "," \o ToString(cfg_lose_nth)
                        \o "," \o ToString(cfg_peer_group_size)
                        \o "," \o ToString(cfg_initial_contacts)
                        \o "," \o ToString(MaxRound)
                        \o ","
       IN
        /\ PrintT("no-convergence" \o cfg_str)
        /\ PrintT("result")

EndSim ==
    /\ StopConditionReached
    /\ sim_status # 1
    /\ IF PrintStatsOnDeadlock = TRUE 
       THEN IF \/ IsConverged(incarnation, peer_states, Member, Nil, DeadState, AliveState)
               \/ PrintStatsWithoutConvergence = TRUE
            THEN PrintStatsToCSV
            ELSE IF CannotConvergeOnJoined
                 THEN PrintNoConvergence 
                 ELSE PrintT("no-convergence") 
       ELSE TRUE
    /\ sim_status' = 1
    /\ UNCHANGED <<configVars, incarnation, peer_states, messages, pending_direct_ack, pending_indirect_ack, probe_ctr, round, initial_state_vars>>

RecordGossipStats(member, gossip_source, incoming_states, end_of_round) ==
    RecordIncomingGossipStats(member, gossip_source, incoming_states, end_of_round)
    
RecordStateStats ==
    MayBeRecordMemberCounts

(************************************************************************) 
(******************** SELECTING OUTGOING GOSSIP *************************)
(************************************************************************)

(* NOTES
Peer states are selected for piggybacking on probes, probe requests and acks based on:
1. The maximum number of times a peer state can be disseminated (lambda log n in the paper
   but in this spec the constant DisseminationLimit. When under this limit, the state is
   still infective.
2. The maximum number of peer states that can be piggybacked.
   In this spec the constant MaxUpdatesPerPiggyBack.
3. In the case that all valid peer states do not fit, prioritise those that have been 
   disseminated fewer times.
*)

\* For the given member, returns the peers it has state on that is still infective
PeersUnderDisseminationsLimit(member, peer, new_peer_states) ==
    { m1 \in Member : 
        /\ m1 # member
        /\ m1 # peer
        /\ new_peer_states[m1].disseminations < DisseminationLimit
    }
    
\* Choose the peer states to gossip based on the MaxUpdatesPerGossip and when there is more
\* gossip than can be accomodated in a single message, choose the peer states
\* in order of fewest disseminations first
Prioritise(candidate_peers, limit, new_peer_states) ==
    CHOOSE peer_subset \in SUBSET candidate_peers :
        /\ Cardinality(peer_subset) = limit
        /\ \A peer1 \in peer_subset :
            \A peer2 \in candidate_peers \ peer_subset :
                new_peer_states[peer1].disseminations <= new_peer_states[peer2].disseminations

ShareableState(peer_state) ==
    [incarnation |-> peer_state.incarnation,
     state       |-> peer_state.state]

SelectOutgoingGossip(member, dest_peer, merged_peer_states) ==
    LET candidate_peers == PeersUnderDisseminationsLimit(member, dest_peer, merged_peer_states)
    IN
        IF Cardinality(candidate_peers) <= cfg_max_updates 
        THEN [peer \in candidate_peers |-> ShareableState(merged_peer_states[peer])]
        ELSE LET peers == Prioritise(candidate_peers, cfg_max_updates, merged_peer_states)
             IN [peer \in peers |-> ShareableState(merged_peer_states[peer])]
             
\* Increment the dissemination counter of the peer states that have been gossiped             
UpdatePeerStates(member, updated_peer_states, sent_peer_states) ==
    peer_states' = [peer_states EXCEPT ![member] =  
                        [peer \in Member |-> IF peer \in DOMAIN sent_peer_states
                                             THEN [updated_peer_states[peer] EXCEPT !.disseminations = @ + 1]
                                             ELSE updated_peer_states[peer]]]
                                                                 

(************************************************************************) 
(******************** INCOMING GOSSIP ***********************************)
(************************************************************************)

(* NOTES
Gossip can come in on probes, probe requests and acks. Any incoming gossip is 
merged with existing peer state, with stale peer states being replaced by any newer gossiped state. 
Stale peer state is that which has a lower incarnation number than the gossiped state or 
which has the same incarnation number, but a lower precedence state. 
The precedence order is (highest to lowest) Dead, Suspect, Alive.
*)

ResetCountersOfRecord(record, member_round) ==
    [incarnation    |-> record.incarnation,
     state          |-> record.state,
     disseminations |-> 0,
     round          |-> member_round]

NewAliveMemberRecord(incarnation_number, member_round) ==
    [incarnation    |-> incarnation_number, 
     state          |-> AliveState, 
     disseminations |-> 0, 
     round          |-> member_round]

MergeGossipWithCurrentState(member, gossip_source, source_incarnation, incoming_peer_states) ==
    [peer \in Member |-> 
        IF peer = member 
        THEN peer_states[member][member] \* it holds no data about itself 
        ELSE 
            IF peer = gossip_source
            THEN IF peer_states[member][gossip_source].incarnation < source_incarnation
                 THEN NewAliveMemberRecord(source_incarnation, round[member])
                 ELSE peer_states[member][gossip_source]
            ELSE
                IF peer \in DOMAIN incoming_peer_states
                THEN IF IsNewInformation(member, peer, incoming_peer_states[peer])
                     THEN ResetCountersOfRecord(incoming_peer_states[peer], round[member])
                     ELSE peer_states[member][peer]
                ELSE peer_states[member][peer]]
                    

\* Updates the state and counters of a peer of the given member
\* This is not called when an incarnation has changed, only a state change 
\* like Alive->Suspect or Suspect->Dead
\* When configured as SWIM v2, we skip suspect state and go straight to dead.
UpdateState(member, peer, state) ==
    LET new_state == IF state = SuspectState /\ SuspectTimeout = 0 THEN DeadState ELSE state
    IN
        peer_states' = [peer_states EXCEPT ![member][peer] =
                            [@ EXCEPT !.state          = new_state,
                                      !.disseminations = 0,
                                      !.round          = round[member]]]

MayBeIncrementIncarnation(msg) ==
    IF msg.dest_state.state = SuspectState /\ msg.dest_state.incarnation = incarnation[msg.dest]
    THEN incarnation[msg.dest] + 1 
    ELSE incarnation[msg.dest]

MayBeUpdateIncarnation(member, new_incarnation) ==
    IF incarnation[member] < new_incarnation
    THEN incarnation' = [incarnation EXCEPT ![member] = new_incarnation]
    ELSE UNCHANGED incarnation

(************************************************************************) 
(******************** ACTION: SendDirectProbe****************************)
(************************************************************************)

(* Notes
Triggers a probe request from a member to a peer and is the beginning of a new protocol round
for that member.
A new protocol round can only commence when the prior one is complete. That can occur when:
- there are no pending expirations (suspect to dead) to apply
- there are no pending acks to direct probes
- there are no pending indirect acks via probe requests that have a chance of completing
  (message loss and dead members can cause there to be no reply from any probe requests sent out). 
*)

\* The current round is complete only if:
\* - The member has no pending expirations
\* - The member is not waiting on a direct ack
\* - The member is not waiting on an indirect ack
CurrentRoundComplete(member) ==
    /\ ~\E peer \in Member :
        /\ peer_states[member][peer].state = SuspectState
        /\ round[member] - peer_states[member][peer].round > SuspectTimeout
    /\ pending_indirect_ack[member] = Nil   
    /\ pending_direct_ack[member] = Nil
    
\* The member knows of the peer's existence and it is not pending expiry
IsValidProbeTarget(member, peer) ==
    /\ member # peer
    /\ \/ peer_states[member][peer].state = AliveState       
       \/ /\ peer_states[member][peer].state = SuspectState
          /\ round[member] - peer_states[member][peer].round <= SuspectTimeout

\* Peers picked in a random but time bounded manner
IsValidRandomPick(member, peer) ==
    \A m \in Member : 
        IF IsValidProbeTarget(member, m) 
        THEN probe_ctr[member][peer] <= probe_ctr[member][m]
        ELSE TRUE

\* This is necessary for statistics simulation to ensure that all members are
\* sending out probes at the same rate and stay within one round of each other
\* It tests that the member is on an equal or lower round than all its peers that 
\* are both alive and who themselves still have peers they believe are alive (if a member
\* thinks everyone else is dead, then it cannot take part in further rounds and
\* is therefore not included in fair scheduling)
\* It also ensures there are no outstanding messages regarding indirect probing for this member
IsFairlyScheduled(member, peer) ==
    /\ \A m1 \in Member : 
        \/ incarnation[m1] = Nil
        \/ \A m2 \in Member : m1 = m2 \/ peer_states[m1][m2].state = DeadState
        \/ /\ incarnation[m1] # Nil
           /\ round[member] <= round[m1]
    /\ ~\E msg \in DOMAIN messages :
        /\ msg.on_behalf_of = member
        /\ messages[msg] > 0  

\* The sending of a direct probe is the beginning of a new protocol period.
SendDirectProbe(member, peer) ==
    /\ ~StopConditionReached
    /\ member # peer
    /\ incarnation[member] # Nil            \* The member is alive
    /\ CurrentRoundComplete(member)         \* This member can initiate its next protocol round
    /\ IsValidProbeTarget(member, peer)     \* The peer is valid (the member think it's not dead for example)
    /\ IsValidRandomPick(member, peer)      \* Peers are picked randomly, but in a balanced way
    /\ IsFairlyScheduled(member, peer)      \* For simulation - we keep all members within 1 round of each other
    /\ LET gossip_to_send == SelectOutgoingGossip(member, peer, peer_states[member])
       IN
        /\ SendMessage([type         |-> ProbeMessage,
                        source       |-> member,
                        dest         |-> peer,
                        round        |-> round[member],
                        on_behalf_of |-> Nil,
                        dest_state   |-> ShareableState(peer_states[member][peer]),
                        source_inc   |-> incarnation[member],
                        gossip       |-> gossip_to_send])
        /\ UpdatePeerStates(member, peer_states[member], gossip_to_send)
        /\ RegisterPendingDirectAck(member, peer)
        /\ UNCHANGED <<configVars, incarnation, pending_indirect_ack, round, sim_status, initial_state_vars >>


        
(************************************************************************) 
(******************** ACTION: ReceiveProbe ******************************)
(************************************************************************)

(* Notes
Handles a probe message from a peer, either a direct or an indirect probe.
If the received incarnation is greater than the destination's incarnation number, update the
destination's incarnation number to 1 plus the received number. This can happen after a node
leaves and rejoins the cluster. If the destination is suspected by the source, increment the
destination's incarnation and respond with the updated incarnation, this will tell the source
that the destination is in fact alive. 
If the destination's incarnation is greater than the source's incarnation, just send an ack.
Adds pending gossip (that will fit) to the ack (piggybacking).
Adds any incoming gossip that is new, to the peer state to be gossiped later.
*)

\* Send an ack and piggyback gossip if any to send
SendAck(probe, source_incarnation, merged_peer_state, piggyback_gossip) ==
    ProcessedOneAndSendAnother(probe, 
                       [type         |-> AckMessage,
                        source       |-> probe.dest,
                        dest         |-> probe.source,
                        round        |-> probe.round,
                        on_behalf_of |-> probe.on_behalf_of,
                        dest_state   |-> ShareableState(merged_peer_state[probe.source]),
                        source_inc   |-> source_incarnation,
                        gossip       |-> piggyback_gossip])
 
ReceiveProbe ==
    /\ ~StopConditionReached
    /\ \E msg \in DOMAIN messages :
        /\ CanReceiveMessage(msg, ProbeMessage)
        /\ LET merged_peer_state == MergeGossipWithCurrentState(msg.dest, 
                                                              msg.source, 
                                                              msg.source_inc, 
                                                              msg.gossip)
               new_incarnation   == MayBeIncrementIncarnation(msg)
           IN LET send_gossip == SelectOutgoingGossip(msg.dest, msg.source, merged_peer_state)
              IN
               /\ MayBeUpdateIncarnation(msg.dest, new_incarnation)
               /\ SendAck(msg, new_incarnation, merged_peer_state, send_gossip)
               /\ UpdatePeerStates(msg.dest, merged_peer_state, send_gossip)
               /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, FALSE)
    /\ UNCHANGED <<configVars, round, pending_direct_ack, pending_indirect_ack, probe_ctr, sim_status, initial_state_vars >>

(************************************************************************) 
(******************** ACTION: ReceiveAck ********************************)
(************************************************************************)

(* Notes
Handles an ack message (from a direct probe only) from a peer.
Increments this member's round as this is the end of a protocol round 
*)
ReceiveAck ==
    /\ ~StopConditionReached
    /\ \E msg \in DOMAIN messages :
        /\ CanReceiveMessage(msg, AckMessage)
        /\ msg.on_behalf_of = Nil \* this is a direct probe
        /\ msg.round = round[msg.dest]
        /\ LET merged_peer_state == MergeGossipWithCurrentState(msg.dest, 
                                                                msg.source, 
                                                                msg.source_inc, 
                                                                msg.gossip)
               new_incarnation   == MayBeIncrementIncarnation(msg)
           IN
            /\ MayBeUpdateIncarnation(msg.dest, new_incarnation)
            /\ UpdatePeerStates(msg.dest, merged_peer_state, <<>>)
            /\ RegisterReceivedDirectAck(msg.dest)
            /\ MessageProcessed(msg)
            /\ IncrementRound(msg.dest)
            /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, TRUE)
            /\ UNCHANGED <<configVars, pending_indirect_ack, probe_ctr, sim_status, initial_state_vars>>

(************************************************************************) 
(******************** ACTION: Expire ************************************)
(************************************************************************)

(* Notes
Expires a suspected peer once it has reached the timeout.
We can run as variant 2 by setting the timeout to 0 which means
immediate expiry.
*)
Expire(member, peer) ==
    /\ ~StopConditionReached
    /\ member # peer
    /\ peer_states[member][peer].state = SuspectState
    /\ (round[member] - peer_states[member][peer].round) > SuspectTimeout
    /\ UpdateState(member, peer, DeadState)
    /\ UNCHANGED <<configVars, incarnation, messages, pending_direct_ack, pending_indirect_ack, 
                   probe_ctr, round, sim_status, initial_state_vars >>


(************************************************************************) 
(******************** ACTION: SendProbeRequest **************************)
(************************************************************************)

(* Notes
Enabled when a direct probe has failed, there are still probe requests to
be sent out and valid peers to receive them. 
The number of probe requests is bounded by the minimum of:
- The PeerGroupSize value, this is the number of peers a member will send probe requests to
- The number of available peers to send to
*)

NewProbeRequest(member, peer, failed_peer, gossip_to_send) ==
    [type         |-> ProbeRequestMessage,
     source       |-> member,
     dest         |-> peer,
     target       |-> failed_peer,
     on_behalf_of |-> Nil,
     dest_state   |-> ShareableState(peer_states[member][peer]),
     source_inc   |-> incarnation[member],
     round        |-> round[member],
     gossip       |-> gossip_to_send]

IsPreviouslySentPR(msg, source, r) ==
    /\ msg.type = ProbeRequestMessage
    /\ msg.source = source
    /\ msg.round = r
    

EligibleProbeRequestPeer(member, peer, failed_peer, r) ==
    /\ peer # member
    /\ peer # failed_peer
    /\ IsValidProbeTarget(member, peer)
    /\ ~\E msg \in DOMAIN messages : 
            /\ IsPreviouslySentPR(msg, member, r)
            /\ msg.dest = peer 

SendOneProbeRequest(failed_probe) == 
    LET member      == failed_probe.source
        failed_peer == failed_probe.dest
    IN
        \E peer \in Member : 
            /\ EligibleProbeRequestPeer(member, peer, failed_peer, failed_probe.round)
            /\ LET gossip_to_send == SelectOutgoingGossip(member, peer, peer_states[member])
               IN
                    /\ SendMessage(NewProbeRequest(member, peer, failed_peer, gossip_to_send))
                    /\ UpdatePeerStates(member, peer_states[member], gossip_to_send)
                    /\ pending_indirect_ack' = [pending_indirect_ack EXCEPT ![member] = failed_peer]
                    /\ pending_direct_ack' = [pending_direct_ack EXCEPT ![member] = Nil]

DirectProbeFailed(msg) ==
    /\ msg.type = ProbeMessage
    /\ messages[msg] <= 0
    /\ msg.round = round[msg.source]
    /\ msg.on_behalf_of = Nil
    /\ ~\E ack \in DOMAIN messages : 
        /\ ack.type = AckMessage
        /\ ack.dest = msg.source
        /\ ack.round = msg.round
        /\ messages[ack] >= 1
        
SendProbeRequest ==
    /\ ~StopConditionReached
    /\ \E msg \in DOMAIN messages :
        /\ DirectProbeFailed(msg)
        /\ Quantify(DOMAIN messages, LAMBDA prev_msg : IsPreviouslySentPR(prev_msg, msg.source, msg.round)) < cfg_peer_group_size
        /\ SendOneProbeRequest(msg)
        /\ UNCHANGED <<configVars, incarnation, probe_ctr, round, sim_status, initial_state_vars>>

(************************************************************************) 
(******************** ACTION: NoPeersForProbeRequest ********************)
(************************************************************************)

(* Notes
This is enabled when we haven't sent out any probe requests and 
there are no valid peers to send to.
*)

NoEligiblePeersForProbeRequest(failed_probe) == 
    LET member      == failed_probe.source
        failed_peer == failed_probe.dest
    IN
        \/ Quantify(DOMAIN messages, LAMBDA msg : IsPreviouslySentPR(msg, failed_probe.source, failed_probe.round)) >= cfg_peer_group_size
        \/ ~\E peer \in Member : 
            EligibleProbeRequestPeer(member, peer, failed_peer, failed_probe.round)

ProbeRequestsSent(member) ==
    \E msg \in DOMAIN messages :
        /\ msg.type = ProbeRequestMessage
        /\ msg.round = round[member]
        /\ msg.source = member

NoPeersForProbeRequest ==
    /\ ~StopConditionReached
    /\ \E msg \in DOMAIN messages :
        /\ DirectProbeFailed(msg)
        /\ ~ProbeRequestsSent(msg.source)
        /\ NoEligiblePeersForProbeRequest(msg)
        /\ IF peer_states[msg.source][msg.dest].state = AliveState
           THEN UpdateState(msg.source, msg.dest, SuspectState)
           ELSE UNCHANGED peer_states
        /\ IncrementRound(msg.source)
        /\ RecordStateStats
        /\ pending_direct_ack' = [pending_direct_ack EXCEPT ![msg.source] = Nil]
        /\ UNCHANGED <<configVars, incarnation, messages, probe_ctr, pending_indirect_ack, sim_status, initial_state_vars>>    

(************************************************************************) 
(******************** ACTION: ReceiveProbeRequest ***********************)
(************************************************************************)

(* Notes
Receives a probe request and then sends a probe to the target peer.
*)

ReceiveProbeRequest ==
    /\ ~StopConditionReached
    /\ \E msg \in DOMAIN messages :
        /\ CanReceiveMessage(msg, ProbeRequestMessage)
        /\ LET merged_peer_state == MergeGossipWithCurrentState(msg.dest, 
                                                                msg.source, 
                                                                msg.source_inc, 
                                                                msg.gossip)
               new_incarnation   == MayBeIncrementIncarnation(msg)
           IN LET gossip_to_send == SelectOutgoingGossip(msg.dest, msg.target, merged_peer_state)
              IN
                /\ MayBeUpdateIncarnation(msg.dest, new_incarnation)
                /\ ProcessedOneAndSendAnother(msg,
                               [type         |-> ProbeMessage,
                                source       |-> msg.dest,
                                dest         |-> msg.target,
                                round        |-> msg.round,
                                on_behalf_of |-> msg.source,
                                dest_state   |-> ShareableState(merged_peer_state[msg.target]),
                                source_inc   |-> new_incarnation,
                                gossip       |-> gossip_to_send])
                /\ UpdatePeerStates(msg.dest, merged_peer_state, gossip_to_send)
                /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, FALSE)
    /\ UNCHANGED <<configVars, pending_direct_ack, pending_indirect_ack, probe_ctr, round, sim_status, initial_state_vars >>


(************************************************************************) 
(******************** ACTION: ReceiveProbeRequestAck ********************)
(************************************************************************)

(*
This is only enabled when the target of the original direct probe is in fact
alive. If the target really were dead, it would not respond to the indirect probe.
The ack from the target peer is forwarded back to the member that sent the probe
request.
*)

ForwardedAck(msg, merged_peer_state, gossip_to_send) ==
    [type         |-> ForwardedAckMessage,
     source       |-> msg.dest,
     dest         |-> msg.on_behalf_of,
     on_behalf_of |-> msg.on_behalf_of,
     target       |-> msg.source,
     dest_state   |-> ShareableState(merged_peer_state[msg.on_behalf_of]),
     source_inc   |-> incarnation[msg.dest],
     round        |-> msg.round,
     gossip       |-> gossip_to_send]

ReceiveProbeRequestAck ==
    /\ ~StopConditionReached
    /\ \E msg \in DOMAIN messages :
        /\ CanReceiveMessage(msg, AckMessage)
        /\ msg.on_behalf_of # Nil
        /\ LET merged_peer_state == MergeGossipWithCurrentState(msg.dest, 
                                                                msg.source, 
                                                                msg.source_inc, 
                                                                msg.gossip)
               new_incarnation   == MayBeIncrementIncarnation(msg)
           IN LET send_gossip == SelectOutgoingGossip(msg.dest, msg.on_behalf_of, merged_peer_state)
              IN
                /\ MayBeUpdateIncarnation(msg.dest, new_incarnation)
                /\ UpdatePeerStates(msg.dest, merged_peer_state, send_gossip)
                /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, FALSE)
                /\ ProcessedOneAndSendAnother(msg, ForwardedAck(msg, merged_peer_state, send_gossip))
                /\ UNCHANGED <<configVars, pending_direct_ack, pending_indirect_ack, probe_ctr, round, sim_status, initial_state_vars>>

(************************************************************************) 
(******************** ACTION: ReceiveForwardedAck ***********************)
(************************************************************************)

(* Notes
This member earlier sent out a direct probe, which failed (not responded to) and
so had sent out up to PeerGroupSize probe requests. If the original target peer
is in fact alive, then the member may receive multiple forwarded acks. On the
first such message that is received, it untracks the target as pending an indirect ack
and increments its own round as this is the end of a protocol round for this member.
*)

ReceiveForwardedAck ==
    /\ ~StopConditionReached
    /\ \E msg \in DOMAIN messages :
        /\ CanReceiveMessage(msg, ForwardedAckMessage)
        /\ LET merged_peer_state == MergeGossipWithCurrentState(msg.dest, 
                                                                msg.source, 
                                                                msg.source_inc, 
                                                                msg.gossip)
               new_incarnation   == MayBeIncrementIncarnation(msg)
           IN
            /\ MayBeUpdateIncarnation(msg.dest, new_incarnation)
            /\ UpdatePeerStates(msg.dest, merged_peer_state, <<>>)
            /\ IF round[msg.dest] # msg.round \/ pending_indirect_ack[msg.dest] = Nil 
               THEN /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, FALSE)
                    /\ UNCHANGED << round, pending_indirect_ack >>
               ELSE /\ IncrementRound(msg.dest)
                    /\ pending_indirect_ack' = [pending_indirect_ack EXCEPT ![msg.dest] = Nil]
                    /\ RecordGossipStats(msg.dest, msg.source, msg.gossip, TRUE) 
            /\ MessageProcessed(msg)
            /\ UNCHANGED <<configVars, pending_direct_ack, probe_ctr, sim_status, initial_state_vars>>


(************************************************************************) 
(******************** ACTION: ProbeRequestFails *************************)
(************************************************************************)

(* Notes
This is enabled when the chain of up to PeerGroupSize probe requests is broken,
either due to the target peer really being dead, or message loss somewhere.
This is the end of a protocol period of this member, so the round for this member 
is incremented.
*)

IndirectProbeChainIntact(member) ==
    LET round_of_chain == round[member]
    IN
        \E msg \in DOMAIN messages :
           /\ msg.round = round_of_chain
           /\ \/ /\ msg.type = ProbeRequestMessage 
                 /\ msg.source = member
              \/ /\ msg.type = ProbeMessage
                 /\ msg.on_behalf_of = member
              \/ /\ msg.type = AckMessage
                 /\ msg.on_behalf_of = member
              \/ /\ msg.type = ForwardedAckMessage
                 /\ msg.dest = member
           /\ messages[msg] > 0

NoMoreProbeRequestsToSend(member) == 
    LET failed_probe == CHOOSE msg \in DOMAIN messages :
                            /\ msg.type = ProbeMessage
                            /\ msg.round = round[member]
                            /\ msg.source = member
                            /\ msg.on_behalf_of = Nil
    IN NoEligiblePeersForProbeRequest(failed_probe)

NoResponseToProbeRequests ==
    /\ ~StopConditionReached
    /\ \E member \in Member :
        /\ pending_indirect_ack[member] # Nil
        /\ ProbeRequestsSent(member)
        /\ NoMoreProbeRequestsToSend(member)
        /\ ~IndirectProbeChainIntact(member)
        /\ LET pr == CHOOSE msg \in DOMAIN messages :
                        /\ msg.type = ProbeRequestMessage
                        /\ msg.source = member
                        /\ msg.round = round[member]
           IN
                /\ IF peer_states[member][pr.target].state = AliveState
                   THEN UpdateState(member, pr.target, SuspectState)
                   ELSE UNCHANGED << peer_states >>
                /\ pending_indirect_ack' = [pending_indirect_ack EXCEPT ![member] = Nil]
                /\ IncrementRound(member)
                /\ RecordStateStats
                /\ UNCHANGED <<configVars, incarnation, messages, pending_direct_ack, probe_ctr, sim_status, initial_state_vars>>

(************************************************************************) 
(******************** ACTION: MemberJoins *******************************)
(************************************************************************)

(* Notes
A member that joins does not have a Nil incarnation prior to joining. A
member that is yet to join is alive but knows of no other peers.
Joining is the act of informing it of the existence of InitialContactMemberCount peers
that it can start probing.
*)

MemberJoins ==
    \E member \in Member :
        /\ incarnation[member] # Nil
        /\ \A m \in Member : \/ member = m
                             \/ peer_states[member][m].state = UnknownState
        /\ \E contact_peers \in SUBSET Member : 
            /\ \A p \in contact_peers : incarnation[p] # Nil
            /\ Cardinality(contact_peers) = cfg_initial_contacts
            /\ peer_states' = [peer_states EXCEPT ![member] =
                                    [m \in Member |-> IF m \in contact_peers
                                                      THEN KnownAliveStateRecord
                                                      ELSE UnknownStateRecord]]
            /\ UNCHANGED <<configVars, incarnation, messages, pending_direct_ack, pending_indirect_ack, 
                           probe_ctr, round, sim_status, initial_state_vars >>


(************************************************************************) 
(******************** ACTION: MemberLeaves *******************************)
(************************************************************************)

(* Notes
Only enabled if the constant AllowMembersToLeave is set to TRUE.
Simply changes its incarnation to Nil which represents a dead member.
Once left, a member cannot rejoin. SWIM makes no provision for rejoining members,
it would need to join with a different identifier which is not modelled in this spec.
There must be at least two live members for a member to leave, we do not model all members leaving.
Any messages sent to the leaving member, but not processed are lost.
*)
MemberLeaves ==
    /\ MemberLeavesEnabled
    /\ \E m1, m2 \in Member :
        /\ m1 # m2
        /\ incarnation[m1] # Nil
        /\ incarnation[m2] # Nil
        /\ incarnation' = [incarnation EXCEPT ![m1] = Nil]
        /\ messages' = [msg \in DOMAIN messages |-> IF msg.dest = m1 THEN 0 ELSE messages[msg]]
        /\ UNCHANGED <<configVars, peer_states, pending_direct_ack, pending_indirect_ack, 
                       probe_ctr, round, sim_status, initial_state_vars >>


(************************************************************************) 
(******************** Init, Next state and spec *************************)
(************************************************************************)

\* We can configure the initial state to start with a certain number of undetected states
\* such as undetected dead members or undetected newly joined members.
\* We can also configure some members to not have joined yet
\* The rest will be started, and already know about each other and their peer state they have not being infective.
\* This all allows us to test various scenarios easily
Init ==
    \E num_members \in NumMembersMin..NumMembersMax, 
        peer_group_size \in PeerGroupSizeMin..PeerGroupSizeMax,
        suspect_timeout \in SuspectTimeoutMin..SuspectTimeoutMax,
        dis_limit \in DisseminationLimitMin..DisseminationLimitMax,
        max_updates \in MaxUpdatesPerPiggyBackMin..MaxUpdatesPerPiggyBackMax,
        lose_nth \in LoseEveryNthMin..LoseEveryNthMax,
        initial_contacts \in InitialContactsMin..InitialContactsMax,
        new_members \in NewMembersMin..NewMembersMax,
        dead_members \in DeadMembersMin..DeadMembersMax,
        unjoined_member \in UnjoinedMembersMin..UnjoinedMembersMax :

        /\ cfg_num_members = num_members
        /\ cfg_peer_group_size = peer_group_size
        /\ cfg_suspect_timeout = suspect_timeout
        /\ cfg_dis_limit = dis_limit
        /\ cfg_max_updates = max_updates
        /\ cfg_lose_nth = lose_nth
        /\ cfg_initial_contacts = initial_contacts
        /\ cfg_new_members = new_members
        /\ cfg_dead_members = dead_members
        /\ cfg_unjoined_members = unjoined_member
        /\ initial_state_dead = RandomSubset(dead_members, Member) 
        /\ initial_state_joined = RandomSubset(new_members, (Member \ initial_state_dead))
        /\ initial_state_unjoined = RandomSubset(unjoined_member, (Member \ (initial_state_dead \union initial_state_joined))) 
        /\ incarnation = [m \in Member |-> IF m \in initial_state_dead THEN Nil ELSE 1]
        /\ peer_states = [m \in Member |-> [m1 \in Member |-> 
                                                CASE m \in initial_state_joined   -> IF m1 \in RandomSubset(cfg_initial_contacts, (Member \ (initial_state_dead \union initial_state_joined \union initial_state_unjoined)))
                                                                                    THEN InitialContactStateRecord
                                                                                    ELSE IF m = m1 
                                                                                        THEN KnownAliveStateRecord
                                                                                        ELSE UnknownStateRecord
                                                [] m \in initial_state_dead     -> UnknownStateRecord
                                                [] m \in initial_state_unjoined -> UnknownStateRecord
                                                [] OTHER                        -> IF m1 \in initial_state_joined \/ m1 \in initial_state_unjoined
                                                                                    THEN UnknownStateRecord
                                                                                    ELSE KnownAliveStateRecord]]
        /\ round = [m \in Member |-> 1]
        /\ messages = [msg \in {} |-> 0]
        /\ pending_direct_ack = [m \in Member |-> Nil]
        /\ pending_indirect_ack = [m \in Member |-> Nil]
        /\ probe_ctr = [m \in Member |-> [m1 \in Member |-> 0]]
        /\ sim_status = 0
        /\ initial_state_stats = [alive_states  |-> StateCount(AliveState, peer_states, Member),
                                alive_members |-> Cardinality(Member) - Cardinality(initial_state_unjoined)]
        /\ ResetStats(1000)

Next ==
    \/ \E member, peer \in Member : 
        \/ SendDirectProbe(member, peer)
        \/ Expire(member, peer)
    \/ ReceiveProbe
    \/ ReceiveAck
    \/ SendProbeRequest
    \/ NoPeersForProbeRequest
    \/ ReceiveProbeRequest
    \/ ReceiveProbeRequestAck
    \/ ReceiveForwardedAck
    \/ NoResponseToProbeRequests
    \/ MemberJoins
    \/ MemberLeaves
    \/ MessageIgnored
    \/ EndSim

MemberOrNil ==
    Member \union {Nil}

States ==
    { AliveState, SuspectState, DeadState, UnknownState }

TypeOK ==
    /\ incarnation \in [Member -> Nat \union {Nil}]
    /\ peer_states \in [Member -> [Member -> [incarnation    : Nat, 
                                              state          : States, 
                                              round          : Nat, 
                                              disseminations : 0..cfg_dis_limit]]]
    /\ round \in [Member -> Nat]
    /\ pending_direct_ack \in [Member -> MemberOrNil]
    /\ pending_indirect_ack \in [Member -> MemberOrNil]
    /\ probe_ctr \in [Member -> [Member -> Nat]]
    /\ sim_status \in Nat


HasInfectiveInfo ==
    IF \E m \in Member : round[m] > 4 
    THEN \E m \in Member :
           /\ \E m1 \in Member :
               \*/\ peer_states[m][m1].disseminations > 0
               /\ peer_states[m][m1].disseminations < cfg_dis_limit
    ELSE TRUE

Inv ==
    TRUE

Liveness ==
    WF_vars(Next)

Spec == Init /\ [][Next]_vars 

============================================================================
\* Modification History
\* Last modified Sun Nov 08 06:47:48 PST 2020 by jack
\* Last modified Thu Oct 18 12:45:40 PDT 2018 by jordanhalterman
\* Created Mon Oct 08 00:36:03 PDT 2018 by jordanhalterman