/* We establish a classic paxos model referring to 
 ** the 2001 paper (Leslie Lamport. Paxos Made Simple) and 
 ** the 2004 paper (Jim Gray and Leslie Lamport: Consensus on Transaction Commit. MSR-TR-2003-96)
 * We refer to the original paper of Lamport for a detailed understanding of Paxos if you are confused with part of this model
 * (Leslie Lamport. The part-time parliament. ACM transactions on Computer Systems, 16(2):133-169, May 1998)
 * There are other variants of Paxos, such as Fast Paxos, Byzantine Paxos, and Raft.
 *
 * The classic paxos protocol has three types of "nodes":
 * - Coordinators/Proposers/Leaders: which propose values
 * - Acceptors: which accept and decide a value under the coordination of (one or more) coordinators
 * - Learners: which learns a value after the protocol reaches a decide phase
 *
 * We assume asynchronous communication model, i.e., messages may not get lost, but there is not a time bound for message delivery
 * Integrity/Correctness: a decided value must be proposed by a coordinator
 * Consistency/Safety: a single value is decided (for each protocol round/view/cycle)
 *
 * Note that classic paxos assumes that no participant is malicious. 
 * However, a participant may become faulty, as long as the total number of faulty node is less than half of the total number of nodes.
 * The total number of nodes is known to everyone.
 * 
 * Simplifications in the model:
 * -- We assume an coordinator picks a ballot when it becomes active (is event is atomic)
 * -- The ballot being selected is ever increasing, starting from 0; Each coordinator's ballot number is unique/distinct
 * -- Each time a ballot is picked, such information is broadcast to every acceptor
 * -- A message is recorded in a global data structure, and may be delivered to each individual node by individual action (modelling asynchrony)
 * -- We assume all messages are broadcast (since no party is malicious)
 * -- No modelling message loss (as it cannot be distinguished from being ignored by the receiver)
 * -- If a node becomes faulty, then its irreversible (unlike a sleepy node in a sleepy model)
 * -- Learners are NOT explicitly modelled. We can directly observe a decision value if a leader/coordinator performs Step 3a.
 * -- We only model a single round of consensus
 *
 * We prove the safety condition (Consistency) at the end of the model
 */

type Acceptor(==)  // a set of acceptors (nodes)
type Proposal = int //nat  // the value that is proposed by some leader, 0 by default, but 0 is not considered a valid decision.
const acceptors: set<Acceptor>
const leaders: set<Acceptor>
//const ballots: set<int>
const F: int

lemma{:axiom} Quorum()
  ensures |acceptors| == 2 * F + 1

// an internal state of an acceptor: the highest ballot so far and its associated value 
datatype AState = AState(highest: int, value: Proposal) 
// the message type from an acceptor in step 1b
datatype AMsg = AMsg(ballot: int, highest: int, value: Proposal, acc: Acceptor)
// the message type from an acceptor in step 2b
datatype CMsg = CMsg(ballot: int, value: Proposal, acc: Acceptor)
// a triple representing a promise from an acceptor in step 1b: current highest promise, highest value, and the acceptor ID
datatype Promise = Promise(highest: int, value: Proposal, acc: Acceptor)

// a global state of a Paxos protocol run
datatype TSState = TSState(
    leader_ballot: map<Acceptor, int>,   // updated for a leader when it picks a ballot in step 1a, initially -1
    leader_propose: map<Acceptor, Proposal>,  // updated in step 2a for a leader when it proposes a value, initially 0
    leader_decision: map<Acceptor, Proposal>, // updated in step 3a for a leader when it decides a value, initially 0
    ballot: int,  // initially 0
    // all states of acceptors
    acceptor_state: map<Acceptor, AState>,  
    // counting the response of the form <bal, -1, 0> from any acceptor message in step 1b
    empty_count: map<Acceptor, set<Acceptor>>, 
    // counting the response of the form <bal, highest_bal, v> from any acceptor message in step 1b
    ballot_count: map<Acceptor, set<Promise>>,    
    // counting response from acceptors <bal, val, acceptor> in step 2b, where the domain of the map is the leader
    // Here, different leaders making same decision is possible, but his does not affect the checking of consistency/safety.
    decision_count: map<Acceptor, set<Acceptor>>,
    // the set of messages sent by acceptors in step 1b
    amsgs: set<AMsg>,
    // the set of messages sent by acceptors in step 2b
    cmsgs: set<CMsg>
)

// define the constraints for the types of a state components
ghost predicate type_ok(s: TSState){
    && s.leader_ballot.Keys == s.leader_propose.Keys == s.leader_decision.Keys 
        == s.empty_count.Keys == s.decision_count.Keys == s.ballot_count.Keys == leaders
    && s.acceptor_state.Keys == acceptors
    //&& forall n :: n in leaders ==> (forall v :: v in s.ballot_count[n].Keys ==> v >= -1)
}
// define what a valid state is in a Paxos run
ghost predicate valid(s: TSState){
    true
}

// the initial state when a protocol round starts
ghost predicate init(s: TSState)
  requires type_ok(s)
  ensures type_ok(s) && valid(s)
{
    && s.ballot == 0
    && (forall n :: n in leaders ==> s.leader_ballot[n] == -1)
    && (forall n :: n in leaders ==> s.leader_propose[n] == 0)
    && (forall n :: n in leaders ==> s.leader_decision[n] == 0)
    && (forall n :: n in leaders ==> s.decision_count[n] == {})
    && (forall a :: a in acceptors ==> s.acceptor_state[a] == AState(-1, 0))
    && (forall n :: n in leaders ==> s.empty_count[n] == {})
    && (forall n :: n in leaders ==> s.ballot_count[n] == {})
    && s.amsgs == {} && s.cmsgs == {}
}

// In the following we define each transition relation following the Paxos protocol.
//
// Step 1a: a leader (coordinator) chooses a ballot number & sends it to every acceptor. 
// This ballot number may be received by an acceptor sometime later.
predicate choose_ballot(s: TSState, s': TSState, c: Acceptor)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders
{
    && s.leader_ballot[c] == -1 // leader n was inactive
    && s'.leader_ballot == s.leader_ballot[c:= s.ballot] // n is now associated with a ballot
    && s'.ballot == s.ballot + 1
    // all the other state components remain the same
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.acceptor_state == s.acceptor_state
    && s'.empty_count == s.empty_count
    && s'.ballot_count == s.ballot_count
    && s'.decision_count == s.decision_count
}
// Step 1b: an acceptor may receive message 1a from a leader (coordinator) ometime later
// In this case, the ballot number is higher than the acceptor's highest recorded ballot
predicate receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors
{
    && s.leader_ballot[c] != -1 // leader n already has a ballot
    //&& s.acceptor_state[a].highest != -1 // acceptor a may have agreed on some ballot value if highest == -1
    && s.acceptor_state[a].highest < s.leader_ballot[c] // acceptor a has accepted some value for a lower ballot, or never promised a ballot
    // acceptor a promises with a message that contains c's ballot number
    && s'.amsgs == s.amsgs + {AMsg(s.leader_ballot[c], s.acceptor_state[a].highest, s.acceptor_state[a].value, a)}
    // acceptor a updates its highest (ballot, value) pair received so far --- // no need to update acceptor state 
    //&& s'.acceptor_state == s.acceptor_state[a:= AState(s.leader_ballot[c], s.acceptor_state[a].value)]
    && s'.acceptor_state == s.acceptor_state
    // all the other state components remain the same
    && s'.leader_ballot == s.leader_ballot
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.ballot == s.ballot
    && s'.cmsgs == s.cmsgs
    && s'.empty_count == s.empty_count
    && s'.ballot_count == s.ballot_count
    && s'.decision_count == s.decision_count
}

// Before step 2a: message received by a leader (copied from amsg)
ghost predicate receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, bn: int, highest: int, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors
{
    && AMsg(bn, highest, value, a) in s.amsgs && s.leader_ballot[c] == bn
    && (
      || (highest == -1 && s'.empty_count == s.empty_count[c:= s.empty_count[c]+{a}] 
              && s'.ballot_count == s.ballot_count) // the empty_count case
      || (highest != -1 && s'.ballot_count == s.ballot_count[c:= s.ballot_count[c]+{Promise(highest, value, a)}] 
              && s'.empty_count == s.empty_count) // the ballot count case
    ) // all the other state components remain the same
    && s'.leader_ballot == s.leader_ballot
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.ballot == s.ballot
    && s'.acceptor_state == s.acceptor_state
    && s'.decision_count == s.decision_count
    && s'.amsgs == s.amsgs
    && s'.cmsgs == s.cmsgs
}

// Step 2a, scenario 1: if a leader with a ballot number bn has collected at least F+1 empty counts


// Step 2a, scenario 2: if a leader with a ballot number bn has collected at least F+1 ballot counts


// Step 2b, an acceptor replies with an cmsg if it receives a value with a large enough ballot number 


// Before step 3a: message received by a leader (copied from cmsg)


// Step 3a, a leader with a ballot number bn has collected at least F+1 decision counts




/* Why do we have consistency for Paxos? Intuitively, it could be understood in the following way.
   If there is a ballot bn is observed to be decided with value v, there must be at least F + 1 acceptors promised 
   that they will only reply to a ballot number greater than or equal to bn. Therefore, for all other ballot bn' < bn
   those acceptors will not reply to any request with bn'; and for all new ballot bn'' >= bn, those acceptors will
   reply with (bn'', bn, v) in Step 1b. Since the leader with bn'' is honest, he will be forced in Step 2a to propose v 
   if it receives >(F + 1) Step 1b messages; he will not propose another value v' as there will be impossible for it
   to receive >(F + 1) Step 1b message for a different value.
 */