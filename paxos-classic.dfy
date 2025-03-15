/* We establish a classic paxos model referring to 
 ** the 2001 paper (Leslie Lamport. Paxos Made Simple) and 
 ** the 2004 paper (Jim Gray and Leslie Lamport: Consensus on Transaction Commit. MSR-TR-2003-96)
 ** the author also consulted this website https://uvdn7.github.io/paxos-explained/ to achieve a better understanding in Paxos
 * Overall we refer to the original paper of Lamport for a detailed understanding of Paxos if you are confused with part of this model
 * (Leslie Lamport. The part-time parliament. ACM transactions on Computer Systems, 16(2):133-169, May 1998)
 * There are other variants of Paxos, such as Fast Paxos, Byzantine Paxos, and Raft.
 *
 * The classic paxos protocol has three types of "nodes":
 * - Coordinators/Proposers/Leaders: which propose values
 * - Acceptors: which accept and decide a value under the coordination of (one or more) coordinators
 * - Learners: which learns a value after the protocol reaches a decide phase
 *
 * We assume asynchronous communication model, i.e., messages cannot get lost, but there does not exist a time bound for message delivery
 * Integrity/Correctness: a decided value must be proposed by a coordinator
 * Consistency/Safety: a single value is decided (for each protocol round/view/cycle)
 *
 * Note that classic paxos assumes that no participant is malicious. 
 * A participant may become faulty, as long as the total number of faulty node is less than half of the total number of nodes.
 * The total number of nodes is known to everyone.
 * 
 * Simplifications in the model:
 * -- We assume that an coordinator picks a ballot when it becomes active (this event is atomic)
 * -- The ballot number to be selected is ever increasing, starting from 0; This implies every coordinator's ballot number is unique/distinct
 * -- Each time a ballot is picked, such information is broadcast to every acceptor
 * -- A message is recorded in a global data structure, and may be delivered to each individual node by an individual "receive" action (modelling asynchrony)
 * -- We assume all messages are broadcast (since no party is malicious)
 * -- No modelling message of loss (as it cannot be distinguished from being ignored by the receiver)
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
// an internal state of a leader: its ballot and its value to be proposed
datatype LState = LState(ballot: int, value: Proposal)
// the message type from an acceptor in step 1b
datatype PMsg = PMsg(ballot: int, highest: int, value: Proposal, acc: Acceptor)
// the message type from an acceptor in step 2b
datatype CMsg = CMsg(ballot: int, value: Proposal, acc: Acceptor)

// a global state of a Paxos protocol run
datatype TSState = TSState(
    leader_ballot: map<Acceptor, int>,   // updated for a leader when it picks a ballot in step 1a, initially -1
    leader_propose: map<Acceptor, Proposal>,  // updated in step 2a for a leader when it proposes a value, initially 0
    leader_decision: map<Acceptor, Proposal>, // updated in step 3a for a leader when it decides a value, initially 0
    ballot: int,  // initially 0
    // states of acceptors
    acceptor_state: map<Acceptor, AState>,  
    // states of leaders
    leader_state: map<Acceptor, LState>,  
    // counting the response of the form <highest_bal, bal, value, acc> from any acceptor message in step 1b
    // where the domain of the map is the leaders
    promise_count: map<Acceptor, set<Acceptor>>,    
    // counting response from acceptors <bal, val, acceptor> in step 2b, where the domain of the map is the leaders
    // Here, different leaders making same decision is possible, but this should not affect the checking of consistency/safety.
    decision_count: map<Acceptor, set<Acceptor>>,
    // the set of messages sent by acceptors in step 1b
    pmsgs: set<PMsg>,
    // the set of messages sent by acceptors in step 2b
    cmsgs: set<CMsg>
)

// define the constraints for the types of a state components
ghost predicate type_ok(s: TSState){
    && s.leader_ballot.Keys == s.leader_propose.Keys == s.leader_decision.Keys 
        == s.promise_count.Keys == s.decision_count.Keys == leaders
    && s.acceptor_state.Keys == acceptors
    && s.leader_state.Keys == leaders
    //&& forall n :: n in leaders ==> (forall v :: v in s.ballot_count[n].Keys ==> v >= -1)
}
// define what a valid state is in a Paxos run
// we may also add invariants into this predicate later
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
    && (forall n :: n in leaders ==> s.leader_state[n] == LState(-1, 0))
    && (forall n :: n in leaders ==> s.promise_count[n] == {})
    && (forall n :: n in leaders ==> s.decision_count[n] == {})
    && s.pmsgs == {} && s.cmsgs == {}
}

// In the following we define a transition relation for each step following the Paxos protocol.
//
// Step 1a: a leader (coordinator) chooses a ballot number & sends it to every acceptor. 
// This ballot number may be received by an acceptor sometime later, 
// which is modelled by (an acceptor later) looking into the leader_ballot component.
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
    && s'.leader_state == s.leader_state
    && s'.promise_count == s.promise_count
    && s'.decision_count == s.decision_count
}
// Step 1b: an acceptor may receive message 1a from a leader (coordinator) sometime later
// In this case, the ballot number is higher than the acceptor's highest recorded ballot.
// There are two possibilities here: 
// (1) the acceptor has not yet confirmed any value; 
// (2) the acceptor has already confirmed some value previously
predicate receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors
{
    && s.leader_ballot[c] != -1 // leader n already has a ballot
    && s.acceptor_state[a].highest < s.leader_ballot[c] // acceptor a has not yet promised a ballot >= c's ballot
    // acceptor a promises with a message that contains c's ballot number
    && s'.pmsgs == s.pmsgs + {PMsg(s.leader_ballot[c], s.acceptor_state[a].highest, s.acceptor_state[a].value, a)}
    // acceptor a updates its highest (ballot, value) pair received so far --- 
    && s'.acceptor_state == s.acceptor_state[a := AState(s.leader_ballot[c], s.acceptor_state[a].value)]
    // all the other state components remain the same
    && s'.leader_ballot == s.leader_ballot
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.ballot == s.ballot
    && s'.cmsgs == s.cmsgs
    && s'.promise_count == s.promise_count
    && s'.decision_count == s.decision_count
}

// Before step 2a: message received by a leader (copied from pmsg)
ghost predicate receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, bn: int, highest: int, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors
{
    && PMsg(bn, highest, value, a) in s.pmsgs && s.leader_ballot[c] == bn
    && (
      || (value != 0 && s'.leader_state == s.leader_state[c:= LState(s.leader_state[c].ballot, value)])
      || (value == 0 && s'.leader_state == s.leader_state)
    )
    && s'.promise_count == s.promise_count[c:= s.promise_count[c]+{a}]
    // all the other state components remain the same
    && s'.leader_ballot == s.leader_ballot
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.ballot == s.ballot
    && s'.acceptor_state == s.acceptor_state
    && s'.decision_count == s.decision_count
    && s'.pmsgs == s.pmsgs
    && s'.cmsgs == s.cmsgs
}

// Step 2a, scenario 1: if a leader with a ballot number bn has collected at least F+1 empty counts


// Step 2a, scenario 2: if a leader with a ballot number bn has collected at least F+1 ballot counts


// Step 2b, an acceptor replies with an cmsg if it receives a value with a large enough ballot number 


// Before step 3a: message received by a leader (copied from cmsg)


// Step 3a, a leader with a ballot number bn has collected at least F+1 decision counts




/* Why do we have consistency for Paxos? Intuitively, it could be understood in the following way.
   If there is a ballot bn that is observed as having been decided with value v, then
   (1) there must be at least F + 1 acceptors promised in Step 1b that they will only reply to a ballot number greater than or equal to bn, and
   (2) the same F+1 acceptors have sent out a confirm reply in Step 2b in response to the proposer with ballot number bn for v. 
   
   Therefore, for all other ballots bn' < bn those acceptors will not reply to any request with bn'; and for all new ballot bn'' >= bn, 
   those acceptors will reply with (bn'', bn, v) in Step 1b since they have previously confirmed that value. 
   (Note they cannot all go faulty which is against our assumption) Since the leader with bn'' is honest, 
   he will be forced in Step 2a to propose v (with bn'') if it receives at least one Step 1b message with a confirmed v; 
   He will not propose a different value unless it has not received any Step 1b message with a confirmed v 
   (Intuitively, that value "v" should have already been confirmed by the system but it may still be waiting 
   for a proposer to "announce" that it is confirmed).

   In general, we cannot distinguish the case when a user is faulty and the case that a message from or to that user is taking too long. 
 */