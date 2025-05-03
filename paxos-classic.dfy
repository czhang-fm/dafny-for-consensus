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
 * Simplification and abstractions made in the model:
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
type Proposal = int // the value that is proposed by some leader, 0 by default, but 0 is not considered a valid decision.
const acceptors: set<Acceptor>
const leaders: set<Acceptor>
//const ballots: set<int>
const F: int

lemma{:axiom} Quorum()
  ensures |acceptors| == 2 * F + 1

// an internal state of an acceptor: the highest ballot so far and its associated value 
datatype AState = AState(highest: int, value: Proposal) 
// the message type from an acceptor in step 1b --- Promising
datatype PMsg = PMsg(ballot: int, highest: int, value: Proposal)
// the message type from an acceptor in step 2b --- Confirming
datatype CMsg = CMsg(ballot: int, value: Proposal)

// a global state of a Paxos protocol run
datatype TSState = TSState(
    leader_ballot: map<Acceptor, int>,   // updated for a leader when it picks a ballot in step 1a, initially -1
    leader_propose: map<Acceptor, Proposal>,  // updated in step 2a for a leader when it proposes a value, initially 0
    leader_decision: map<Acceptor, Proposal>, // updated in step 3a for a leader when it decides a value, initially 0
    ballot: int,  // initially 0
    // states of acceptors
    acceptor_state: map<Acceptor, AState>,  
    // states of leaders are already encoded in the first three maps

    // counting PMsg of the form <bn, 0> from any acceptor message in step 1b
    // where the domain of the map is the set of leaders
    promise_count: map<Acceptor, set<Acceptor>>,    
    // counting CMsg from acceptors of the form <bal, val> in step 2b, where the domain of the map is the set of leaders
    // Here, different leaders making a (same) decision is possible, which should not affect consistency/safety.
    decision_count: map<Acceptor, set<Acceptor>>,
    // the set of messages sent by acceptors in step 1b
    pmsgs: map<Acceptor, set<PMsg>>,
    // the set of messages sent by acceptors in step 2b
    cmsgs: map<Acceptor, set<CMsg>>,
    // an auxiliary data structure from the set of chosen ballots to leaders
    ballot_mapping: seq<Acceptor>,
    // an auxiliary counter for state transitions
    counter: int,
    // an auxiliary function mapping PMsg to its receiver
    receiver_pmsg: map<PMsg, Acceptor>,
    // an auxiliary function mapping CMsg to its receiver
    receiver_cmsg: map<CMsg, Acceptor>,
    // an auxiliary function mapping each acceptor to a ballot number
    acceptor_ballot: map<Acceptor, int>
)

// define the constraints for the types of a state components
ghost predicate type_ok(s: TSState){
    && s.leader_ballot.Keys == s.leader_propose.Keys == s.leader_decision.Keys 
        == s.promise_count.Keys == s.decision_count.Keys == leaders
    && s.acceptor_state.Keys == s.pmsgs.Keys == s.cmsgs.Keys == s.acceptor_ballot.Keys == acceptors
    //&& forall n :: n in leaders ==> (forall v :: v in s.ballot_count[n].Keys ==> v >= -1)
    //&& (forall bn :: s.ballot_mapping[bn] in leaders)
}
// define what a valid state is in a Paxos run
// we may also add invariants into this predicate later
ghost predicate valid(s: TSState) /// the list of invariants for all states
  requires type_ok(s)
{
    //true
    //&& forall n :: n in leaders ==> (s.leader_propose[n] != 0 ==> 
    //  (|| (exists m :: m in leaders && m != n && s.leader_propose[m] == s.leader_propose[n])
    //   || |s.promise_count[n]| >= F+1 ))
    //&& forall n, m :: n in leaders && m in leaders && s.leader_propose[n] != 0 && s.leader_propose[m] != 0 ==> s.leader_propose[n] == s.leader_propose[m] 
   && s.ballot >= 0
   && s.counter >= 0
   && (forall n :: n in leaders && s.leader_ballot[n] != -1 ==> s.leader_ballot[n] >= 0)
   && (forall n :: n in leaders ==> s.leader_ballot[n] < s.ballot)
   && (forall n :: n in leaders ==> (s.leader_decision[n] != 0) ==> (|s.decision_count[n]| >= F+1)) 
   && (forall n :: n in leaders ==> (s.leader_decision[n] != 0) ==> (s.leader_propose[n] == s.leader_decision[n]))
   && (forall n :: n in leaders ==> (s.leader_propose[n] != 0) ==> s.leader_ballot[n] != -1)
   //&& (forall n :: n in leaders ==> (s.leader_decision[n] != 0) ==> 
   //  (forall m :: m in leaders && s.leader_ballot[m] >= s.leader_ballot[n] && s.leader_decision[m] != 0 ==> s.leader_decision[m] == s.leader_decision[n]))
   //&& (forall m :: m in leaders && |s.decision_count[m]| >= F+1 ==> |(set x | x in s.cmsgs && x.ballot == s.leader_ballot[m])| >= F+1)
   ////&& (forall m :: m in leaders ==> (s.decision_count[m] <= (set a | a in acceptors && exists x :: x in s.cmsgs && x.ballot == s.leader_ballot[m] && x.acc == a)))
   //&& (forall m :: m in leaders ==> (s.promise_count[m] <= (set a | a in acceptors && exists x :: x in s.pmsgs && x.ballot == s.leader_ballot[m] && x.value == 0 && x.acc == a)))
   && (forall n :: n in leaders ==> (s.leader_propose[n] != 0) ==> ( //true
      || |s.promise_count[n]| >= F + 1
      || exists a, h :: a in acceptors && PMsg(s.leader_ballot[n], h, s.leader_propose[n]) in s.pmsgs[a] //&& s.leader_propose[n] != 0
      ))
       // the base case for leader_proposal lemma
   && (forall n :: n in leaders ==> (s.leader_ballot[n] == 0 && s.leader_propose[n] != 0) ==> |s.promise_count[n]| >= F + 1)
   // the inductive case for the leader_proposal lemma: we defer the following conditions
   //&& (forall n :: n in leaders && s.leader_ballot[n] > 0 ==> (exists n' :: n' in leaders && s.leader_ballot[n'] == s.leader_ballot[n] - 1))
   && (|s.ballot_mapping| == s.ballot)
   && (forall bn :: bn >= 0 && bn < s.ballot ==> s.ballot_mapping[bn] in leaders)
   && (forall bn :: bn >= 0 && bn < s.ballot ==> s.leader_ballot[s.ballot_mapping[bn]] == bn)

   && (forall bn, v, a :: a in acceptors && v != 0 ==> ((CMsg(bn, v) in s.cmsgs[a]) ==> s.acceptor_state[a].value == v)) 
   //&& (forall v, a :: a in acceptors && v != 0 && s.acceptor_state[a].value == v ==> (exists bn :: CMsg(bn, v) in s.cmsgs[a]))
   && (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v != 0 ==> s.acceptor_state[a].value == v)
   //&& (forall a1, a2 :: a1 in acceptors && a2 in acceptors && s.acceptor_state[a1].value != 0 && s.acceptor_state[a2].value != 0 ==> s.acceptor_state[a1].value == s.acceptor_state[a2].value) // this will be violated if a leader is dishonest
   //&& (forall a, bn, v :: a in acceptors && (CMsg(bn, v) in s.cmsgs[a]) ==> (exists n :: n in leaders && s.leader_propose[n] == v)) // same as above
   //&& (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v != 0 ==> (exists n :: n in leaders && s.leader_propose[n] == v))
   //// The following two conditions connects PMsg(bn, h, v) to the existence of n in leaders :: s.leader_ballot[n] <= s.acceptor_state[a].highest
   && (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v != 0 ==> h < bn && s.acceptor_state[a].highest > -1 && s.acceptor_state[a].value == v)
   && (forall a :: a in acceptors && s.acceptor_state[a].highest > -1 ==> (exists n :: n in leaders && s.leader_ballot[n] > -1 && s.leader_ballot[n] <= s.acceptor_state[a].highest))
   //&& (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v != 0 ==> (exists n :: n in leaders && s.leader_ballot[n] > -1 && s.leader_ballot[n] <= h)) // the quantification on h maybe too general
   //&& (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v != 0 && h != -1 ==> (exists old_h :: PMsg(h, old_h, v) in s.pmsgs[a])) // this requires a second order predicates on states
   && (forall bn, v, a :: a in acceptors && CMsg(bn, v) in s.cmsgs[a] && v > 0 ==> (exists n :: n in leaders && s.leader_propose[n] == v && s.leader_ballot[n] == bn)) // if (bn, v) is confirmed, then some leader with bn has proposed v
   /*&& (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v != 0 ==> (h < bn && (
      || (exists h' :: PMsg(h, h', v) in s.pmsgs[a])
      || CMsg(h, v) in s.cmsgs[a]
      )))*/
   //&& (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v != 0 ==> s.leader_propose[s.receiver_pmsg[PMsg(bn, h, v)]] == v)
   && (forall a :: a in acceptors ==> s.acceptor_state[a].highest >= s.acceptor_ballot[a])
   // now connect to highest for all PMsg(bn, h, v) when v > 0
}

// the initial state when a protocol round starts
ghost predicate init(s: TSState)
  requires type_ok(s)
{
    && s.ballot == 0
    && s.counter == 0
    && (forall n :: n in leaders ==> s.leader_ballot[n] == -1)
    && (forall n :: n in leaders ==> s.leader_propose[n] == 0)
    && (forall n :: n in leaders ==> s.leader_decision[n] == 0)
    && (forall n :: n in leaders ==> s.decision_count[n] == {})
    && (forall a :: a in acceptors ==> s.acceptor_state[a] == AState(-1, 0))
    && (forall n :: n in leaders ==> s.promise_count[n] == {})
    && (forall n :: n in leaders ==> s.decision_count[n] == {})
    && (forall a :: a in acceptors ==> s.pmsgs[a] == {})
    && (forall a :: a in acceptors ==> s.cmsgs[a] == {})
    && (forall a :: a in acceptors ==> s.acceptor_ballot[a] == -1)
    && s.ballot_mapping == []
}
lemma Inv_init(s: TSState)
  requires type_ok(s) && init(s)
  ensures valid(s)
{
  //assert forall n :: n in leaders ==> |s.decision_count[n]| == 0;
  //assert forall n :: n in leaders ==> |s.promise_count[n]| == 0;
}

// In the following we define a transition relation for each step following the Paxos protocol.
//
// Step 1a: a leader (coordinator) chooses a ballot number & sends it to every acceptor. 
// This ballot number may be received by an acceptor sometime later, 
// which is modelled by (an acceptor later) looking into the leader_ballot component.
predicate choose_ballot(s: TSState, s': TSState, c: Acceptor)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders 
{
    && s.leader_ballot[c] == -1 // leader n has not chosen any ballot before
    && s'.leader_ballot == s.leader_ballot[c:= s.ballot] // n is now associated with a ballot
    && s'.ballot == s.ballot + 1
    && s.leader_propose[c] == 0
    && s.leader_decision[c] == 0
    && s.promise_count[c] == {}
    && s.decision_count[c] == {} // c hasn't made any decision yet ???
    // there is so far no messages in s.pmsgs and s.cmsgs that are related to c's ballot // I comment out this part for now
    //&& (forall a, x :: a in acceptors && x in s.pmsgs[a] ==> x.ballot != s.leader_ballot[c])
    //&& (forall a, x :: a in acceptors && x in s.cmsgs[a] ==> x.ballot != s.leader_ballot[c])
    // all the other state components remain the same
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.acceptor_state == s.acceptor_state
    && s'.promise_count == s.promise_count
    && s'.decision_count == s.decision_count
    && s'.pmsgs == s.pmsgs
    && s'.cmsgs == s.cmsgs
    && s'.ballot_mapping == s.ballot_mapping + [c]
    && s'.counter == s.counter + 1
    && s'.receiver_pmsg == s.receiver_pmsg
    && s'.receiver_cmsg == s.receiver_cmsg
    && s'.acceptor_ballot == s.acceptor_ballot
}
lemma Inv_choose_ballot(s: TSState, s': TSState, c: Acceptor)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && choose_ballot(s, s', c)
  ensures valid(s')
{
  //assert forall v, a :: a in acceptors && v != 0 && s.acceptor_state[a].value == v ==> (exists bn :: CMsg(bn, v) in s.cmsgs[a]);
  //assert s'.leader_ballot[c] == s'.ballot - 1;
}
// Step 1b: an acceptor may receive a ballot number sent from a leader (coordinator) sometime later
// In this case, if the ballot number is higher than the acceptor's highest recorded ballot, it will make a promise.
// Otherwise, the acceptor will not do anything.
// There are two possible cases here: 
// (1) the acceptor has not yet confirmed any value (if acceptor_state[a].value == 0); the acceptor will make a promise on that ballot number.
// (2) the acceptor has already confirmed some value previously; the acceptor will reply with a non-zero value that is previously confirmed for the current ballot
predicate receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors
{
    && s.leader_ballot[c] >= 0 // != -1 // leader n already has a ballot
    && s.acceptor_state[a].highest < s.leader_ballot[c] // acceptor a has not yet promised a ballot >= c 's ballot
    // acceptor a sends out a message that contains c's ballot number as a promise
    // in this case, the second value being 0 means that the acceptor has not yet sent out any confirmation so far
    && s'.pmsgs[a] == s.pmsgs[a] + {PMsg(s.leader_ballot[c], s.acceptor_state[a].highest, s.acceptor_state[a].value)} 
    // acceptor a updates its highest (ballot, value) pair received so far --- 
    && s'.acceptor_state == s.acceptor_state[a := AState(s.leader_ballot[c], s.acceptor_state[a].value)]
    // all the other state components remain the same
    && s'.leader_ballot == s.leader_ballot
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.ballot == s.ballot
    && (forall a' :: a' in acceptors && a' != a ==> s'.pmsgs[a'] == s.pmsgs[a'])
    && s'.cmsgs == s.cmsgs
    && s'.promise_count == s.promise_count
    && s'.decision_count == s.decision_count
    && s'.ballot_mapping == s.ballot_mapping
    && s'.counter == s.counter + 1    
    && s'.receiver_pmsg == s.receiver_pmsg[PMsg(s.leader_ballot[c], s.acceptor_state[a].highest, s.acceptor_state[a].value) := c]
    && s'.receiver_cmsg == s.receiver_cmsg
    && s'.acceptor_ballot == s.acceptor_ballot
}
lemma Inv_receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_higher_ballot(s, s', c, a)
  ensures valid(s')
{
  assert valid(s);
  assert s.leader_ballot[c] >= 0;
  assert s'.leader_ballot[c] >= 0;
  assert s'.leader_ballot[c] <= s'.acceptor_state[a].highest;
  //assert forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s'.pmsgs[a] && v != 0 ==> (exists n :: n in leaders && s'.leader_ballot[n] >= 0 && s'.leader_ballot[n] <= h);
  /*if s.acceptor_state[a].value == 0 {
    assert valid(s');
  } else {
    assert s.leader_ballot[c] >= 0; // this branch is problematic
  }*/
//  assert (forall bn, h, v :: PMsg(bn, h, v) in s.pmsgs[a] && v != 0 ==> (exists n :: n in leaders && s.leader_propose[n] == v)); // PMsg(bn, h, s.acceptor_state[a].value) does not exist in state s
//  assert s.acceptor_state[a].value != 0 ==> (exists c' :: c' in leaders && s.leader_propose[c'] == s.acceptor_state[a].value);
}

// Before step 2a: message 1b received by a leader (copied from pmsg)
ghost predicate receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors 
{
    && (exists highest :: PMsg(s.leader_ballot[c], highest, value) in s.pmsgs[a])
    && s.leader_decision[c] == 0 // leader c has not yet reached a decision
    && s.leader_propose[c] == 0
    // leader c has chosen a ballot (i.e. c has progressed through step 1a)
    && s.leader_ballot[c] != -1
    && ( 
      || (value != 0 && s'.leader_propose == s.leader_propose[c:= value]) // the force case: the acceptor has already confirmed a value
      // the promise_count only makes sense when it is not a force case, otherwise the leader simply follows what's decided by the system
      || (value == 0 && s'.leader_propose == s.leader_propose && s'.promise_count == s.promise_count[c:= s.promise_count[c]+{a}])
    )
    // all the other state components remain the same
    && s'.leader_ballot == s.leader_ballot
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.ballot == s.ballot
    && s'.acceptor_state == s.acceptor_state
    && s'.decision_count == s.decision_count
    && s'.pmsgs == s.pmsgs
    && s'.cmsgs == s.cmsgs
    && s'.ballot_mapping == s.ballot_mapping
    && s'.counter == s.counter + 1
    && s'.receiver_pmsg == s.receiver_pmsg
    && s'.receiver_cmsg == s.receiver_cmsg
    && s'.acceptor_ballot == s.acceptor_ballot
}
////lemma{:axiom} acceptor_membership(s: TSState, c: Acceptor, a: Acceptor)
////  requires type_ok(s) && valid(s) && c in leaders && a in acceptors
////  ensures (exists bn :: PMsg(s.leader_ballot[c], bn, 0, a) in s.pmsgs) ==> a in (set a | a in acceptors && exists x :: x in s.pmsgs && x.ballot == s.leader_ballot[c] && x.value == 0 && x.acc == a)
//{}

lemma Inv_receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_response_1b(s, s', c, a, value)
  ensures valid(s')
{
  //acceptor_membership(s, c, a);
  //assert PMsg(s.leader_ballot[c], highest, value, a) in s.pmsgs; 
  //assert a in (set a | a in acceptors && exists x :: x in s.pmsgs && x.ballot == s.leader_ballot[c] && x.value == 0 && x.acc == a);
}

// Step 2a, scenario 1: if a leader with a ballot number bn has collected at least F+1 promise counts, 
// it will propose a new value to all acceptors by updating leader_propose
ghost predicate propose_value_2a(s: TSState, s': TSState, c: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && value != 0
{
    && |s.promise_count[c]| >= F+1
    && s.leader_ballot[c] != -1
    && s.leader_propose[c] == 0
    && s.leader_decision[c] == 0
    && s'.leader_propose == s.leader_propose[c:= value]
    // all the other state components remain the same
    && s'.leader_ballot == s.leader_ballot
    && s'.leader_decision == s.leader_decision
    && s'.ballot == s.ballot
    && s'.acceptor_state == s.acceptor_state
    && s'.promise_count == s.promise_count
    && s'.decision_count == s.decision_count
    && s'.pmsgs == s.pmsgs
    && s'.cmsgs == s.cmsgs
    && s'.ballot_mapping == s.ballot_mapping
    && s'.counter == s.counter + 1
    && s'.receiver_pmsg == s.receiver_pmsg
    && s'.receiver_cmsg == s.receiver_cmsg
    && s'.acceptor_ballot == s.acceptor_ballot
}
lemma Inv_propose_value_2a(s: TSState, s': TSState, c: Acceptor, value: Proposal)
  requires  type_ok(s) && type_ok(s') && valid(s) && c in leaders && value != 0 && propose_value_2a(s, s', c, value)
  ensures valid(s')
{} // comment out for the moment

// Step 2a, scenario 2: if a leader with a ballot number bn has received a message 1b that contains some previous confirmed value
// the leader will propose the same value (the force case). 
// We do not need to define a new predicate for this behaviour as it is already encoded in the "receive_response_1b" predicate


// Step 2b, an acceptor replies with an cmsg if it receives a value with a large enough ballot number 
ghost predicate confirm_ballot_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value != 0
{
    && s.leader_ballot[c] == s.acceptor_state[a].highest
    && s.leader_propose[c] == value 
    && ((s.acceptor_state[a].value == value && s'.acceptor_ballot == s.acceptor_ballot) 
       || (s.acceptor_state[a].value == 0 && s'.acceptor_ballot == s.acceptor_ballot[a := s.leader_ballot[c]]))
    && s'.acceptor_state == s.acceptor_state[a := AState(s.leader_ballot[c], value)]
    && s'.cmsgs == s.cmsgs[a := s.cmsgs[a] + {CMsg(s.leader_ballot[c], value)}]
    // all the other state components remain the same
    && s'.leader_ballot == s.leader_ballot
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.ballot == s.ballot
    && s'.promise_count == s.promise_count
    && s'.decision_count == s.decision_count
    && s'.pmsgs == s.pmsgs
    && s'.ballot_mapping == s.ballot_mapping
    && s'.counter == s.counter + 1
    && s'.receiver_pmsg == s.receiver_pmsg
    && s'.receiver_cmsg == s.receiver_cmsg[CMsg(s.leader_ballot[c], value) := c]
}
lemma subset_predicate(s1 : set<CMsg>, s2: set<CMsg>, ballot: int) // to simplify these lemmas later ...
  requires s1 <= s2
  ensures (set x | x in s1 && x.ballot == ballot) <= (set x | x in s2 && x.ballot == ballot)
{}
lemma{:axiom} subset_less(s1 : set<CMsg>, s2: set<CMsg>) // Dafny cannot directly access the size of a set
  requires s1 <= s2
  ensures |s1| <= |s2|

lemma Inv_confirm_ballot_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value != 0
  requires confirm_ballot_2b(s, s', c, a, value)
  ensures valid(s')
{
  //assert |s.decision_count[c]| <= |(set x | x in s.cmsgs && x.ballot == s.leader_ballot[c])|;
  //assert |s.decision_count[c]| == |s'.decision_count[c]|;
  //assert s.cmsgs <= s'.cmsgs;
  //assert s.leader_ballot[c] == s'.leader_ballot[c];
  //subset_predicate(s.cmsgs, s'.cmsgs, s.leader_ballot[c]);
  //subset_less((set x | x in s.cmsgs && x.ballot == s.leader_ballot[c]), (set x | x in s'.cmsgs && x.ballot == s'.leader_ballot[c]));
  //assert |(set x | x in s.cmsgs && x.ballot == s.leader_ballot[c])| <= |(set x | x in s'.cmsgs && x.ballot == s'.leader_ballot[c])|;
  //assert |s'.decision_count[c]| <=  |(set x | x in s'.cmsgs && x.ballot == s'.leader_ballot[c])|;
  //assert forall m :: m in leaders ==> |s'.decision_count[m]| <=  |(set x | x in s'.cmsgs && x.ballot == s'.leader_ballot[m])|;
}

// Before step 3a: message received by a leader (copied from cmsg)
ghost predicate receive_confirm_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value != 0
{
    && CMsg(s.leader_ballot[c], value) in s.cmsgs[a] 
    && s.leader_decision[c] == 0 // c has not yet made a decision
    && s'.decision_count == s.decision_count[c:= s.decision_count[c]+{a}]
    // all the other state components remain the same
    && s'.acceptor_state == s.acceptor_state
    && s'.leader_ballot == s.leader_ballot
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.ballot == s.ballot
    && s'.promise_count == s.promise_count
    && s'.pmsgs == s.pmsgs
    && s'.cmsgs == s.cmsgs
    && s'.ballot_mapping == s.ballot_mapping
    && s'.counter == s.counter + 1
    && s'.receiver_pmsg == s.receiver_pmsg
    && s'.receiver_cmsg == s.receiver_cmsg
    && s'.acceptor_ballot == s.acceptor_ballot
}
lemma Inv_receive_confirm_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, bn: int, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value != 0
  requires receive_confirm_2b(s, s', c, a, value)
  ensures valid(s')
{}

// Step 3a, a leader with a ballot number bn has collected at least F+1 decision counts
ghost predicate leader_decide(s: TSState, s': TSState, c: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && value != 0
{
    && |s.decision_count[c]| >= F+1 && s.leader_decision[c] == 0 && s.leader_propose[c] == value
    && s'.leader_decision == s.leader_decision[c := value]
    // all the other state components remain the same
    && s'.acceptor_state == s.acceptor_state
    && s'.leader_ballot == s.leader_ballot
    && s'.leader_propose == s.leader_propose
    && s'.ballot == s.ballot
    && s'.promise_count == s.promise_count
    && s'.decision_count == s.decision_count
    && s'.pmsgs == s.pmsgs
    && s'.cmsgs == s.cmsgs
    && s'.ballot_mapping == s.ballot_mapping
    && s'.counter == s.counter + 1
    && s'.receiver_pmsg == s.receiver_pmsg
    && s'.receiver_cmsg == s.receiver_cmsg
    && s'.acceptor_ballot == s.acceptor_ballot
}
lemma Inv_leader_decide(s: TSState, s': TSState, c: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && value != 0
  requires leader_decide(s, s', c, value)
  ensures valid(s')
{}

ghost predicate transition(s: TSState, s': TSState)
  requires type_ok(s) && type_ok(s') && valid(s)
{
  || (exists c :: c in leaders && choose_ballot(s, s', c))
  || (exists c, a :: c in leaders && a in acceptors && receive_higher_ballot(s, s', c, a))
  || (exists c, a, value :: c in leaders && a in acceptors && receive_response_1b(s, s', c, a, value))
  || (exists c, value :: c in leaders && value != 0 && propose_value_2a(s, s', c, value))
  || (exists c, a, value :: c in leaders && a in acceptors && value != 0 && receive_confirm_2b(s, s', c, a, value))
  || (exists c, a, value :: c in leaders && a in acceptors && value != 0 && confirm_ballot_2b(s, s', c, a, value))
  || (exists c, value :: c in leaders && value != 0 && leader_decide(s, s', c, value))
}

// Once a leader c makes a proposal v, then c stick to that proposal
lemma leader_proposal(s: TSState, s': TSState, c: Acceptor)
  requires type_ok(s) && type_ok(s') && valid(s) 
  requires transition(s, s')
  requires c in leaders && s.leader_propose[c] != 0
  ensures s.leader_propose[c] == s'.leader_propose[c]
{}
ghost predicate acceptor_pmsg(s: TSState, a: Acceptor, bn: int, highest: int, v: Proposal)
  requires type_ok(s) && a in acceptors && v != 0 && PMsg(bn, highest, v) in s.pmsgs[a]
{
  && (exists n :: n in leaders && s.leader_propose[n] == v)
  //&& s.acceptor_state[a].value == v
}
// Once an acceptor sends out PMsg(bn, highest, v), then it is from a leader's proposal
lemma acceptor_msg_inv(s: TSState, s': TSState, a: Acceptor, bn: int, highest: int, v: Proposal)
  requires type_ok(s) && type_ok(s') && valid(s) && a in acceptors && v != 0 && PMsg(bn, highest, v) in s.pmsgs[a] && acceptor_pmsg(s, a, bn, highest, v)
  requires transition(s, s')
  ensures acceptor_pmsg(s', a, bn, highest, v)
{
  //var c :| c in leaders && s.leader_propose[c] == v;
} 
// Once an acceptor decides a value v != 0, then it sticks to that value 
lemma acceptor_state_inv(s: TSState, s': TSState, a: Acceptor)
  requires type_ok(s) && type_ok(s') && valid(s) 
  requires transition(s, s')
  requires a in acceptors && s.acceptor_state[a].value != 0
  ensures s.acceptor_state[a].value == s'.acceptor_state[a].value 
{}

//&& (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v != 0 && h != -1 ==> (exists old_h :: PMsg(h, old_h, v) in s.pmsgs[a])) // this requires a second order predicates on states
// next we need to prove that if PMsg(bn, h , v) in s.pmsgs[a] && v != 0 && h != -1, then there exists PMsg(h, old_h, v) in s.pmsgs[a], because PMsg(h, old_h, v) in s''.pmsgs[a] for some pre-state s''
/*
lemma pmsg_value(s': TSState, s: TSState, a: Acceptor, bn: int, h: int, v: Proposal)
  requires type_ok(s') && type_ok(s) && valid(s') && transition(s', s) && a in acceptors
  requires PMsg(bn, h , v) in s.pmsgs[a] && v != 0 && h != -1
  ensures  (exists old_h :: PMsg(h, old_h, v) in s.pmsgs[a])
{

  if s.counter == 0 {

  } else if ! (PMsg(bn, h , v) in s'.pmsgs[a]) {
    //assert s'.acceptor_state[a].highest == v;
    assert exists c :: receive_higher_ballot(s', s, c, a);
  }
}*/

lemma first_leader_proposal(s: TSState, c: Acceptor)
  requires type_ok(s) && valid(s)
  requires c in leaders && s.leader_ballot[c] == 0 && s.leader_propose[c] != 0
  ensures |s.promise_count[c]| >= F + 1
{}
// forall n :: n in leaders && s.leader_ballot[n] > 0 ==> (exists n' :: n' in leaders && s.leader_ballot[n'] == s.leader_ballot[n] - 1)
/*lemma increment_ballot(s: TSState, c: Acceptor)
  requires type_ok(s) && valid(s)
  requires c in leaders && s.leader_ballot[c] > 0 
  ensures exists c' :: c' in leaders && s.leader_ballot[c'] == s.leader_ballot[c] - 1
{}*/

/*
////    assert |s.promise_count[c]| < F + 1 ==> (var c' :| c' in leaders && (s.leader_ballot[c'] == s.leader_ballot[c] - 1) && all_leader_proposal(s, c'));
lemma all_leader_proposal(s: TSState, c: Acceptor)
  requires type_ok(s) && valid(s)
  requires c in leaders && s.leader_propose[c] != 0
  ensures  exists c' :: c' in leaders && s.leader_ballot[c'] <= s.leader_ballot[c] && |s.promise_count[c']| >= F + 1
  decreases s.leader_ballot[c]
{
  assert s.leader_ballot[c] >= 0;
  assert s.leader_ballot[c] < s.ballot;
  if s.leader_ballot[c] == 0
  {
    first_leader_proposal(s, c);
  } else if |s.promise_count[c]| >= F + 1 {

  }
  else
  {
    assert s.leader_ballot[c] < s.ballot;
    assert s.ballot > 0;
    assert s.ballot_mapping[s.leader_ballot[c] - 1] in leaders;
    var c' := s.ballot_mapping[s.leader_ballot[c] - 1];
    assert s.leader_ballot[c'] == s.leader_ballot[c] - 1;
    all_leader_proposal(s, c');
  }
}
*/

/*
lemma inv_lemma(s: TSState, s': TSState)
  requires type_ok(s) && type_ok(s') && valid(s) 
  requires transition(s, s')
  ensures valid(s')
{
  //leader_proposal(s, s');
}*/

lemma consistency(s: TSState, c1: Acceptor, c2: Acceptor)
  requires type_ok(s)
  requires c1 in leaders && c2 in leaders && (s.leader_decision[c1] != 0) && (s.leader_decision[c2] != 0)
  ensures s.leader_decision[c1] == s.leader_decision[c2]
{}

/* Why do we have consistency for Paxos? Intuitively, it could be understood in the following way.
   If there is a ballot bn that is observed as having been decided with value v, then
   (1) there must be at least F + 1 acceptors promised in Step 1b that they will only reply to a ballot number greater than or equal to bn, and
   (2) At least F+1 acceptors have sent out a confirm reply in Step 2b in response to the proposer with ballot number bn for v. 
   
   Therefore, for all other ballots bn' < bn, those acceptors will not reply to the request with bn'; and for all new ballot bn'' >= bn, 
   those acceptors will reply with (bn'', highest, v) in step-1b since they have previously confirmed value v. 
   (Note they cannot all go faulty which is against our assumption) Since the leader with bn'' is honest, 
   he will be forced in Step 2a to propose v (with bn'') if it receives at least one step-1b message with a confirmed v; 
   He will not propose a different value unless it has not received any step-1b message with a confirmed v. 
   (Intuitively, that value "v" should have already been confirmed by the system but it may still be waiting 
   for a proposer to "announce" that it is confirmed. In such a scenario, we say "v" has been "decided" by the system,
   which may serve as an invariant in a consistency proof.)

   In general, we cannot distinguish the case when a user is faulty and the case that a message from or to that user is taking too long. 
 */
