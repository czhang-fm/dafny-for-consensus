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

module Paxos_protocol {
  type Acceptor(==)  // a set of acceptors (nodes)
  type Proposal = int // the value that is proposed by some leader, 0 by default, but 0 is not considered a valid decision.
  const acceptors: set<Acceptor>
  const leaders: set<Acceptor>
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
    // an auxiliary function mapping each acceptor to a ballot number which decides the acceptor's current confirmed value
    acceptor_ballot: map<Acceptor, int>
  )

  // define the constraints for the types of a state components
  ghost predicate type_ok(s: TSState){
    && s.leader_ballot.Keys == s.leader_propose.Keys == s.leader_decision.Keys 
        == s.promise_count.Keys == s.decision_count.Keys == leaders
    && s.acceptor_state.Keys == s.pmsgs.Keys == s.cmsgs.Keys == s.acceptor_ballot.Keys == acceptors
    && F > 0 // We assume there are at least 3 acceptors in the protocol
  }

  // the initial state when a protocol round starts
  ghost predicate init(s: TSState)
  requires type_ok(s)
  {
    && s.ballot == 0
    && (forall c :: c in leaders ==> s.leader_ballot[c] == -1)
    && (forall c :: c in leaders ==> s.leader_propose[c] == 0)
    && (forall c :: c in leaders ==> s.leader_decision[c] == 0)
    && (forall c :: c in leaders ==> s.decision_count[c] == {})
    && (forall a :: a in acceptors ==> s.acceptor_state[a] == AState(-1, 0))
    && (forall c :: c in leaders ==> s.promise_count[c] == {})
    && (forall c :: c in leaders ==> s.decision_count[c] == {})
    && (forall a :: a in acceptors ==> s.pmsgs[a] == {})
    && (forall a :: a in acceptors ==> s.cmsgs[a] == {})
    && (forall a :: a in acceptors ==> s.acceptor_ballot[a] == -1)
    && s.ballot_mapping == []
  }

  // In the following we define a transition relation for each step following the Paxos protocol.
  //
  // Step 1a: a leader (coordinator) chooses a ballot number & sends it to every acceptor. 
  // This ballot number may be received by an acceptor sometime later, 
  // which is modelled by (an acceptor later) looking into the s.leader_ballot[c] component.
  predicate choose_ballot(s: TSState, s': TSState, c: Acceptor)
  requires type_ok(s) && type_ok(s') && c in leaders 
  {
    && s.leader_ballot[c] == -1 // leader n has not chosen any ballot before
    && s'.leader_ballot == s.leader_ballot[c:= s.ballot] // n is now associated with a ballot
    && s'.ballot == s.ballot + 1
    && s.leader_propose[c] == 0
    && s.leader_decision[c] == 0 // c hasn't made any decision yet
    && s.promise_count[c] == {}
    && s.decision_count[c] == {}  
    // all the other state components remain the same
    && s'.leader_propose == s.leader_propose
    && s'.leader_decision == s.leader_decision
    && s'.acceptor_state == s.acceptor_state
    && s'.promise_count == s.promise_count
    && s'.decision_count == s.decision_count
    && s'.pmsgs == s.pmsgs
    && s'.cmsgs == s.cmsgs
    && s'.ballot_mapping == s.ballot_mapping + [c]
    && s'.acceptor_ballot == s.acceptor_ballot
  }

  // Step 1b: an acceptor receives a ballot number sent from a leader (coordinator) 
  // In this case, if the ballot number is higher than the acceptor's highest recorded ballot, it will make a promise.
  // Otherwise, the acceptor will not do anything.
  // There are two possible cases here: 
  // (1) the acceptor has not yet confirmed any value (if acceptor_state[a].value == 0); the acceptor will make a promise PMsg(bn, -1, 0) on that ballot number bn.
  // (2) the acceptor has already confirmed some value previously; the acceptor will reply with a non-zero value that is previously confirmed 
  predicate receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor)
  requires type_ok(s) && type_ok(s') && c in leaders && a in acceptors
  {
    && s.leader_ballot[c] >= 0 // != -1 // leader n already has a ballot
    && s.acceptor_state[a].highest < s.leader_ballot[c] // acceptor a has not yet promised a ballot >= c 's ballot
    // acceptor a sends out a message that contains c's ballot number as a promise
    // in this case, the second value being 0 means that the acceptor has not yet sent out any confirmation so far
    && s'.pmsgs == s.pmsgs[a := s.pmsgs[a] + {PMsg(s.leader_ballot[c], s.acceptor_state[a].highest, s.acceptor_state[a].value)}]
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
    && s'.ballot_mapping == s.ballot_mapping
    && s'.acceptor_ballot == s.acceptor_ballot
  }

  // Before step 2a: message 1b received by a leader (copied from pmsg)
  ghost predicate receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && c in leaders && a in acceptors 
  {
    && (exists highest :: PMsg(s.leader_ballot[c], highest, value) in s.pmsgs[a])
    && s.leader_decision[c] == 0 // leader c has not yet reached a decision
    && s.leader_propose[c] == 0
    // leader c has chosen a ballot (i.e. c has progressed through step 1a)
    && s.leader_ballot[c] >= 0
    && ( 
      || (value > 0 && s'.leader_propose == s.leader_propose[c:= value]) // the force case: the acceptor has already confirmed a value
      // the promise_count only makes sense when it is not a force case, otherwise the leader simply follows what's decided by the system
      || (value == 0 && s'.leader_propose == s.leader_propose && s'.promise_count == s.promise_count[c:= s.promise_count[c]+{a}]) // the free case:
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
    && s'.acceptor_ballot == s.acceptor_ballot
  }

  // Step 2a, scenario 1: if a leader with a ballot number bn has collected at least F+1 promise counts, 
  // it will propose a new value to all acceptors by updating leader_propose
  ghost predicate propose_value_2a(s: TSState, s': TSState, c: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && c in leaders 
  {
    && |s.promise_count[c]| >= F+1
    && s.leader_ballot[c] >= 0
    && s.leader_propose[c] == 0
    && s.leader_decision[c] == 0
    && value > 0
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
    && s'.acceptor_ballot == s.acceptor_ballot
  }

  // Step 2a, scenario 2: if a leader with a ballot number bn has received a message 1b that contains some previous confirmed value
  // the leader will propose the same value (the force case). 
  // We do not need to define a new predicate for this behaviour as it is already encoded in the "receive_response_1b" predicate


  // Step 2b, an acceptor replies with an cmsg if it receives a value with a large enough ballot number 
  ghost predicate confirm_ballot_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && c in leaders && a in acceptors && value > 0
  {
    && s.leader_ballot[c] >= s.acceptor_state[a].highest
    && s.leader_propose[c] == value 
    && ((s.acceptor_state[a].value == value && s'.acceptor_ballot == s.acceptor_ballot) // bookkeeping acceptor_ballot
       || (s.acceptor_state[a].value != value && s'.acceptor_ballot == s.acceptor_ballot[a := s.leader_ballot[c]])) 
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
  }

  // Before step 3a: message received by a leader (copied from cmsg)
  ghost predicate receive_confirm_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && c in leaders && a in acceptors && value > 0
  {
    && CMsg(s.leader_ballot[c], value) in s.cmsgs[a] 
    && value == s.leader_propose[c]
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
    && s'.acceptor_ballot == s.acceptor_ballot
  }

  // Step 3a, a leader with a ballot number bn has collected at least F+1 decision counts
  ghost predicate leader_decide(s: TSState, s': TSState, c: Acceptor, value: Proposal)
  requires type_ok(s) && type_ok(s') && c in leaders && value != 0
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
    && s'.acceptor_ballot == s.acceptor_ballot
  }

  ghost predicate transition(s: TSState, s': TSState)
  requires type_ok(s) && type_ok(s')
  {
    || (exists c :: c in leaders && choose_ballot(s, s', c))
    || (exists c, a :: c in leaders && a in acceptors && receive_higher_ballot(s, s', c, a))
    || (exists c, a, value :: c in leaders && a in acceptors && receive_response_1b(s, s', c, a, value))
    || (exists c, value :: c in leaders && value != 0 && propose_value_2a(s, s', c, value))
    || (exists c, a, value :: c in leaders && a in acceptors && value > 0 && receive_confirm_2b(s, s', c, a, value))
    || (exists c, a, value :: c in leaders && a in acceptors && value > 0 && confirm_ballot_2b(s, s', c, a, value))
    || (exists c, value :: c in leaders && value != 0 && leader_decide(s, s', c, value))
  }
}