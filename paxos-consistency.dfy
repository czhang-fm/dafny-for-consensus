include "paxos-classic.dfy"

module Consistency {

    import opened Paxos_protocol

    lemma{:axiom} Quorum()
    ensures |acceptors| == 2 * F + 1

    /* A few lemmas related to size of sets
     */
    lemma SubsetSize<T> (A1: set<T>, A2: set<T>)
    requires A1 <= A2
    ensures |A1| <= |A2|
    {
        if A1 == {}
        {}
        else {
            var a :| a in A1;
            SubsetSize(A1 - {a}, A2 - {a});
        }
    }
    lemma SizeSubset<T> (A1: set<T>, A2: set<T>)
    requires |A1| > |A2|
    ensures !(A1 <= A2){
        if |A2| == 0 {

        } else {
            var a :| a in A2;
            SizeSubset(A1 - {a}, A2 - {a});
        }
    }
    lemma Intersection<T> (A: set<T>, B: set<T>, C: set<T>)
    requires A <= C && B <= C 
    requires |A| > 0 && |B| > 0
    requires |A| + |B| > |C|
    ensures exists a :: a in A && a in B && a in C
    {
        SizeSubset(A, C-B);
    }
    lemma GetAcceptor(A: set<Acceptor>, B: set<Acceptor>) returns (a: Acceptor)
    requires A <= acceptors && |A| >= 1
    requires B <= acceptors && |B| >= 1
    requires |A| + |B| > 2 * F + 1
    ensures a in A && a in B
    {
        Quorum();
        assert |A| + |B| > |acceptors|;
        Intersection(A, B, acceptors);
        a :| a in A && a in B;
    }

    /** define what a valid state is in a Paxos run
        we will add invariants into this predicate later
     */
    ghost predicate valid(s: TSState) /// the list of invariants for all states
    requires type_ok(s)
    {
        && (forall c :: c in leaders && (s.leader_decision[c] > 0) ==> (|s.decision_count[c]| >= F+1)) 
        && (forall c :: c in leaders && (s.leader_decision[c] > 0) ==> (s.leader_propose[c] == s.leader_decision[c]))
        && (forall c :: c in leaders && s.leader_propose[c] > 0 ==> s.leader_ballot[c] >= 0)
        && (forall c :: c in leaders ==> (s.leader_propose[c] > 0) ==> ( // a proposed value from c is either from an acceptor, or by c itself if majority promises are collected 
            || |s.promise_count[c]| >= F + 1
            || exists a, h :: a in acceptors && PMsg(s.leader_ballot[c], h, s.leader_propose[c]) in s.pmsgs[a] //
            ))
        // if (bn, v) is confirmed, then some leader with bn has proposed v
        && (forall bn, v, a :: a in acceptors && CMsg(bn, v) in s.cmsgs[a] && v > 0 ==> (exists n :: n in leaders && s.leader_propose[n] == v && s.leader_ballot[n] == bn)) 
    }

    lemma Min_leader_decision(s: TSState, c1: Acceptor, c2: Acceptor)
    requires type_ok(s) && valid(s)
    requires c1 in leaders && c2 in leaders
    requires s.leader_ballot[c1] < s.leader_ballot[c2]
    requires s.leader_propose[c1] > 0 && (|set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| >= F + 1)
    requires forall c :: c in leaders  && s.leader_ballot[c] < s.leader_ballot[c1] ==> (|set a | a in acceptors && CMsg(s.leader_ballot[c], s.leader_propose[c]) in s.cmsgs[a]| <= F)
    ensures |s.promise_count[c2]| <= F
    {}

    /** the list of lemmas for the initial state and all the transitions, since it's easier to debug in this way.
     */
    lemma Inv_init(s: TSState)
    requires type_ok(s) && init(s)
    ensures valid(s)
    {}

    lemma Inv_choose_ballot(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && choose_ballot(s, s', c)
    ensures valid(s')
    {}

    lemma Inv_receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_higher_ballot(s, s', c, a)
    ensures valid(s')
    {}

    lemma Inv_receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_response_1b(s, s', c, a, value)
    ensures valid(s')
    {}

    lemma Inv_propose_value_2a(s: TSState, s': TSState, c: Acceptor, value: Proposal)
    requires  type_ok(s) && type_ok(s') && valid(s) && c in leaders && value != 0 && propose_value_2a(s, s', c, value)
    ensures valid(s')
    {}

    lemma Inv_confirm_ballot_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value > 0
    requires confirm_ballot_2b(s, s', c, a, value)
    ensures valid(s')
    {}

    lemma Inv_receive_confirm_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, bn: int, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value > 0
    requires receive_confirm_2b(s, s', c, a, value)
    ensures valid(s')
    {}

    lemma Inv_leader_decide(s: TSState, s': TSState, c: Acceptor, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && value != 0
    requires leader_decide(s, s', c, value)
    ensures valid(s')
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
    for a proposer to "announce" it. In such a scenario, we say "v" has been "decided" by the system,
    which needs to be represented by the invariants in our consistency proof.)

    In general, we cannot distinguish the case when a user is faulty and the case that a message from or to that user is taking too long. 
    */
}