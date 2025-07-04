include "paxos-classic.dfy"
include "auxiliary.dfy"
include "paxos-invariants.dfy"
// include "paxos-leader-ballot-invariants.dfy"

module Consistency {

    import opened Paxos_protocol
    import opened Auxiliary_lemmas
    import opened Invariants
    // import opened Leader_ballot_invariants

    lemma{:axiom} Quorum()
    ensures |acceptors| == 2 * F + 1

    lemma GetAcceptor<T>(A: set<Acceptor>, B: set<Acceptor>) returns (a: Acceptor)
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

    // // the base case of lemma Min_leader_decision
    // lemma Same_ballot_leaders(s: TSState, c1: Acceptor, c2: Acceptor)
    // requires type_ok(s) && valid(s) && valid_leader_ballot(s)
    // requires c1 in leaders && c2 in leaders
    // requires s.leader_ballot[c1] == s.leader_ballot[c2] >= 0
    // ensures c1 == c2
    // {}
    // // selecting a leader with the same proposal but a smaller ballot number in the induction step of lemma Min_leader_decision
    // lemma Select_leader_smaller_ballot(s: TSState, c1: Acceptor) returns (c2: Acceptor)
    // requires type_ok(s) && valid(s) && c1 in leaders
    // requires s.leader_propose[c1] > 0 && |s.promise_count[c1]| <= F
    // ensures c2 in leaders && s.leader_ballot[c2] < s.leader_ballot[c1] && s.leader_propose[c2] == s.leader_propose[c1]
    // {
    //     c2 :| c2 in leaders && s.leader_ballot[c2] < s.leader_ballot[c1] && s.leader_propose[c2] == s.leader_propose[c1];
    // }

    // lemma Min_leader_decision(s: TSState, c1: Acceptor, c2: Acceptor)
    // requires type_ok(s) && valid(s) && valid_leader_ballot(s)
    // requires c1 in leaders && c2 in leaders
    // requires s.leader_ballot[c1] <= s.leader_ballot[c2]
    // requires s.leader_propose[c1] > 0 && s.leader_propose[c2] > 0
    //     && (|set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| >= F + 1)
    // requires forall c :: c in leaders  && s.leader_ballot[c] < s.leader_ballot[c1] ==> 
    //     (|set a | a in acceptors && CMsg(s.leader_ballot[c], s.leader_propose[c]) in s.cmsgs[a]| <= F)
    // ensures s.leader_propose[c1] == s.leader_propose[c2]
    // //invariant s.leader_ballot[1] <= s.leader_ballot[2]
    // decreases s.leader_ballot[c2] - s.leader_ballot[c1]
    // {
    //     if s.leader_ballot[c2] == s.leader_ballot[c1]{
    //         // base case: when c2 == c1, then their proposal should be the same
    //         // assert c1 == c2;
    //         Same_ballot_leaders(s, c1, c2);
    //     } else { 
    //         // induction step:
    //         //assert s.leader_ballot[c2] > s.leader_ballot[c1];
    //         Conflict_confirm_promise(s, c1, c2); // rule out the first case of invariant X
    //         //assert exists c :: c in leaders && s.leader_ballot[c] < s.leader_ballot[c2] && s.leader_propose[c] == s.leader_propose[c2];
    //         //var c3 :| c3 in leaders && s.leader_ballot[c3] < s.leader_ballot[c2] && s.leader_propose[c3] == s.leader_propose[c2]; // this is from the second case of invariant X and invariant Y
    //         var c3 := Select_leader_smaller_ballot(s, c2);
    //         Min_leader_decision(s, c1, c3);
    //     }
    // }

    lemma Consistency(s: TSState, c1: Acceptor, c2: Acceptor)
    requires type_ok(s) && valid(s)
    requires c1 in leaders && c2 in leaders && (s.leader_decision[c1] > 0) && (s.leader_decision[c2] > 0)
    // ensures s.leader_decision[c1] == s.leader_decision[c2]
    // {}

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