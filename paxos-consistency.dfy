include "paxos-classic.dfy"
include "auxiliary.dfy"

module Consistency {

    import opened Paxos_protocol
    import opened Auxiliary_lemmas

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

    /** define what a valid state is in a Paxos run
        we will add invariants into this predicate later
     */
    ghost predicate valid(s: TSState) /// the list of invariants for all states
    requires type_ok(s)
    {
        // the followings are the variants that pick up basic features of the Paxos protocol to be used in the proof of the first lemma
        && (forall c :: c in leaders && (s.leader_decision[c] > 0) ==> (|s.decision_count[c]| >= F+1)) 
        && (forall c :: c in leaders && (s.leader_decision[c] > 0) ==> (s.leader_propose[c] == s.leader_decision[c]))
        && (forall c :: c in leaders && s.leader_propose[c] > 0 ==> s.leader_ballot[c] >= 0)
        && (forall c :: c in leaders ==> s.promise_count[c] <= acceptors)
        && (forall a, c :: a in acceptors && c in leaders && a in s.promise_count[c] ==> (exists h :: PMsg(s.leader_ballot[c], h, 0) in s.pmsgs[a]))
        && (forall a :: a in acceptors ==> s.acceptor_state[a].value >= 0)
//        && (forall a :: a in acceptors ==> !(PMsg(-1, -1, 0) in s.pmsgs[a])) //
//        && (forall a :: a in acceptors ==> s.acceptor_ballot[a] <= s.acceptor_state[a].highest) //
//        && (forall a, bn, value :: a in acceptors && CMsg(bn, value) in s.cmsgs[a] ==> bn <= s.acceptor_ballot[a]) //
//        && (forall a :: a in acceptors && s.acceptor_ballot[a] >= 0 ==> (s.acceptor_state[a].highest >= s.acceptor_ballot[a] && s.acceptor_state[a].value > 0)) //

        // if acceptor a sends a promise to c with a highest confirmed ballot -1, then acceptor a must not have sent confirm message to any leader with a smaller ballot
        && (forall a, bn, bn', h, value :: a in acceptors && 0 <= bn < bn' && (CMsg(bn, value) in s.cmsgs[a]) ==> 
               (!(PMsg(bn', h, 0) in s.pmsgs[a])))  //* (1) equivalent to the invariant (2)
        && (forall a :: a in acceptors ==> (s.acceptor_state[a].value > 0 ==> s.acceptor_state[a].highest >=0) )
        && (forall a, bn, highest, value :: a in acceptors && (PMsg(bn, highest, value) in s.pmsgs[a]) ==> (highest == -1 ==> value == 0))
        && (forall a :: a in acceptors && s.acceptor_state[a].value == 0 ==> s.cmsgs[a] == {})
        && (forall a, bn, highest, value  :: a in acceptors && (PMsg(bn, highest, value) in s.pmsgs[a]) ==> bn <= s.acceptor_state[a].highest)
        && (forall a, bn, bn', h, value :: a in acceptors && (CMsg(bn, value) in s.cmsgs[a]) && (PMsg(bn', h, 0) in s.pmsgs[a]) ==> bn >= bn') //* (2) equivalent to the invariant (1)

        // a proposed value from c is either from an acceptor, or by c itself if majority promises are collected 
        // (used for the induction step in the proof of the lemma Min_leader_decision)
        && (forall c :: c in leaders ==> (s.leader_propose[c] > 0) ==> ( 
            || |s.promise_count[c]| >= F + 1
            || exists a, h :: a in acceptors && PMsg(s.leader_ballot[c], h, s.leader_propose[c]) in s.pmsgs[a] // * invariant X
            ))
        // if (bn, v) is confirmed, then some leader with bn has proposed v
        && (forall bn, v, a :: a in acceptors && CMsg(bn, v) in s.cmsgs[a] && v > 0 ==> (exists n :: n in leaders && s.leader_propose[n] == v && s.leader_ballot[n] == bn)) 
        // the following invariants are required for the induction step in the proof of lemma Min_leader_decision
        && (forall a :: a in acceptors && s.acceptor_state[a].value > 0 ==> s.acceptor_state[a].highest >= 0)
        && (forall a :: a in acceptors && s.acceptor_state[a].value > 0 ==> (exists n :: n in leaders && s.leader_propose[n] == s.acceptor_state[a].value && s.leader_ballot[n] <= s.acceptor_state[a].highest))
        && (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v > 0 ==> 
           h < bn && (exists n :: n in leaders && 0 <= s.leader_ballot[n] <= h && s.leader_propose[n] == v)) // * invariant Y
    }

    // the following are invariants used in the proof of lemma Same_ballot_leaders (split from the main body of invariants)
    ghost predicate valid_leader_ballot(s: TSState) 
    requires type_ok(s)
    {
        && s.ballot >= 0 && s.ballot == |s.ballot_mapping|
        && (forall c :: c in leaders && s.leader_ballot[c] >= 0 ==> s.leader_ballot[c] < |s.ballot_mapping|)
        && (forall c :: c in leaders && s.leader_ballot[c] >= 0 ==> s.ballot_mapping[s.leader_ballot[c]] == c)
        && (forall c1, c2 :: c1 in leaders && c2 in leaders && s.leader_ballot[c1] == s.leader_ballot[c2] > 0 ==> c1 == c2)
    }

    lemma Conflict_confirm_promise(s: TSState, c1: Acceptor, c2: Acceptor)
    requires type_ok(s) && valid(s)
    requires c1 in leaders && c2 in leaders
    requires s.leader_ballot[c1] < s.leader_ballot[c2]
    requires s.leader_propose[c1] > 0 && (|set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| >= F + 1)
    ensures |s.promise_count[c2]| <= F
    {
        assert (set a | a in acceptors && (exists h :: PMsg(s.leader_ballot[c2], h, 0) in s.pmsgs[a])) <= acceptors - (set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]);
        Quorum();
        assert |acceptors - (set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a])| <= F;
        SubsetSize((set a | a in acceptors && (exists h :: PMsg(s.leader_ballot[c2], h, 0) in s.pmsgs[a])),
            acceptors - (set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]));
        //assert |(set a | a in acceptors && (exists h :: PMsg(s.leader_ballot[c2], h, 0) in s.pmsgs[a]))| <= F;
        //assert forall a :: a in acceptors && a in s.promise_count[c2] ==> (exists h :: PMsg(s.leader_ballot[c2], h, 0) in s.pmsgs[a]);
        //assert s.promise_count[c2] <= acceptors;
        //assert s.promise_count[c2] <= (set a | a in acceptors && (exists h :: PMsg(s.leader_ballot[c2], h, 0) in s.pmsgs[a]));
        SubsetSize(s.promise_count[c2], (set a | a in acceptors && (exists h :: PMsg(s.leader_ballot[c2], h, 0) in s.pmsgs[a])));
    }
    // the base case of lemma Min_leader_decision
    lemma Same_ballot_leaders(s: TSState, c1: Acceptor, c2: Acceptor)
    requires type_ok(s) && valid(s) && valid_leader_ballot(s)
    requires c1 in leaders && c2 in leaders
    requires s.leader_ballot[c1] == s.leader_ballot[c2] >= 0
    ensures c1 == c2
    {}
    // selecting a leader with the same proposal but a smaller ballot number in the induction step of lemma Min_leader_decision
    lemma Select_leader_smaller_ballot(s: TSState, c1: Acceptor) returns (c2: Acceptor)
    requires type_ok(s) && valid(s) && c1 in leaders
    requires s.leader_propose[c1] > 0 && |s.promise_count[c1]| <= F
    ensures c2 in leaders && s.leader_ballot[c2] < s.leader_ballot[c1] && s.leader_propose[c2] == s.leader_propose[c1]
    {
        c2 :| c2 in leaders && s.leader_ballot[c2] < s.leader_ballot[c1] && s.leader_propose[c2] == s.leader_propose[c1];
    }

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

    /** the list of lemmas for all the reachable states and all the transitions, since it's easier to debug in this way.
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

    lemma consistency(s: TSState, c1: Acceptor, c2: Acceptor)
    requires type_ok(s) && valid(s)
    requires c1 in leaders && c2 in leaders && (s.leader_decision[c1] > 0) && (s.leader_decision[c2] > 0)
    //ensures s.leader_decision[c1] == s.leader_decision[c2]

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