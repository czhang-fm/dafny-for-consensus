include "paxos-classic.dfy"
include "auxiliary.dfy"
include "paxos-invariants.dfy"
include "paxos-leader-ballot-invariants.dfy"

module Consistency {

    import opened Paxos_protocol
    import opened Auxiliary_lemmas
    import opened Invariants
    import opened Leader_ballot_invariants

    lemma{:axiom} Quorum()
    ensures |acceptors| == 2 * F + 1

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

    // lemma 1: if an acceptor is in the promised set and leader is nonforced, then there is such a promise
    lemma Nonforced_promise(s: TSState, c: Acceptor, a: Acceptor, highest: int, v: Proposal)
    requires type_ok(s) && valid(s)
    requires c in leaders && s.leader_forced[c] == 0 && a in s.promise_count[c]
    ensures exists highest, v :: PMsg(s.leader_ballot[c], highest, v) in s.pmsgs[a] && highest == -1 && v == 0
    {}
    // an auxiliary lemma for lemma 2
    lemma Nonforced_promise_2(s: TSState, c: Acceptor)
    requires type_ok(s) && valid(s)
    requires c in leaders && s.leader_forced[c] == 0 && s.leader_propose[c] > 0
    ensures s.promise_count[c] <= (set a | a in acceptors && PMsg(s.leader_ballot[c], -1, 0) in s.pmsgs[a])
    {
        if s.promise_count[c] == {}
        {}
        else {
            var a :| a in s.promise_count[c];
            assert a in (set a | a in acceptors && exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a]);
            var h, v :| PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a];
            Nonforced_promise(s, c, a, h, v);
            assert PMsg(s.leader_ballot[c], -1, 0) in s.pmsgs[a];
        }

    }
    // lemma 2: invariant Y as lemma 2
    lemma Majority_promise(s: TSState, c: Acceptor)
    requires type_ok(s) && valid(s)
    requires c in leaders && s.leader_forced[c] == 0 && s.leader_propose[c] > 0
    ensures |set a | a in acceptors && PMsg(s.leader_ballot[c], -1, 0) in s.pmsgs[a]| >= F + 1
    {
        assert |s.promise_count[c]| >= F + 1;
        Nonforced_promise_2(s, c);
        SubsetSize(s.promise_count[c], (set a | a in acceptors && PMsg(s.leader_ballot[c], -1, 0) in s.pmsgs[a]));
    }

    // lemma 3: tracing the proposed value to the original proposer
    lemma Fresh_proposal(s: TSState, c1: Acceptor) returns (c2: Acceptor)
    requires type_ok(s) && valid(s) && valid_leader_ballot(s)
    requires c1 in leaders && s.leader_propose[c1] > 0
    ensures c2 in leaders && s.leader_propose[c1] == s.leader_propose[c2] 
    ensures s.leader_ballot[c1] >= s.leader_ballot[c2]
    ensures |set a | a in acceptors && PMsg(s.leader_ballot[c2], -1, 0) in s.pmsgs[a]| >= F + 1
    decreases s.leader_ballot[c1]
    {
        // use variant X to expand to two cases:
        if s.leader_forced[c1] == 0 {
            Majority_promise(s, c1);
            c2 := c1;
        } else {
            assert s.leader_forced[c1] > 0 && s.leader_propose[c1] == s.leader_forced[c1];
            assert (exists a, highest, value :: a in acceptors && PMsg(s.leader_ballot[c1], highest, value) in s.pmsgs[a] && highest == s.leader_forced_ballot[c1] && value == s.leader_propose[c1]);
            // assert exists c3 :: c3 in leaders && s.leader_ballot[c3] < s.leader_ballot[c1] && s.leader_propose[c3] == s.leader_propose[c1];  
            var c3 :| c3 in leaders && s.leader_ballot[c3] < s.leader_ballot[c1] && s.leader_propose[c3] == s.leader_propose[c1];
            c2 := Fresh_proposal(s, c3);
        }
    }
    // lemma 4: if a leader proposes an original value, then it must be the first proposal
    lemma Fresh_proposal_unique(s: TSState, c1: Acceptor, c2: Acceptor)
    requires type_ok(s) && valid(s) 
    requires c1 in leaders && c2 in leaders && s.leader_propose[c1] > 0
    requires |set a | a in acceptors && PMsg(s.leader_ballot[c1], -1, 0) in s.pmsgs[a]| >= F + 1
    requires s.leader_ballot[c2] < s.leader_ballot[c1]
    ensures |set a | a in acceptors && CMsg(s.leader_ballot[c2], s.leader_propose[c2]) in s.cmsgs[a]| < F + 1
    {
        if |set a | a in acceptors && CMsg(s.leader_ballot[c2], s.leader_propose[c2]) in s.cmsgs[a]| >= F + 1 {
            Quorum();
            var a := GetAcceptor((set a | a in acceptors && CMsg(s.leader_ballot[c2], s.leader_propose[c2]) in s.cmsgs[a]), set a | a in acceptors && PMsg(s.leader_ballot[c1], -1, 0) in s.pmsgs[a]);
            // assert false;
        }
    } 
    // auxiliary lemma for lemma 5: may not be useful ???
    lemma Majority_promise_2(s: TSState, c: Acceptor)
    requires type_ok(s) && valid(s)
    requires c in leaders && s.leader_forced[c] > 0 && s.leader_propose[c] > 0
    ensures |set a | a in acceptors && (exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a])| >= F + 1
    // ensures forall a, h, v :: a in acceptors && PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a] ==> h <= s.leader_forced_ballot[c] && v == s.leader_propose[c]
    // ensures exists a, h, v :: a in acceptors && PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a] ==> h == s.leader_forced_ballot[c] && v == s.leader_propose[c]
    {
        assert |s.promise_count[c]| >= F + 1;
        SubsetSize(s.promise_count[c], (set a | a in acceptors && exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a]));
        //
    }

    // lemma 5: if a value is "chosen" for a leader, than all follow up leaders may only propose that value
    // This can be proved by induction for all c2 with a ballot number larger than or equal to c1 and s.leader_propose[c2] > 2
    lemma X(s: TSState, c1: Acceptor, c2: Acceptor)
    requires type_ok(s) && valid(s) && valid_leader_ballot(s)
    requires c1 in leaders && c2 in leaders && s.leader_propose[c2] > 0
    requires s.leader_ballot[c1] <= s.leader_ballot[c2]
    requires |set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| >= F + 1 // v1 from c1 is chosen
    // ensures s.leader_propose[c1] == s.leader_propose[c2]
    // {
    //     if s.leader_ballot[c1] == s.leader_ballot[c2]{
    //         // base case: trivial
    //         assert s.leader_propose[c1] == s.leader_propose[c2];
    //     } else {
    //         assert s.leader_ballot[c1] <= s.leader_ballot[c2] - 1;
    //         // induction step:
    //         if s.leader_forced[c2] == 0 {
    //             // the nonforce case: impossible
    //             Majority_promise(s, c2);
    //             assert |set a | a in acceptors && PMsg(s.leader_ballot[c2], -1, 0) in s.pmsgs[a]| >= F + 1;
    //             Fresh_proposal_unique(s, c2, c1);
    //             assert |set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| < F + 1;
    //             assert false;
    //         } else { //the force case:
    //             assert s.leader_forced[c2] > 0 && s.leader_propose[c2] == s.leader_forced[c2];
    //             assert |s.promise_count[c2]| >= F + 1;
    //             // now we need to show at least an acceptor in s.promise_cout[c2] that has confirmed s.leader_ballot[c1]
    //             var a := GetAcceptor((set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]), s.promise_count[c2]);
    //             // Majority_promise_2(s, c2);
    //             // assert |set a | a in acceptors && (exists h, v :: PMsg(s.leader_ballot[c2], h, v) in s.pmsgs[a])| >= F + 1;
    //             // now we need to show at least an acceptor in PMsg(c2, h, v) has confirmed s.leader_ballot[c1]
    //             // var a := GetAcceptor((set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]), (set a | a in acceptors && (exists h, v :: PMsg(s.leader_ballot[c2], h, v) in s.pmsgs[a])));
    //             assert exists h, v :: PMsg(s.leader_ballot[c2], h, v) in s.pmsgs[a] && h >= s.leader_ballot[c1];
    //             //
    //         }
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
    (2) At least F + 1 acceptors have sent out a confirm reply in Step 2b in response to the proposer with ballot number bn for v. 
    
    Therefore, for all other ballots bn' < bn, those acceptors will not reply to the request with bn'; and for all new ballot bn'' >= bn, 
    those acceptors will reply with (bn'', highest, v) in step-1b since they have previously confirmed value v. 
    (Note they cannot all go faulty which is against our assumption) Since the leader with bn'' is honest, 
    it will be forced in Step 2a to propose v (with bn'') if it receives at least one step-1b message with a confirmed v; 
    It will not propose a different value unless it has not received any step-1b message with a confirmed v. 
    (Intuitively, that value "v" should have already been confirmed by the system but it may still be waiting 
    for a proposer to "announce" it. In such a scenario, we say "v" has been "decided" by the system,
    which needs to be represented by the invariants in our consistency proof.)

    In general, we cannot distinguish the case when a user is faulty and the case that a message from or to that user is taking too long. 
    */
}