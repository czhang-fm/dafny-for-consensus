include "paxos-classic.dfy"
include "auxiliary.dfy"
include "paxos-invariants.dfy"
include "promise-invariants.dfy"

module SupportingLemmas {

    import opened Paxos_protocol
    import opened Auxiliary_lemmas
    import opened Invariants
    import opened PromiseInvariants

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
    // lemma -1: if there are majority promise to a leader, then no other leader with a smaller ballot number can be "confirmed" by majority
    // this will be used in the nonforce case in the induction step proof of lemma X.
    lemma Fresh_proposal_unique(s: TSState, c1: Acceptor, c2: Acceptor)
    requires type_ok(s) && valid(s) 
    requires c1 in leaders && c2 in leaders && s.leader_propose[c2] > 0
    requires |set a | a in acceptors && PMsg(s.leader_ballot[c2], -1, 0) in s.pmsgs[a]| >= F + 1
    requires s.leader_ballot[c1] < s.leader_ballot[c2]
    ensures |set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| < F + 1
    {
        if |set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| >= F + 1 {
            Quorum();
            var a := GetAcceptor((set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]), set a | a in acceptors && PMsg(s.leader_ballot[c2], -1, 0) in s.pmsgs[a]);
            // assert false;
        }
    } 
    // lemma 1: if an acceptor is in the promised set and leader is nonforced, then there is a non-force promise from the acceptor to the leader
    lemma Nonforced_promise(s: TSState, c: Acceptor, a: Acceptor)
    requires type_ok(s) && valid(s)
    requires c in leaders && s.leader_forced[c] == 0 && a in s.promise_count[c]
    ensures exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a] && h == -1 && v == 0 //PMsg(s.leader_ballot[c], -1, 0) in s.pmsgs[a]
    {} // this is not good enough
    // lemma 1.5
    lemma Existence_promise(s: TSState, c: Acceptor, a: Acceptor)
    requires type_ok(s) && valid(s)
    requires c in leaders && s.leader_forced[c] == 0 && a in s.promise_count[c]
    ensures PMsg(s.leader_ballot[c], -1, 0) in s.pmsgs[a]
    {}
    // lemma 2: if a leader proposes a value, then it has collected at least F+1 promises (a sanity check)
    lemma Leader_propose(s: TSState, c: Acceptor)
    requires type_ok(s) && valid(s)
    requires c in leaders && s.leader_propose[c] > 0
    ensures |s.promise_count[c]| >= F + 1
    {}
    // lemma 3: if a leader proposes a fresh value, then it has collected at least F+1 PMsg(bn, -1, 0) promises
    lemma Leader_fresh_propose(s: TSState, c: Acceptor)
    requires type_ok(s) && valid(s)
    requires c in leaders && s.leader_propose[c] > 0 && s.leader_forced[c] == 0
    ensures |set a | a in acceptors && PMsg(s.leader_ballot[c], -1, 0) in s.pmsgs[a]| >= F + 1
    {
        assert |s.promise_count[c]| >= F + 1;
        // assert forall a :: a in s.promise_count[c] ==> (exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a] && h == -1 && v == 0);
        // assert s.promise_count[c] <= (set a | a in acceptors && (exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a] && h == -1 && v == 0));
        // SubsetSize(s.promise_count[c], set a | a in acceptors && (exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a] && h == -1 && v == 0));
        assert forall a :: a in s.promise_count[c] ==> PMsg(s.leader_ballot[c], -1, 0) in s.pmsgs[a];
        SubsetSize(s.promise_count[c], set a | a in acceptors && PMsg(s.leader_ballot[c], -1, 0) in s.pmsgs[a]);
    }
    // lemma 4: the nonforce case of lemma X: Given c1 & c2 both proposed with bn1 < bn2, if v1 is confirmed by majority acceptors, then v2 cannot be (freely) proposed in the "non-force" case.
    lemma NonforceX(s: TSState, c1: Acceptor, c2: Acceptor)
    requires type_ok(s) && valid(s)
    requires c1 in leaders && c2 in leaders && s.leader_propose[c1] > 0 && s.leader_propose[c2] > 0
    requires s.leader_ballot[c1] < s.leader_ballot[c2]
    requires |set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| >= F + 1
    ensures s.leader_forced[c2] > 0
    {
        assert s.leader_forced[c2] >= 0;
        if s.leader_forced[c2] == 0 {
            Leader_fresh_propose(s, c2);
            Fresh_proposal_unique(s, c1, c2);
            assert |set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| <= F;
            assert false;
        }
    }
    // lemma 5: same chosen ballot ==> same leader
    lemma EqualBallot(s: TSState, c1: Acceptor, c2: Acceptor)
    requires type_ok(s) && valid(s)
    requires c1 in leaders && c2 in leaders
    requires s.leader_ballot[c1] >= 0 && s.leader_ballot[c2] == s.leader_ballot[c1]
    ensures c1 == c2
    {}
    // lemma 6: if an acceptor confirmed CMsg(bn1, v1) and later promised PMsg(bn2, bn, v2), then bn1 <= bn




    // lemma 6': if a leader proposes a value in the forced case, then that value must be from another leader with a smaller ballot (ok, but)
    lemma leader_proposal_forced(s: TSState, c: Acceptor) returns (c': Acceptor)
    requires type_ok(s) && valid(s) && valid_promise(s)
    requires c in leaders && s.leader_propose[c] > 0
    requires s.leader_forced_ballot[c] >= 0
    ensures (exists c' :: c' in leaders && s.leader_ballot[c'] < s.leader_ballot[c] && s.leader_ballot[c']==s.leader_forced_ballot[c] && s.leader_propose[c] == s.leader_propose[c'])
    {
        assert s.leader_propose[c] == s.leader_forced[c];
        assert exists bn, v, a :: a in acceptors && PMsg(s.leader_ballot[c], bn, v) in s.pmsgs[a] && a in s.promise_count[c] && v == s.leader_forced[c]; 
        c' :| c' in leaders && s.leader_ballot[c'] < s.leader_ballot[c] && s.leader_ballot[c']==s.leader_forced_ballot[c] && s.leader_propose[c'] == s.leader_propose[c];
    }

    // lemma 7: the force case of lemma X && the leader c2 must have a ballot at least as large as c1
    // lemma NonforceLarger(s: TSState, c1: Acceptor, c2: Acceptor)
    // requires type_ok(s) && valid(s)
    // requires c1 in leaders && c2 in leaders && s.leader_propose[c1] > 0 && s.leader_propose[c2] > 0
    // requires |set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| >= F + 1
    // requires forall c :: c in leaders && s.leader_ballot[c] < s.leader_ballot[c1] ==> (|set a | a in acceptors && CMsg(s.leader_ballot[c], s.leader_propose[c]) in s.cmsgs[a]| <= F)
    // ensures s.leader_ballot[c1] <= s.leader_ballot[c2]
    // {
    //     assert |s.promise_count[c2]| >= F + 1;
    //     assert s.promise_count[c2] <= (set a | a in acceptors && CMsg(s.leader_ballot[c2], s.leader_propose[c2]) in s.cmsgs[a]);
    // }
    // {
    //     if s.leader_ballot[c2] < s.leader_ballot[c1]{
    //         assert |s.promise_count[c2]| >= F + 1;
    //         assert (set a | a in acceptors && CMsg(s.leader_ballot[c2], s.leader_propose[c2]) in s.cmsgs[a]) <= s.promise_count[c2];
    //         SubsetSize((set a | a in acceptors && CMsg(s.leader_ballot[c2], s.leader_propose[c2]) in s.cmsgs[a]), s.promise_count[c2]);
    //         assert false;
    //     }
    // }

}