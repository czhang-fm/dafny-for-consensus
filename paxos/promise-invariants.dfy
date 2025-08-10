include "paxos-classic.dfy"
include "auxiliary.dfy"
include "paxos-invariants.dfy"

module PromiseInvariants {

    import opened Paxos_protocol
    import opened Auxiliary_lemmas
    import opened Invariants

    ghost predicate valid_promise(s: TSState) /// move the PMsg related invariants to here
    requires type_ok(s) && valid(s) 
    {
        // if a leader c is forced to a value, then there exists PMsg(bn, ballot, v) in s.pmsgs[a] with a in s.promise_count 
        // and (h,v) as forced ballot and forced value
        && (forall bn, ballot, v, a :: a in acceptors && PMsg(bn, ballot, v) in s.pmsgs[a] ==> ballot < bn)
        && (forall a :: a in acceptors && s.acceptor_state[a].value > 0 ==> 
        (exists c :: c in leaders && s.acceptor_state[a].confirmed_ballot == s.leader_ballot[c] && s.acceptor_state[a].value == s.leader_propose[c]))
        && (forall bn, ballot, v, a :: a in acceptors && PMsg(bn, ballot, v) in s.pmsgs[a] && v>0 ==> 
        (exists c :: c in leaders && ballot == s.leader_ballot[c] && v == s.leader_propose[c]))
        && (forall c :: c in leaders && s.leader_forced[c] > 0 ==> // invariant V
        (exists a, ballot, v :: a in s.promise_count[c] && PMsg(s.leader_ballot[c], ballot, v) in s.pmsgs[a] && ballot == s.leader_forced_ballot[c] && v == s.leader_forced[c]))
        // && (forall a, c :: a in acceptors && c in leaders && s.leader_forced[c] > 0 && a in s.promise_count[c] ==>
        //     (forall bn, v :: PMsg(s.leader_ballot[c], bn, v) in s.pmsgs[a] ==> bn <= s.leader_forced_ballot[c])) // another presentation, or can we prove it as a lemma?
        // && (forall c :: c in leaders && s.leader_forced_ballot[c] >= 0 ==>
        // (forall a, ballot, v :: a in s.promise_count[c] && PMsg(s.leader_ballot[c], ballot, v) in s.pmsgs[a] ==> ballot <= s.leader_forced_ballot[c])) // another failed trial

        // This is possible that there may be some PMsg(bn1, _, _) not yet received by c1 ???
        // && (forall c, ballot, v:: c in leaders && s.leader_forced_ballot[c] >= 0 && PMsg(s.leader_ballot[c], ballot, v) in s.received_promises[c] ==> ballot <= s.leader_forced_ballot[c])
        && (forall c, m :: c in leaders && m in s.received_promises[c] ==> s.leader_forced_ballot[c] >= m.confirmed_ballot) // this time it's successful ???
        && (forall a :: a in acceptors ==> |s.pmsgs[a]| <= s.acceptor_state[a].highest_ballot + 1) // this proves that the set of PMsg is bounded for all acceptors
        && (forall c :: c in leaders && s.leader_forced[c] > 0 ==> // this is the same as invariant in the above
            (exists m :: m in s.received_promises[c] && m.confirmed_ballot == s.leader_forced_ballot[c] && m.value == s.leader_forced[c]))
    }

    /** the list of lemmas to be checked for invariants in all the reachable states 
    for all the transitions, since it's easier to debug in this way.
     */
    lemma Inv_init(s: TSState)
    requires type_ok(s) && init(s)
    ensures valid_promise(s)
    {}

    lemma Inv_choose_ballot(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && choose_ballot(s, s', c) && valid_promise(s)
    ensures valid_promise(s')
    {
        assert s.leader_ballot[c] == -1 && s'.leader_ballot[c] == s.ballot;
        assert forall c :: c in leaders ==> s.leader_ballot[c] < s.ballot == s'.ballot - 1;
        // assert forall c' :: c' in leaders && c' != c ==> s'.leader_ballot[c'] < s'.leader_ballot[c] == s.ballot == s'.ballot - 1;
    }

    lemma Inv_receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor) 
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_higher_ballot(s, s', c, a) && valid_promise(s)
    ensures valid_promise(s')
    {
        assert forall c :: c in leaders ==> (set a | a in acceptors && exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a]) <= (set a | a in acceptors && exists h, v :: PMsg(s'.leader_ballot[c], h, v) in s'.pmsgs[a]);
    }

    lemma Inv_receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, m: PMsg)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors 
    requires receive_response_1b(s, s', c, a, m) && valid_promise(s)
    ensures valid_promise(s')
    {
        assert m.confirmed_ballot <= s.leader_forced_ballot[c] ==> s.leader_forced_ballot == s'.leader_forced_ballot;
        assert m.confirmed_ballot > s.leader_forced_ballot[c] ==> s'.leader_forced_ballot[c] == m.confirmed_ballot;
        assert m.confirmed_ballot <= s'.leader_forced_ballot[c];
        assert m in s'.received_promises[c];
        // assert PMsg(s'.leader_ballot[c], confirmed, value) in s'.pmsgs[a];
        // assert a in s'.promise_count[c];
        // assert  (forall a, c :: a in acceptors && c in leaders && s.leader_forced[c] > 0 && a in s.promise_count[c] ==>
        //    (forall bn, v :: PMsg(s.leader_ballot[c], bn, v) in s.pmsgs[a] ==> bn <= s.leader_forced_ballot[c]));
        assert forall c :: c in leaders ==> (s.leader_forced_ballot[c] <= s'.leader_forced_ballot[c]); // leader_forced_ballot[c] can only increase ....
        // assert  (forall a, c :: a in acceptors && c in leaders && s'.leader_forced_ballot[c] >= 0 && a in s'.promise_count[c] ==>
        //    (forall bn, v :: PMsg(s.leader_ballot[c], bn, v) in s'.pmsgs[a] && bn != confirmed ==> bn <= s'.leader_forced_ballot[c]));
        // assert forall a :: a in acceptors ==> s.pmsgs[a] == s'.pmsgs[a];
        // assert s'.promise_count == s.promise_count[c:= s.promise_count[c]+{a}];
        assert s'.received_promises == s.received_promises[c:= s.received_promises[c]+{m}];
        
        // the following assertion cannot be proved by Dafny as Dafny struggled to find a trigger?
        assert (forall m :: m in s.received_promises[c] ==> m.confirmed_ballot <= s.leader_forced_ballot[c]) ==>
            (forall m :: m in s'.received_promises[c] ==> m.confirmed_ballot <= s'.leader_forced_ballot[c]); 
    }

    lemma Inv_propose_value_2a(s: TSState, s': TSState, c: Acceptor, value: Proposal)
    requires  type_ok(s) && type_ok(s') && valid(s) && c in leaders && value > 0 && propose_value_2a(s, s', c, value) && valid_promise(s)
    ensures valid_promise(s')
    {
        assert s'.leader_forced[c] > 0 ==> s'.leader_propose[c] == s'.leader_forced[c];
    }

    lemma Inv_confirm_ballot_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value > 0
    requires confirm_ballot_2b(s, s', c, a, value) && valid_promise(s)
    ensures valid_promise(s')
    {}

    lemma Inv_receive_confirm_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, m: CMsg)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors 
    requires receive_confirm_2b(s, s', c, a, m) && valid_promise(s)
    ensures valid_promise(s')
    {}

    lemma Inv_leader_decide(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders 
    requires leader_decide(s, s', c) && valid_promise(s)
    ensures valid_promise(s')
    {}

}