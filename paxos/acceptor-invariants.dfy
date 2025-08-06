include "paxos-classic.dfy"
include "auxiliary.dfy"
include "paxos-invariants.dfy"

module AcceptorInvariants {

    import opened Paxos_protocol
    import opened Auxiliary_lemmas
    import opened Invariants

    ghost predicate valid_acceptor(s: TSState) /// move the PMsg related invariants to here
    requires type_ok(s) && valid(s)
    {
        && (forall a, bn, v :: a in acceptors && CMsg(bn, v) in s.cmsgs[a] ==> s.acceptor_state[a].highest >= bn && s.acceptor_state[a].confirmed >= bn)
        && (forall a, bn1, bn2, bn, v1, v2 :: a in acceptors && CMsg(bn1, v1) in s.cmsgs[a] && PMsg(bn2, bn, v2) in s.pmsgs[a] && bn1 < bn2==>
            bn1 <= bn && bn < bn2)
        // we need to find an active leader for each allocated ballot
        && (forall c :: c in leaders ==> s.leader_ballot[c] < s.ballot)
        // && (forall bn :: 0 <= bn <= s.ballot - 1 ==> (exists c :: c in leaders && s.leader_ballot[c] == bn))
        && (|s.ballot_mapping| == s.ballot)
        && (forall bn :: 0 <= bn < s.ballot ==> s.ballot_mapping[bn] in leaders && s.leader_ballot[s.ballot_mapping[bn]] == bn)
        // we need to relate PMsg(bn1, bn, v) with v>0 to the actual leader who proposed b
        && (forall a :: a in acceptors && s.acceptor_state[a].value > 0 ==> 
            (exists c :: c in leaders && s.leader_propose[c] == s.acceptor_state[a].value && s.leader_ballot[c] == s.acceptor_state[a].confirmed))
        && (forall bn1, bn, v, a :: a in acceptors && PMsg(bn1, bn, v) in s.pmsgs[a] && v>0 ==> 
            (bn < bn1 && exists c :: c in leaders && s.leader_ballot[c] == bn && s.leader_propose[c] == v)) // invariant 1 for lemma 7.5 
        // && (forall bn, v, a, c :: a in acceptors && c in leaders && PMsg(s.leader_ballot[c], bn, v) in s.pmsgs[a] && a in s.promise_count[c] && v>0 && bn >= 0==>
        //     bn < s.leader_ballot[c] && bn <= s.leader_forced_ballot[c]) // invariant 2 for lemma 7.5 (bn <= s.leader_forced_ballot[c])
        // && (forall a, c :: a in acceptors && c in leaders && s.leader_forced[c] > 0 && a in s.promise_count[c] ==>
        //    (forall bn, v :: PMsg(s.leader_ballot[c], bn, v) in s.pmsgs[a] ==> bn <= s.leader_forced_ballot[c])) // another presentation, or can we prove it as a lemma
        // Dafny cannot figure out the following set is finite : 
        // && (forall c, bn :: c in leaders && bn in (set bn | exists a, bn, v :: a in acceptors && a in s.promise_count[c] && PMsg(s.leader_ballot[c], bn, v) in s.pmsgs[a]) ==> bn <= s.leader_forced_ballot[c])
    }

    /** the list of lemmas to be checked for invariants in all the reachable states 
    for all the transitions, since it's easier to debug in this way.
     */
    lemma Inv_init(s: TSState)
    requires type_ok(s) && init(s)
    ensures valid_acceptor(s)
    {}

    lemma Inv_choose_ballot(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && choose_ballot(s, s', c) && valid_acceptor(s)
    ensures valid_acceptor(s')
    {
        assert forall a :: a in acceptors ==> s.pmsgs[a] == s'.pmsgs[a];
    }

    lemma Inv_receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor) 
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_higher_ballot(s, s', c, a) && valid_acceptor(s)
    ensures valid_acceptor(s')
    {
        assert forall bn1, v1:: CMsg(bn1, v1) in s.cmsgs[a] ==> s.acceptor_state[a].value > 0;
        assert s.acceptor_state[a].value > 0 ==> PMsg(s.leader_ballot[c], s.acceptor_state[a].confirmed, s.acceptor_state[a].value) in s'.pmsgs[a];
        assert forall bn1, v1:: CMsg(bn1, v1) in s.cmsgs[a] && PMsg(s.leader_ballot[c], s.acceptor_state[a].confirmed, s.acceptor_state[a].value) in s'.pmsgs[a] ==> bn1 <= s.acceptor_state[a].confirmed;
    }

    lemma Inv_receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, confirmed: int, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors //&& confirmed >= 0 && value > 0 
    requires receive_response_1b(s, s', c, a, confirmed, value) && valid_acceptor(s)
    ensures valid_acceptor(s')
    {
        assert confirmed <= s.leader_forced_ballot[c] ==> s.leader_forced_ballot == s'.leader_forced_ballot;
        assert confirmed > s.leader_forced_ballot[c] ==> s'.leader_forced_ballot[c] == confirmed;
        assert confirmed <= s'.leader_forced_ballot[c];
        assert PMsg(s'.leader_ballot[c], confirmed, value) in s'.pmsgs[a];
        assert a in s'.promise_count[c];
        // assert forall bn, v, a, c :: a in acceptors && c in leaders && PMsg(s.leader_ballot[c], bn, v) in s.pmsgs[a] && a in s.promise_count[c] && v>0 && bn >= 0==>
        //     bn < s.leader_ballot[c] && bn <= s.leader_forced_ballot[c]; 
        // assert a in s'.promise_count[c] && confirmed >= 0 && value > 0;
        // assert forall bn, v, a, c :: a in acceptors && c in leaders && PMsg(s'.leader_ballot[c], bn, v) in s'.pmsgs[a] && a in s'.promise_count[c] && v>0 && bn >= 0==>
        //     bn < s'.leader_ballot[c] && bn <= s'.leader_forced_ballot[c];
    }

    lemma Inv_propose_value_2a(s: TSState, s': TSState, c: Acceptor, value: Proposal)
    requires  type_ok(s) && type_ok(s') && valid(s) && c in leaders && value > 0 && propose_value_2a(s, s', c, value) && valid_acceptor(s)
    ensures valid_acceptor(s')
    {}

    lemma Inv_confirm_ballot_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value > 0
    requires confirm_ballot_2b(s, s', c, a, value) && valid_acceptor(s)
    ensures valid_acceptor(s')
    {
        // assert s'.acceptor_state[a].value == s'.leader_propose[c];
        // assert s'.acceptor_state[a].confirmed == s'.leader_ballot[c];
    }

    lemma Inv_receive_confirm_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, bn: int, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value > 0
    requires receive_confirm_2b(s, s', c, a, value) && valid_acceptor(s)
    ensures valid_acceptor(s')
    {}

    lemma Inv_leader_decide(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders 
    requires leader_decide(s, s', c) && valid_acceptor(s)
    ensures valid_acceptor(s')
    {}

}