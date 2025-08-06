include "paxos-classic.dfy"
include "auxiliary.dfy"
include "paxos-invariants.dfy"
include "promise-invariants.dfy"
include "acceptor-invariants.dfy"
include "supporting-lemmas.dfy"

module ForcedInvariants {

    import opened Paxos_protocol
    import opened Auxiliary_lemmas
    import opened Invariants
    import opened PromiseInvariants
    import opened AcceptorInvariants
    import opened SupportingLemmas

    ghost predicate valid_forced(s: TSState) /// move the PMsg related invariants to here
    requires type_ok(s) && valid(s) 
    {
        // if a leader c is forced to a value:
        // (1) the other (promise) invariant has shown that there exists PMsg(bn, ballot, v) in s.pmsgs[a] with a in s.promise_count 
        // and (h,v) as forced ballot and forced value
        // (2) here we need to further show the (forced) invariant: s.leader_forced_ballot[c] represents the largest such ballot 
        // wrapped in PMsg(leader_ballot[c], _, _) messages, and v is proposed by the leader of that ballot, i.e.,
        // && (forall a, c :: a in acceptors && c in leaders && s.leader_forced[c] > 0 && a in s.promise_count[c] ==>
        //    (forall bn, v :: PMsg(s.leader_ballot[c], bn, v) in s.pmsgs[a] ==> bn <= s.leader_forced_ballot[c])) 
        true
    }
    // lemma 7.1 (*): the force case of lemma X && the leader c2 must have received a promise from another leader with a ballot at least as large as c1
    lemma NewForceCaseLarger(s: TSState, c1: Acceptor, c2: Acceptor) returns (c3 : Acceptor)
    requires type_ok(s) && valid(s) && valid_acceptor(s)
    requires c1 in leaders && c2 in leaders && s.leader_propose[c1] > 0 && s.leader_propose[c2] > 0
    requires s.leader_forced[c2] > 0 && s.leader_ballot[c1] < s.leader_ballot[c2]
    requires |set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| >= F + 1
    ensures c3 in leaders && s.leader_ballot[c1] <= s.leader_ballot[c3] 
    ensures exists a, v :: a in acceptors && PMsg(s.leader_ballot[c2], s.leader_ballot[c3], v) in s.pmsgs[a] && a in s.promise_count[c2] 
    // ensures exists m :: m in s.received_promises[c2] && m.highest == s.leader_ballot[c3] // the new postcondition about existence of m in s.received_promise[c2] with m.highest == s.leader_ballot[c3]
    {
        assert |s.promise_count[c2]| >= F+1;
        var a := GetAcceptor((set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]), s.promise_count[c2]);
        var v1 :| CMsg(s.leader_ballot[c1], v1) in s.cmsgs[a];
        var bn, v2 :| PMsg(s.leader_ballot[c2], bn, v2) in s.pmsgs[a];
        AcceptorConfirmPromise(s, a, c1, c2, bn, v1, v2); assert s.leader_ballot[c1] <= bn;
        assert bn < s.ballot;
        c3 := s.ballot_mapping[bn];
    }
    // lemma 7.2: the existence of a leader c2 which passed its ballot to leader_forced_ballot[c1] and its proposal to leader_forced[c1]
    lemma ForceCaseProposer(s: TSState, c1: Acceptor) returns (c2: Acceptor)
    requires type_ok(s) && valid(s) && valid_promise(s) && valid_acceptor(s)
    requires c1 in leaders && s.leader_forced[c1] > 0 
    ensures c2 in leaders
    ensures (exists a :: a in acceptors && PMsg(s.leader_ballot[c1], s.leader_ballot[c2], s.leader_propose[c2]) in s.pmsgs[a] && s.leader_forced_ballot[c1] == s.leader_ballot[c2] && s.leader_forced[c1] == s.leader_propose[c2])
    {
        var counted_acceptors := (set a | a in acceptors && a in s.promise_count[c1]);
        var ballot :| exists a, v :: a in acceptors && a in counted_acceptors && PMsg(s.leader_ballot[c1], ballot, v) in s.pmsgs[a] && ballot == s.leader_forced_ballot[c1];
        c2 := s.ballot_mapping[ballot];
    }
    // lemma 7.3: we need to show all received PMsg(bn1, bn, v) has bn <= leader_forced_ballot[c1]
    lemma ForcedBallotTest(s: TSState, c: Acceptor)
    requires type_ok(s) && valid(s) && valid_acceptor(s) && valid_promise(s)
    requires c in leaders && s.leader_forced_ballot[c] >= 0
    ensures forall m :: m in s.received_promises[c] ==> m.highest <= s.leader_forced_ballot[c]
    {}
    // lemma 7.4: to compare the leader_ballot's generated from lemma 7 and lemma 7.2 
    // this is a failed test as it takes too much time in the assertion, which means more conditions are required.
    // If this succeeds then we will already have lemma 7.5
    lemma ForceCaseTest(s: TSState, c1: Acceptor, c2: Acceptor) //returns (c3 : Acceptor)
    requires type_ok(s) && valid(s) && valid_acceptor(s) && valid_promise(s)
    requires c1 in leaders && c2 in leaders && s.leader_propose[c1] > 0 && s.leader_propose[c2] > 0
    requires s.leader_forced[c2] > 0 && s.leader_ballot[c1] < s.leader_ballot[c2]
    requires |set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| >= F + 1
    {
        // get the c3 with bn1 <= bn3 && bn3 < bn2
        var c3 := ForceCaseLarger(s, c1, c2);
        var c4 := ForceCaseProposer(s, c2);
        assert s.leader_ballot[c4] == s.leader_forced_ballot[c2];
        // ForcedBallotTest(s, c2);
        assert exists a, v :: a in acceptors && PMsg(s.leader_ballot[c2], s.leader_ballot[c3], v) in s.pmsgs[a] && a in s.promise_count[c2];
        var m :| exists a, v :: a in acceptors && PMsg(s.leader_ballot[c2], s.leader_ballot[c3], v) in s.pmsgs[a] && a in s.promise_count[c2] && m == PMsg(s.leader_ballot[c2], s.leader_ballot[c3], v);
        assert m.highest == s.leader_ballot[c3];
        // assert m in s.received_promises[c2];
        // assert exists m :: m in s.received_promises[c2] && m.highest == s.leader_ballot[c3];
        // assert s.leader_ballot[c3] <= s.leader_ballot[c4];
    }


    // lemma 7.5: a more general case of lemma 8
    // lemma ForceCaseLargest(s: TSState, c1: Acceptor) returns (c2 : Acceptor) // half of the currently stalled lemma ....
    // requires type_ok(s) && valid(s) && valid_acceptor(s) && valid_promise(s)
    // requires c1 in leaders && s.leader_propose[c1] > 0 && s.leader_forced[c1] > 0
    // ensures c2 in leaders && s.leader_ballot[c2] < s.leader_ballot[c1]
    // ensures forall a, bn, v:: a in acceptors && PMsg(s.leader_ballot[c1], bn, v) in s.pmsgs[a] && a in s.promise_count[c1] ==> bn <= s.leader_ballot[c2]
    // ensures c2 in leaders && s.leader_forced[c1] == s.leader_propose[c2]
    // {}

    /** the list of lemmas to be checked for invariants in all the reachable states 
    for all the transitions, since it's easier to debug in this way.
     */
    lemma Inv_init(s: TSState)
    requires type_ok(s) && init(s)
    ensures valid_forced(s)
    {}

    lemma Inv_choose_ballot(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && choose_ballot(s, s', c) && valid_forced(s)
    ensures valid_forced(s')
    {
        assert s.leader_ballot[c] == -1 && s'.leader_ballot[c] == s.ballot;
        assert forall c :: c in leaders ==> s.leader_ballot[c] < s.ballot == s'.ballot - 1;
        // assert forall c' :: c' in leaders && c' != c ==> s'.leader_ballot[c'] < s'.leader_ballot[c] == s.ballot == s'.ballot - 1;
    }

    lemma Inv_receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor) 
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_higher_ballot(s, s', c, a) && valid_forced(s)
    ensures valid_forced(s')
    {
        assert forall c :: c in leaders ==> (set a | a in acceptors && exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a]) <= (set a | a in acceptors && exists h, v :: PMsg(s'.leader_ballot[c], h, v) in s'.pmsgs[a]);
    }

    lemma Inv_receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, confirmed: int, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors //&& confirmed >= 0 && value > 0 
    requires receive_response_1b(s, s', c, a, confirmed, value) && valid_forced(s)
    ensures valid_forced(s')
    {
        assert confirmed <= s.leader_forced_ballot[c] ==> s.leader_forced_ballot == s'.leader_forced_ballot;
        assert confirmed > s.leader_forced_ballot[c] ==> s'.leader_forced_ballot[c] == confirmed;
        assert confirmed <= s'.leader_forced_ballot[c];
        assert PMsg(s'.leader_ballot[c], confirmed, value) in s'.pmsgs[a];
        // assert !(a in s.promise_count[c]);
        assert a in s'.promise_count[c];
        // assert  (forall a, c :: a in acceptors && c in leaders && s.leader_forced[c] > 0 && a in s.promise_count[c] ==>
        //    (forall bn, v :: PMsg(s.leader_ballot[c], bn, v) in s.pmsgs[a] ==> bn <= s.leader_forced_ballot[c]));
        assert forall c :: c in leaders ==> (s.leader_forced_ballot[c] <= s'.leader_forced_ballot[c]); // leader_forced_ballot[c] can only increase ....
    }

    lemma Inv_propose_value_2a(s: TSState, s': TSState, c: Acceptor, value: Proposal)
    requires  type_ok(s) && type_ok(s') && valid(s) && c in leaders && value > 0 && propose_value_2a(s, s', c, value) && valid_forced(s)
    ensures valid_forced(s')
    {
        assert s'.leader_forced[c] > 0 ==> s'.leader_propose[c] == s'.leader_forced[c];
    }

    lemma Inv_confirm_ballot_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value > 0
    requires confirm_ballot_2b(s, s', c, a, value) && valid_forced(s)
    ensures valid_forced(s')
    {}

    lemma Inv_receive_confirm_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, bn: int, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value > 0
    requires receive_confirm_2b(s, s', c, a, value) && valid_forced(s)
    ensures valid_forced(s')
    {}

    lemma Inv_leader_decide(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders 
    requires leader_decide(s, s', c) && valid_forced(s)
    ensures valid_forced(s')
    {}

}