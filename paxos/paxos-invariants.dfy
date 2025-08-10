include "paxos-classic.dfy"
include "auxiliary.dfy"

module Invariants {

    import opened Paxos_protocol
    import opened Auxiliary_lemmas

    /** define what a valid state is in a Paxos run
        we will add invariants into this predicate later
     */
    ghost predicate valid(s: TSState) /// the list of invariants for all states 
    requires type_ok(s)
    {
        // the followings are the variants that pick up basic features of the Paxos protocol as required in the Consistency lemma
        && (forall c :: c in leaders && (s.leader_decision[c] > 0) ==> (|s.decision_count[c]| >= F+1)) 
        && (forall c :: c in leaders && (s.leader_decision[c] > 0) ==> (s.leader_propose[c] == s.leader_decision[c]))
        && (forall c :: c in leaders && s.leader_propose[c] > 0 ==> s.leader_ballot[c] >= 0)
        && (forall c :: c in leaders && s.leader_propose[c] == 0 ==> s.decision_count[c] == {}) 
        && (forall c, a :: c in leaders && a in acceptors && a in s.decision_count[c] ==> CMsg(s.leader_ballot[c], s.leader_propose[c]) in s.cmsgs[a])
        && (forall c :: c in leaders && s.leader_propose[c] > 0 ==> s.decision_count[c] <= (set a | a in acceptors && CMsg(s.leader_ballot[c], s.leader_propose[c]) in s.cmsgs[a]))
        //
        && (forall c :: c in leaders ==> s.promise_count[c] <= acceptors)
        && (forall a, c :: a in acceptors && c in leaders && a in s.promise_count[c] ==> 
            (exists m :: m in s.pmsgs[a] && m.ballot == s.leader_ballot[c] && m in s.received_promises[c])) // updated
        && (forall a :: a in acceptors ==> s.acceptor_state[a].value >= 0)
        && (forall a :: a in acceptors ==> (s.acceptor_state[a].value > 0 ==> s.acceptor_state[a].highest_ballot >=0 && s.acceptor_state[a].confirmed_ballot >= -1))
        && (forall a :: a in acceptors ==> (s.acceptor_state[a].value > 0 <==> s.acceptor_state[a].confirmed_ballot >= 0))
        && (forall a, m :: a in acceptors && (m in s.pmsgs[a]) ==> (m.confirmed_ballot == -1 <==> m.value == 0))
        && (forall a :: a in acceptors && s.acceptor_state[a].value == 0 ==> s.cmsgs[a] == {})
        && (forall a :: a in acceptors ==> s.acceptor_state[a].highest_ballot >= s.acceptor_state[a].confirmed_ballot)
        && (forall a, m  :: a in acceptors && m in s.pmsgs[a] ==> m.ballot <= s.acceptor_state[a].highest_ballot && m.confirmed_ballot >= -1)
        && (forall a, bn, bn', value :: a in acceptors && (CMsg(bn, value) in s.cmsgs[a]) && (PMsg(bn', -1, 0) in s.pmsgs[a]) ==> bn >= bn') //* invariant W

        // a value is proposed from c only if majority promises are collected 
        && (forall c :: c in leaders ==> (s.leader_propose[c] > 0) ==> |s.promise_count[c]| >= F + 1) // * invariant X
        && (forall c :: c in leaders && s.leader_propose[c] > 0 ==> (
            || s.leader_forced[c] == 0 
            || (s.leader_forced[c] > 0 && s.leader_propose[c] == s.leader_forced[c])
        )) 
        && (forall c, m :: c in leaders &&  m in s.received_promises[c] ==> 
             (m.confirmed_ballot <= s.leader_forced_ballot[c])) // wait, ok
        && (forall c :: c in leaders ==> (s.leader_forced[c] == 0 <==> s.leader_forced_ballot[c] == -1))
        // if two leaders have the same non-zero ballot, then they are the same leader, used in the base case of lemma X
        && (forall c1, c2 :: c1 in leaders && c2 in leaders && s.leader_ballot[c1] == s.leader_ballot[c2] >= 0 ==> c1 == c2 )
        && (forall c :: c in leaders ==> s.leader_ballot[c] < s.ballot)

    }

    /** the list of lemmas to be checked for invariants in all the reachable states 
        for all the transitions, since it's easier to debug in this way.
     */
    lemma Inv_init(s: TSState)
    requires type_ok(s) && init(s)
    ensures valid(s)
    {}

    lemma Inv_choose_ballot(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && choose_ballot(s, s', c)
    ensures valid(s')
    {
        assert s.leader_ballot[c] == -1 && s'.leader_ballot[c] == s.ballot;
        assert forall c :: c in leaders ==> s.leader_ballot[c] < s.ballot == s'.ballot - 1;
        // assert forall c' :: c' in leaders && c' != c ==> s'.leader_ballot[c'] < s'.leader_ballot[c] == s.ballot == s'.ballot - 1;
    }

    lemma Inv_receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_higher_ballot(s, s', c, a)
    ensures valid(s')
    {
        assert forall c :: c in leaders ==> (set a | a in acceptors && exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a]) <= (set a | a in acceptors && exists h, v :: PMsg(s'.leader_ballot[c], h, v) in s'.pmsgs[a]);
        assert forall c2, h, v :: c2 in leaders && !(PMsg(s.leader_ballot[c], h, v) in s.received_promises[c2]) ==> !(PMsg(s'.leader_ballot[c], h, v) in s'.received_promises[c2]);
    }

    lemma Inv_receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, m: PMsg)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_response_1b(s, s', c, a, m)
    ensures valid(s')
    {
        assert m in s'.pmsgs[a] && a in s'.promise_count[c];
        assert m in s'.received_promises[c];
        assert s.leader_propose[c] == s'.leader_propose[c] == 0;
    }

    lemma Inv_propose_value_2a(s: TSState, s': TSState, c: Acceptor, value: Proposal)
    requires  type_ok(s) && type_ok(s') && valid(s) && c in leaders && value > 0 && propose_value_2a(s, s', c, value)
    ensures valid(s')
    {
        assert s.decision_count[c] == s'.decision_count[c];
        assert forall a :: a in acceptors ==> s.cmsgs[a] == s'.cmsgs[a];
        assert forall c, a :: c in leaders && a in acceptors && a in s.decision_count[c] ==> CMsg(s.leader_ballot[c], s.leader_propose[c]) in s.cmsgs[a];
        assert s.leader_ballot[c] == s'.leader_ballot[c];
        assert forall a :: a in acceptors && a in s.decision_count[c] ==> CMsg(s'.leader_ballot[c], s'.leader_propose[c]) in s'.cmsgs[a];
    }

    lemma Inv_confirm_ballot_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && value > 0
    requires confirm_ballot_2b(s, s', c, a, value)
    ensures valid(s')
    {}

    lemma Inv_receive_confirm_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, m: CMsg)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors 
    requires receive_confirm_2b(s, s', c, a, m)
    ensures valid(s')
    {}

    lemma Inv_leader_decide(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders 
    requires leader_decide(s, s', c)
    ensures valid(s')
    {}
}