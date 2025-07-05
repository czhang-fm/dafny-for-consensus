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
        // the followings are the variants that pick up basic features of the Paxos protocol
        && (forall c :: c in leaders && (s.leader_decision[c] > 0) ==> (|s.decision_count[c]| >= F+1)) 
        && (forall c :: c in leaders && (s.leader_decision[c] > 0) ==> (s.leader_propose[c] == s.leader_decision[c]))
        && (forall c :: c in leaders && s.leader_propose[c] > 0 ==> s.leader_ballot[c] >= 0)
        && (forall c :: c in leaders ==> s.promise_count[c] <= acceptors)
        && (forall a, c :: a in acceptors && c in leaders && a in s.promise_count[c] ==> (exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a])) // updated
        && (forall a :: a in acceptors ==> s.acceptor_state[a].value >= 0)
//        && (forall a :: a in acceptors ==> s.acceptor_ballot[a] <= s.acceptor_state[a].highest) //
//        && (forall a, bn, value :: a in acceptors && CMsg(bn, value) in s.cmsgs[a] ==> bn <= s.acceptor_ballot[a]) //
//        && (forall a :: a in acceptors && s.acceptor_ballot[a] >= 0 ==> (s.acceptor_state[a].highest >= s.acceptor_ballot[a] && s.acceptor_state[a].value > 0)) //

        && (forall a :: a in acceptors ==> (s.acceptor_state[a].value > 0 ==> s.acceptor_state[a].highest >=0) )
        && (forall a, bn, highest, value :: a in acceptors && (PMsg(bn, highest, value) in s.pmsgs[a]) ==> (highest == -1 <==> value == 0))
        && (forall a :: a in acceptors && s.acceptor_state[a].value == 0 ==> s.cmsgs[a] == {})
        && (forall a, bn, highest, value  :: a in acceptors && (PMsg(bn, highest, value) in s.pmsgs[a]) ==> bn <= s.acceptor_state[a].highest)
        && (forall a, bn, bn', value :: a in acceptors && (CMsg(bn, value) in s.cmsgs[a]) && (PMsg(bn', -1, 0) in s.pmsgs[a]) ==> bn >= bn') //* invariant W

        // a value is proposed from c only if majority promises are collected 
        && (forall c :: c in leaders ==> (s.leader_propose[c] > 0) ==> |s.promise_count[c]| >= F + 1) // * invariant X
        && (forall c :: c in leaders && s.leader_propose[c] > 0 ==> (
            || s.leader_forced[c] == 0 
            || (s.leader_forced[c] > 0 && s.leader_propose[c] == s.leader_forced[c])
        ))
        && (forall c, a :: c in leaders && a in acceptors && a in s.promise_count[c] ==> (exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a] && h <= s.leader_forced_ballot[c]))
        && (forall c :: c in leaders && s.leader_forced[c] == 0 && s.leader_ballot[c] >= 0 ==> s.leader_forced_ballot[c] < s.leader_ballot[c])
        && (forall c :: c in leaders ==> (s.leader_forced[c] == 0 <==> s.leader_forced_ballot[c] == -1))
        && (forall a, bn, h, v :: a in acceptors && PMsg(bn, h, v) in s.pmsgs[a] ==> (h < 0 <==> h == -1)) // another auxiliary inv
        && (forall c :: c in leaders ==> (s.promise_count[c] <= (set a | a in acceptors && exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a]))) // used in the proof of lemma 2
        // && (forall c, a, h, v :: c in leaders && a in acceptors && s.leader_forced[c] == 0 && a in s.promise_count[c] && PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a] ==> (h == -1 && v == 0)) //* as lemma 1
        // && (forall c :: c in leaders ==> (s.leader_propose[c] > 0) ==> s.leader_forced[c] == 0 ==> |set a | a in acceptors && PMsg(s.leader_ballot[c], -1, 0) in s.pmsgs[a]| >= F + 1) //* invariant X' as lemma 2
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
        // assert s.leader_ballot[c] == -1 && s'.leader_ballot[c] == s.ballot;
        // assert forall c' :: c' in leaders ==> s.leader_ballot[c'] < s.ballot == s'.ballot - 1;
        // assert forall c' :: c' in leaders && c' != c ==> s'.leader_ballot[c'] < s'.leader_ballot[c] == s.ballot == s'.ballot - 1;
    }

    lemma Inv_receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_higher_ballot(s, s', c, a)
    ensures valid(s')
    {
        assert forall c :: c in leaders ==> (set a | a in acceptors && exists h, v :: PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a]) <= (set a | a in acceptors && exists h, v :: PMsg(s'.leader_ballot[c], h, v) in s'.pmsgs[a]);
    }

    lemma Inv_receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, highest: int, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders && a in acceptors && receive_response_1b(s, s', c, a, highest, value)
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

    lemma Inv_leader_decide(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid(s) && c in leaders 
    requires leader_decide(s, s', c)
    ensures valid(s')
    {}
}