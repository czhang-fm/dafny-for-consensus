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
}