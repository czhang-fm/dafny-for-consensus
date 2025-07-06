include "paxos-classic.dfy"
include "auxiliary.dfy"

module Leader_ballot_invariants {

    import opened Paxos_protocol
    import opened Auxiliary_lemmas

    // the following are invariants used in the proof of lemma Same_ballot_leaders (split from the main body of invariants)
    ghost predicate valid_leader_ballot(s: TSState) 
    requires type_ok(s)
    {
        // invariants for the proof of lemma 3
        && s.ballot >= 0
        //  && (forall c :: c in leaders ==> s.leader_forced[c] >= 0) // timed out, leave it for later
        && (forall c :: c in leaders ==> s.ballot > s.leader_ballot[c])
        && (forall c :: c in leaders ==> s.leader_ballot[c] >= -1)
        // Base case of lemma 3:
        && (forall c1, c2 :: c1 in leaders && c2 in leaders && s.leader_ballot[c1] == s.leader_ballot[c2] >= 0 ==> c1 == c2)
        // Induction step of lemma 3:
        && (forall c :: c in leaders && s.leader_forced[c] > 0 ==> (exists a, highest, value :: a in acceptors && PMsg(s.leader_ballot[c], highest, value) in s.pmsgs[a] && highest == s.leader_forced_ballot[c] && value == s.leader_forced[c]))
        && (forall a :: a in acceptors && s.acceptor_state[a].value > 0 ==> 
           (exists c :: c in leaders && s.leader_propose[c] == s.acceptor_state[a].value && s.leader_ballot[c] <= s.acceptor_state[a].highest))
        // && (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v > 0 ==> 
        //    bn > h && (exists c :: c in leaders && s.leader_ballot[c] <= h && s.leader_propose[c] == v)) // * invariant Y
        // && (forall a :: a in acceptors && s.acceptor_state[a].value > 0 ==> (exists c :: c in leaders && s.acceptor_state[a].value == s.leader_propose[c] && s.acceptor_state[a].highest == s.leader_ballot[c]))// this does not hold
        && (forall bn, h, v, a :: a in acceptors && PMsg(bn, h , v) in s.pmsgs[a] && v > 0 ==> //(&& h >= 0) ==> 
           bn > h && (exists c :: c in leaders && s.leader_ballot[c] == h && s.leader_propose[c] == v)) // * slightly stronger than the above * invariant Z
        // to replace part of the auxiliary lemma for lemma 5
        // && (forall c, a, h, v :: c in leaders && a in acceptors && PMsg(s.leader_ballot[c], h, v) in s.pmsgs[a] ==> h <= s.leader_forced_ballot[c] && v == s.leader_propose[c])
        // && (forall a :: a in acceptors && s.acceptor_state[a].value > 0 ==> (exists c, v :: c in leaders && s.leader_ballot[c] >= 0 && CMsg(s.leader_ballot[c], v) in s.cmsgs[a]))
        // && (forall a :: a in acceptors ==> s.acceptor_state[a].value >= 0 && s.acceptor_state[a].highest >= -1)
        // && (forall a, bn, highest, value :: a in acceptors && (PMsg(bn, highest, value) in s.pmsgs[a]) ==> (highest >= -1 && value >= 0))
        // // && (forall a, bn, highest, value :: a in acceptors && (PMsg(bn, highest, value) in s.pmsgs[a]) ==> (highest == -1 <==> value == 0))
        // && (forall c :: c in leaders ==> (s.leader_forced[c] >= 0 && s.leader_forced_ballot[c] >= -1))
        // // && (forall c :: c in leaders ==> (s.leader_forced[c] > 0 <==> s.leader_forced_ballot[c] > -1))

        /// the following may be removed later ... if not used
        && s.ballot >= 0 && s.ballot == |s.ballot_mapping|
        && (forall c :: c in leaders && s.leader_ballot[c] >= 0 ==> s.leader_ballot[c] < |s.ballot_mapping|)
        && (forall c :: c in leaders && s.leader_ballot[c] >= 0 ==> s.ballot_mapping[s.leader_ballot[c]] == c)
        && (forall c1, c2 :: c1 in leaders && c2 in leaders && s.leader_ballot[c1] == s.leader_ballot[c2] > 0 ==> c1 == c2)
    }

    /** the list of lemmas for the leader ballot related invariants in all the reachable states 
        for all the transitions, since it's easier to debug in this way.
     */
    lemma Inv_ballot_init(s: TSState)
    requires type_ok(s) && init(s)
    ensures valid_leader_ballot(s)
    {}

    lemma Inv_ballot_choose_ballot(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid_leader_ballot(s) && c in leaders && choose_ballot(s, s', c)
    ensures valid_leader_ballot(s')
    {}

    lemma Inv_ballot_receive_higher_ballot(s: TSState, s': TSState, c: Acceptor, a: Acceptor)
    requires type_ok(s) && type_ok(s') && valid_leader_ballot(s) && c in leaders && a in acceptors && receive_higher_ballot(s, s', c, a)
    ensures valid_leader_ballot(s')
    {}

    lemma Inv_ballot_receive_response_1b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, highest: int, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid_leader_ballot(s) && c in leaders && a in acceptors && receive_response_1b(s, s', c, a, highest, value)
    ensures valid_leader_ballot(s')
    {}

    lemma Inv_ballot_propose_value_2a(s: TSState, s': TSState, c: Acceptor, value: Proposal)
    requires  type_ok(s) && type_ok(s') && valid_leader_ballot(s) && c in leaders && value != 0 && propose_value_2a(s, s', c, value)
    ensures valid_leader_ballot(s')
    {}

    lemma Inv_ballot_confirm_ballot_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid_leader_ballot(s) && c in leaders && a in acceptors && value > 0
    requires confirm_ballot_2b(s, s', c, a, value)
    ensures valid_leader_ballot(s')
    {}

    lemma Inv_ballot_receive_confirm_2b(s: TSState, s': TSState, c: Acceptor, a: Acceptor, bn: int, value: Proposal)
    requires type_ok(s) && type_ok(s') && valid_leader_ballot(s) && c in leaders && a in acceptors && value > 0
    requires receive_confirm_2b(s, s', c, a, value)
    ensures valid_leader_ballot(s')
    {}

    lemma Inv_ballot_leader_decide(s: TSState, s': TSState, c: Acceptor)
    requires type_ok(s) && type_ok(s') && valid_leader_ballot(s) && c in leaders 
    requires leader_decide(s, s', c)
    ensures valid_leader_ballot(s')
    {}
}