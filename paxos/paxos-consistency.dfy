include "paxos-classic.dfy"
include "auxiliary.dfy"
include "paxos-invariants.dfy"
include "promise-invariants.dfy"
include "supporting-lemmas.dfy"

module Consistency {

    import opened Paxos_protocol
    import opened Auxiliary_lemmas
    import opened Invariants
    import opened PromiseInvariants
    import opened SupportingLemmas
        
    // lemma X assumes the smallest chosen decision from the system, which later helps to prove the following Consistency lemma
    // lemma X(s: TSState, c1: Acceptor, c2: Acceptor)
    // requires type_ok(s) && valid(s) && valid_promise(s)
    // requires c1 in leaders && c2 in leaders && s.leader_propose[c1] > 0 && s.leader_propose[c2] > 0
    // requires s.leader_ballot[c1] <= s.leader_ballot[c2]
    // requires |set a | a in acceptors && CMsg(s.leader_ballot[c1], s.leader_propose[c1]) in s.cmsgs[a]| >= F + 1
    // requires forall c :: c in leaders && s.leader_ballot[c] < s.leader_ballot[c1] ==> (|set a | a in acceptors && CMsg(s.leader_ballot[c], s.leader_propose[c]) in s.cmsgs[a]| <= F)
    // ensures s.leader_propose[c1] == s.leader_propose[c2] // we need to prove the case for all c in leader in between c1 and c2
    // decreases s.leader_propose[c2] - s.leader_propose[c1]
    // {
    //     if s.leader_ballot[c1] == s.leader_ballot[c2] { // trivial
    //         assert c1 == c2;
    //     } else { // s.leader_ballot[c1] < s.leader_ballot[c2], and since s.leader_propose[c2] > 0, we have 
    //         // assert |s.promise_count[c2]| >= F + 1;
    //         // // to rule out the non-force case
    //         // NonforceX(s, c1, c2);
    //         // // the force case:
    //         // assert s.leader_forced[c2] > 0;
    //         // assert s.leader_forced_ballot[c2] >= 0;
    //         // var c := leader_proposal_forced(s, c2);
    //         // assert s.leader_ballot[c] < s.leader_ballot[c2];
    //         // NonforceLarger(s, c1, c);
    //         // assert s.leader_ballot[c1] <= s.leader_ballot[c];
    //         // X(s, c1, c);
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