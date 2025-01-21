# Dafny models for consensus protocol
## Introduction
This repository is planned to be a store for a number of Dafny models. A purpose of this repostory is to be the home of a few example models for the COSC437 "_verification of security protocols_" lectured at the university of Canterbury. This also serves a initial feasibility study for verification of larger scaled and more complex protocols, such as those currently adopted in the Blockchain communities (Tendermint, algorand, and Ethereum-SSF, to name a few).

## List of models
<p> <b>A very simple Two-Phase commmit protocol</b> This model is translated from the TLA model, A.1 and A.2, in the 2004 paxos-acp paper [3] which consists of a set of resource managers (RMs) that have coordinated update, satisfying the following properties: </p>

- Stability: Once an RM has entered the committed or aborted state, it remains in that state forever.

- Consistency: It is impossible for one RM to be in the committed state and another to be in the aborted state.

<p>A distinguished transaction manager (TM) process coordinates a decision-making procedure. The communication model is asynchronous, i.e., messages cannot get lost, but there is not a time limit for message delivery. In this type of modelling, we define states and transitions in the form of predicates. We only prove the safety condition (Consistency) which is the last lemma in the model.</p>

<p><b>A basic paxos protocol</b> </p> This model refers to the classic Paxos asynchronous model with multiple coordinators and multiple acceptors.

<p></p>

## References

[1]: Leslie Lamport. The part-time parliament. ACM transactions on Computer Systems, 16(2):133-169, May 1998

[2]: Leslie Lamport. Paxos Made Simple, 2001

[3]: Jim Gray and Leslie Lamport: Consensus on Transaction Commit. MSR-TR-2003-96, 2004
