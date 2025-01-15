/* This is new model in Dafny for the very simple Two-Phase commmit protocol
 * The model is translated from the TLA model, A.1 and A.2, in the 2004 paxos-acp paper 
 * which consists of a set of resource managers (RMs) that have coordinated update, satisfying
 * the following properties: 
 *
 * Stability: Once an RM has entered the committed or aborted state, it remains in that state forever.
 * Consistency: It is impossible for one RM to be in the committed state and another to be in the aborted state.
 * A distinguished transaction manager (TM) process coordinates a decision-making procedure.
 *
 * The communication model is asynchronous: 
 *  i.e., messages cannot get lost, but there is not a time limit for message delivery
 *
 * Simplifications in the model:
 * -- No abort message is sent by an RM when it decides to abort (as it cannot be distinguished from a silent-fail)
 * -- No modelling message loss (as it cannot be distinguished from being ignored by the receiver)
 *
 * In this type of modelling, we define states and transitions in the form of predicates.
 * We only prove the safety condition (Consistency) which is the last lemma in the model.
 */

type ResourceManager(==)
datatype RMState = Working | Prepared | Committed | Aborted
const RM: set<ResourceManager>
datatype TMState = Init | TCommitted | TAborted
datatype RMessage = Pair(s: RMState, rm: ResourceManager) 
//type TMessage = TMState // Here we reuse the TMState values for the messages sent out from the TM

// Each RM has 4 states, with the following 4 transition patterns:
// Working --> Prepared; Working --> Aborted; Prepared --(TCommited)--> Committed; Prepared --(TAborted)--> Aborted.
// Note that if an RM is in the Prepared state, it can perform the last two transitions only after receiving messages from the TM.

// The Transaction Manager (TM) has three states, with the following 2 transition patterns
// Init --> Abort; Init --(RM-Prepared)--> TCommmitted
// TM can only make the latter transition after Prepared messages are received from all RMs.

// A state consists of the states of all the RMs, the state of TM, set of messages set by the RMs and the TM.
// The set of Resource Managers (RM) can have any size.
datatype TSState = TSState(
  rm: map<ResourceManager, RMState>, 
  tm: TMState, 
  rmsg: set<RMessage>, 
  tmsg: set<TMState>, 
  tmPrepared: set<ResourceManager>
  )

// specify the invariants of a state
ghost predicate valid(s: TSState){
    // The first set of invariants are about the well-typed-ness of values and messages
    && s.rm.Keys == RM
    && s.tmPrepared <= RM
    && s.tm in {Init, TCommitted, TAborted}
    && s.tmsg <= {Init, TCommitted, TAborted}
    && (forall st, rm :: (Pair(st, rm) in s.rmsg) ==> (st in {Working, Prepared, Committed, Aborted} && rm in RM))
    // The second set of invariants are related to the logical connections between components of a state, which should
    // be maintained by each individual transition relation. All the following condition should be able to enforce
    // the safety lemma at the end of this model.
    && (s.tm == TCommitted <==> TCommitted in s.tmsg)
    && (s.tm == TAborted <==> TAborted in s.tmsg)
    && (forall r :: r in RM && (s.tm == Init) && (r in s.tmPrepared) ==> s.rm[r] == Prepared) // inv-2
    && (forall r :: r in RM && (s.tm == Init) && (Pair(Prepared, r) in s.rmsg) ==> s.rm[r] == Prepared) // inv-1
    && (s.tm == TCommitted ==> (forall r :: r in RM && (s.rm[r] == Prepared || s.rm[r] == Committed)))
    && (s.tm != TCommitted ==> (forall r :: r in RM && s.rm[r] != Committed))
}

// specify the initial state, and Dafny is able to prove that all initial states are valid.
ghost predicate init(s: TSState)
{
    && s.rm.Keys == RM
    && s.tmPrepared <= RM
    && s.tm == Init
    && s.rmsg == {}
    && s.tmsg == {}
    && s.tmPrepared == {}
    && (forall r :: r in RM && s.rm[r] == Working)
}
lemma Inv_init(s: TSState)
  requires init(s)
  ensures valid(s)
{}

// rmPrepare: a ResourceManager may transition from Working to Prepared, and send out rmsg (Prepared, r)
predicate rmPrepare(s: TSState, s': TSState, r: ResourceManager)
  requires valid(s) && r in RM
{
    && s.rm[r] == Working
    && s'.rm == s.rm[r:= Prepared]
    && s'.tm == s.tm
    && s'.tmsg == s.tmsg
    && s'.rmsg == s.rmsg + {Pair(Prepared, r)}
    && s'.tmPrepared == s.tmPrepared
}
lemma Inv_rmPrepare(s: TSState, s': TSState, r: ResourceManager)
  requires valid(s) && rmPrepare(s, s', r) && r in RM
  ensures valid(s')
{}

// rmAbort: a ResourceManager may independently transiton from Working to Aborted
predicate rmAbort(s: TSState, s': TSState, r: ResourceManager)
  requires valid(s) && r in RM
{
    && s.rm[r] == Working
    && s'.rm == s.rm[r:= Aborted]
    && s'.tm == s.tm
    && s'.tmsg == s.tmsg
    && s'.rmsg == s.rmsg
    && s'.tmPrepared == s.tmPrepared
}
lemma Inv_rmAbort(s: TSState, s': TSState, r: ResourceManager)
  requires valid(s) && rmAbort(s, s', r) && r in RM
  ensures valid(s')
{}

// rmRcvCommmit: after received TCommit from TM, a ResourceManager may transiton from any state to Committed
predicate rmRcvCommit(s: TSState, s': TSState, r: ResourceManager)
  requires valid(s) && r in RM
{
    && TCommitted in s.tmsg
    && s'.rm == s.rm[r:= Committed]
    && s'.tm == s.tm
    && s'.rmsg == s.rmsg
    && s'.tmsg == s.tmsg
    && s'.tmPrepared == s.tmPrepared
}
lemma Inv_rmRcvCommit(s: TSState, s': TSState, r: ResourceManager)
  requires valid(s) && rmRcvCommit(s, s', r) && r in RM
  ensures valid(s')
{}

// rmRcvAbort: after received TAborted from TM, a ResourceManager may transiton from any state to Aborted
predicate rmRcvAbort(s: TSState, s': TSState, r: ResourceManager)
  requires valid(s) && r in RM
{
    && TAborted in s.tmsg
    && s'.rm == s.rm[r:= Aborted]
    && s'.tm == s.tm
    && s'.rmsg == s.rmsg
    && s'.tmsg == s.tmsg
    && s'.tmPrepared == s.tmPrepared
}
lemma Inv_rmRcvAbort(s: TSState, s': TSState, r: ResourceManager)
  requires valid(s) && rmRcvAbort(s, s', r) && r in RM
  ensures valid(s')
{}

// rmRcvPrepared: The transition manager (TM) receives (Prepared r) and adds to its collection (tmPrepared)
predicate tmRcvPrepared(s: TSState, s': TSState, r: ResourceManager)
  requires valid(s) && r in RM
{
    && s.tm == s'.tm == Init
    && Pair(Prepared, r) in s.rmsg
    && s'.tmPrepared == s.tmPrepared + {r}
    && s'.rm == s.rm
    && s'.rmsg == s.rmsg
    && s'.tmsg == s.tmsg
}
lemma Inv_tmRcvPrepared(s: TSState, s': TSState, r: ResourceManager)
  requires valid(s) && tmRcvPrepared(s, s', r) && r in RM
  ensures valid(s')
{}

// tmCommit: If TM collected all Prepared messages from RM, it may transition to TCommitted and send out TCommitted (irreversibly)
predicate tmCommit(s: TSState, s': TSState)
  requires valid(s)
{
    && s.tm == Init
    && s.tmPrepared == s'.tmPrepared == RM
    && s'.tm == TCommitted
    && s'.tmsg == s.tmsg + {TCommitted}
    && s'.rm == s.rm
    && s'.rmsg == s.rmsg
}
lemma Inv_tmCommit(s: TSState, s': TSState)
  requires valid(s) && tmCommit(s, s')
  ensures valid(s')
{}

// tmAbort: TM may choose to make a trnasition to TAborted and send out TAborted any time
// This step is irrevesible
predicate tmAbort(s: TSState, s': TSState)
  requires valid(s)
{
    && s.tm == Init
    && s'.tm == TAborted
    && s'.tmsg == s.tmsg + {TAborted}
    && s'.rm == s.rm
    && s'.rmsg == s.rmsg
    && s'.tmPrepared == s.tmPrepared
}
lemma Inv_tmAbort(s: TSState, s': TSState)
  requires valid(s) && tmCommit(s, s')
  ensures valid(s')
{}

// The safety property as enforced by the invariants encoded in the valid() prediate
lemma consistency(s: TSState, r1: ResourceManager, r2: ResourceManager)
  requires valid(s) && r1 in RM && r2 in RM
  ensures s.rm[r1] == Committed ==> s.rm[r2] != Aborted
{}
