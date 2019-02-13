package psync.logic

import psync.formula._
import psync.formula.InlineOps._
import TestCommon._

import org.scalatest._

class MultiPraxosRoles extends FunSuite {

  val p = Variable("p").setType(pid)
  val q = Variable("q").setType(pid)

  // during broadcast, one leader known to all
  val leader = Variable("leader").setType(pid)
  val π = Variable("pi").setType(FSet(pid)) // set of all processes

  // set of active processes
  val act = Variable("act").setType(FSet(pid))
  val act1 = Variable("act1").setType(FSet(pid))

  // log-related types & uninterpreted functions
  val commandType = UnInterpreted("command")
  val committedType = Bool
  val logEntryType = Product(commandType, committedType)
  val key = Int

  val i = Variable("i").setType(key)

  val log        = UnInterpretedFct("log", Some(pid ~> FMap(key, logEntryType)))
  val log1       = UnInterpretedFct("log1", Some(pid ~> FMap(key, logEntryType)))
  val lastIndex  = UnInterpretedFct("lastIndex", Some(pid ~> key))
  val lastIndex1 = UnInterpretedFct("lastIndex1", Some(pid ~> key))

  val payloadType   = UnInterpreted("payload")

  val send = UnInterpretedFct("send", Some(pid ~> FMap(pid, commandType)))
  val mbox = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, commandType)))

  // right now the type of send is too permissive
  // perhaps we could consider the following type
  // val send = UnInterpretedFct("send", Some(pid ~> Product(payloadType, FSet(pid))))
  // (i.e we can only send one msg at each roung -- to many processes)

  // TODO: describe each axiom
  val axioms = And(
    // π is the set of all processes
    ForAll(List (p), (p ∈ π)),

    // all processes in ho are in the keyset of the mbox
    // and the converse is true (keyset of send)
    ForAll(List (p, q),
      ((q ∈ ho(p) ∧ (p ∈ KeySet(send(q)))) ==> (q ∈ KeySet(mbox(p))))),

    ForAll(List (p, q),
      (q ∈ KeySet(mbox(p))) ==> ((q ∈ ho(p) ∧ (p ∈ KeySet(send(q)))))),

    ForAll(List (p, q),
      (q ∈ ho(p) ∧ (p ∈ KeySet(send(q)))) ==> (IsDefinedAt(mbox(p), q) ∧ IsDefinedAt(send(q), p))),

    ForAll(List (p, q),
      (q ∉ ho(p)) ==> (Not(IsDefinedAt(mbox(p), q)))),

    ForAll(List (p, q),
      (Not(IsDefinedAt(mbox(p), q))) ==> (q ∉ ho(p))),

    ForAll(List (p, q),
      (p ∉ KeySet(send(q))) ==> (Not(q ∈ KeySet(mbox(p))))),

    // process p receives from q what q sent to p
    ForAll(List (p, q), ((q ∈ ho(p) ) ∧ (p ∈ KeySet(send(q)))) ==> (mbox(p).lookUp(q) ≡ send(q).lookUp(p))),

    ForAll(List(p), SubsetEq(KeySet(mbox(p)), ho(p))),
  )

  // invariant pre-broadcast
  val inv0 = And(
    leader ∈ act,
    ForAll(List(p), lastIndex(p) ≡ lastIndex(leader))
  )


  // =================================================================================

  // Inner algorithm, round 1
  val round1 = And(
    // active processes after round1 were active prior to round1
    act1 ⊆ act,

    // SEND ==========================================================================

    // non-leaders do not send anything
    ForAll(List(p), (p ≠ leader) ==> (Size(send(p)) ≡ 0)),

    // leader sends current command to all processes
    ForAll(List(q), send(leader).lookUp(q) ≡ log(leader).lookUp(lastIndex(leader))._1),


    // UPDATE ========================================================================

    // leader stays active and conserves values
    leader ∈ act1,
    log1(leader) ≡ log(leader),

    // all nodes keep the same lastIndex
    ForAll(List(p), lastIndex1(p) ≡ lastIndex(p)),

    // if active process receives msg from leader,
    // update log and stay active
    ForAll(List (p),
      ((p ∈ act) ∧ (Size(mbox(p)) > 0)) ==>
        ((log1(p) ≡ log(p).updated(lastIndex(p), Tuple(mbox(p).lookUp(leader), False())))
        // if we use instead the more direct assertion below, the latter test works fine
        //((log1(p) ≡ log(p).updated(lastIndex(p), Tuple(send(leader).lookUp(p), False())))
         ∧ (p ∈ act1)) 
    ),

    // otherwise, becomes inactive, and conserves values
    ForAll(List (p), (p ∉ act) ==> ((p ∉ act1) ∧ (log1(p) ≡ log(p)))),
    ForAll(List (p), ((p ∈ act) ∧ (Size(mbox(p)) ≡ 0)) ==> ((p ∉ act1) ∧ (log1(p) ≡ log(p)))),
  )

  /* Invariant Post-Round1
   * - leader is active
   * - if node is active, it has the same active command as the leader, uncommitted
   * - the previous log is left untouched
   */
  val inv1 = And(
    // leader active
    leader ∈ act1,

    // all active processes have same command
    ForAll(List(p),
      (p ∈ act1) ==> (log1(p).lookUp(lastIndex1(p))._1 ≡ log(leader).lookUp(lastIndex(leader))._1)
    )
  )

  test("inv0 ∧ round1 ⇒ inv1") {
    val fs = List(
      axioms,
      inv0,
      round1,
      Not(inv1)
    )

    val reducer = c3e1
    assertUnsat(fs, debug=false, to=60000, reducer=reducer)
    // val f0 = reduce(c2e1, fs, true, true)
    // getModel(fs, to=60000, reducer=reducer)
  }

  // =================================================================================
  // Inner algorithm, round 2
  val send2 = UnInterpretedFct("send", Some(pid ~> FMap(pid, UnitT())))
  val mbox2 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, UnitT())))

  val round2 = And(
    act1 ⊆ act,

    // SEND ========================

    // leader do not send anything
    Size(send2(leader)) ≡ 0,

    // non-leaders send receipt to leader
    ForAll(List(p), ((p ∈ act) ∧ (p ≠ leader)) ==> send2(p).lookUp(leader) ≡ UnitLit()),

    // non-active nodes do nothing
    ForAll(List(p), (p ∉ act) ==> Size()),


    // UPDATE ======================

    // active processes that aren't the leader stay active
    ForAll(List(p), ((p ∈ act) ∧ (p ≠ leader)) ==> (p ∈ act1)),

    // non-leaders keep same log
    ForAll(List(p), (p ≠ leader) ==> (log1(p) ≡ log(p))),

    // all nodes keep same lastIndex
    ForAll(List(p), lastIndex1(p) ≡ lastIndex(p)),

    // if leader receives majority, commits and stays active
    (Size(mbox2(leader)) >= (n / 2)) ==> (
      log(leader).updated(lastIndex(leader),
        Tuple((log(leader).lookUp(lastIndex(leader)))._1, True()))
      ∧ (leader ∈ act1)
    ),

    // otherwise, leader no longer active
    // keeps same log
    (Size(mbox(leader)) < (n / 2)) ==> ((log1(leader) ≡ log(leader)) ∧ (leader ∉ act1)),
  )

  /* Invariant Post-Round2
   * - if leader is active, a majority of nodes have the same active command as the leader,
   * - if leader is active, it has committed the value
   * - other nodes have the same prefix-log (?)
   */
  val inv2 = And()

}
