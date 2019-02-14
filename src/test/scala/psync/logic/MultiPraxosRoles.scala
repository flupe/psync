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

  // set of active processes
  val act = Variable("act").setType(FSet(pid))
  val act1 = Variable("act1").setType(FSet(pid))

  // log-related types & uninterpreted functions
  val commandType   = UnInterpreted("command")
  val committedType = Bool
  val logEntryType  = Product(commandType, committedType)
  val keyType       = Int
  val log        = UnInterpretedFct("log", Some(pid ~> FMap(keyType, logEntryType)))
  val log1       = UnInterpretedFct("log1", Some(pid ~> FMap(keyType, logEntryType)))
  val lastIndex  = UnInterpretedFct("lastIndex", Some(pid ~> keyType))
  val lastIndex1 = UnInterpretedFct("lastIndex1", Some(pid ~> keyType))

  val i = Variable("i").setType(keyType)
  val j = Variable("j").setType(keyType)

  val send = UnInterpretedFct("send", Some(pid ~> FMap(pid, commandType)))
  val mbox = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, commandType)))

  /* NOTE:
   *   right now the type of send is too permissive
   *   perhaps we could consider the following type
   *   val send = UnInterpretedFct("send", Some(pid ~> Product(payloadType, FSet(pid))))
   *   (i.e we can only send one msg at each round -- to many processes)
   */


  // TODO(flupe): add cardinality constraints

  val axioms = And(
    // q in mbox(p) <=> q sent msg to p and p heard of q
    ForAll(List (p, q),
      (q ∈ KeySet(mbox(p))) ≡ ((q ∈ ho(p) ∧ (p ∈ KeySet(send(q)))))),

    // process p receives from q what q sent to p, if q has been heard of
    ForAll(List (p, q),
      ((q ∈ ho(p)) ∧ (p ∈ KeySet(send(q)))) ==> (mbox(p).lookUp(q) ≡ send(q).lookUp(p))),

    // if a process p sends nothing, then it is received by no one.
    ForAll(List(p),
      (Size(send(p)) ≡ 0) ==> (ForAll(List(q), p ∉ KeySet(mbox(q))))),

    // p receives messages only from processes it has heard of
    ForAll(List(p), (KeySet(mbox(p)) ⊆ ho(p))),

    // p receives messages only from processes that have sent something to p
    // ForAll(List(p),
    //   (KeySet(mbox(p)) ⊆ Comprehension(List(q), p ∈ KeySet(send(q))))),
  )


  // invariant pre-broadcast
  val inv0 = And(
    // leader is active
    leader ∈ act,

    // all processes share same lastIndex
    ForAll(List(p), lastIndex(p) ≡ lastIndex(leader)),

    // each process has entries up to lastIndex(p),
    // and they are equal to entries in log(leader)
    ForAll(List(p, i),
      (i < lastIndex(p)) ==>
        ((i ∈ KeySet(log(p))) ∧ (log(p).lookUp(i) ≡ log(leader).lookUp(i)))),
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
         ∧ (p ∈ act1))
    ),

    // otherwise, becomes inactive, and conserves values
    ForAll(List (p), (p ∉ act) ==> ((p ∉ act1) ∧ (log1(p) ≡ log(p)))),
    ForAll(List (p), ((p ∈ act) ∧ (Size(mbox(p)) ≡ 0)) ==> ((p ∉ act1) ∧ (log1(p) ≡ log(p)))),
  )


  /* Invariant Post-Round1
   * - leader is active
   * - if node is active, it has the same command (on lastIndex(p)) as the leader, uncommitted
   * - for every process, the log prior to lastIndex is left unchanged
   */
  val inv1 = And(
    // leader active
    leader ∈ act1,

    // all active processes have same command
    ForAll(List(p),
      (p ∈ act1) ==> (log1(p).lookUp(lastIndex1(p))._1 ≡ log(leader).lookUp(lastIndex(leader))._1)
    ),

    // all processes have the same values in the log (before lastIndex(i))
    ForAll(List(p, i),
      (i < lastIndex1(leader)) ==> (log1(p).lookUp(i) ≡ log1(leader).lookUp(i))),
  )


  ignore("inv0 ∧ round1 ⇒ inv1") {
    val fs = List(
      axioms,
      inv0,
      round1,
      Not(inv1)
    )

    val reducer = c1e1
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

    // SEND ==========================================================================

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

  // TODO(flupe): add prime maps

  /* Invariant Post-Round2
   * - if leader is active, a majority of nodes have the same active command as the leader,
   * - if leader is active, it has committed the value
   * - other nodes have the same prefix-log (?)
   */
  val inv2 = And(True())

  ignore("inv1 ∧ round2 ⇒ inv2") {
    // val fs = List(
    //   axioms,
    //   inv1,
    //   round2,
    //   Not(inv2)
    // )

    // val reducer = c1e1
    // assertUnsat(fs, debug=false, to=60000, reducer=reducer)
    // val f0 = reduce(c2e1, fs, true, true)
    // getModel(fs, to=60000, reducer=reducer)
  }

}
