package psync.logic

import psync.formula._
import psync.formula.InlineOps._
import TestCommon._

import org.scalatest._

class MultiPraxosRoles extends FunSuite {

  // Housekeeping {{{
  val p = Variable("p").setType(pid)
  val q = Variable("q").setType(pid)

  // during broadcast, one leader known to all
  val leader = Variable("leader").setType(pid)

  // set of active processes
  val act = Variable("act").setType(FSet(pid))
  val act1 = Variable("act1").setType(FSet(pid))
  val pi = Variable("pi").setType(FSet(pid))

  // log-related types & uninterpreted functions
  val cmdType   = UnInterpreted("command")
  val logEntryType  = Product(cmdType, Bool)
  val log        = UnInterpretedFct("log", Some(pid ~> FMap(Int, logEntryType)))
  val log1       = UnInterpretedFct("log1", Some(pid ~> FMap(Int, logEntryType)))
  val lastIndex  = UnInterpretedFct("lastIndex", Some(pid ~> Int))
  val lastIndex1 = UnInterpretedFct("lastIndex1", Some(pid ~> Int))

  val i = Variable("i").setType(Int)
  val j = Variable("j").setType(Int)


  def prime(f: Formula) : Formula = {
    val symMap = Map[Symbol, Symbol](
      log       -> log1,
      lastIndex -> lastIndex1,
    )

    val varMap = Map[Variable, Variable](
      act       -> act1,
    )

    val f1 = FormulaUtils.mapSymbol(x => symMap.getOrElse(x, x), f)
    FormulaUtils.alpha(varMap, f1)
  }


  /* NOTE:
   *   right now the type of send is too permissive
   *   perhaps we could consider the following type
   *   val send = UnInterpretedFct("send", Some(pid ~> Product(payloadType, FSet(pid))))
   *   (i.e we can only send one msg at each round -- to many processes)
   */
  // }}}
  // Axioms {{{

  def axioms(send: UnInterpretedFct, mbox: UnInterpretedFct) = And(
    ForAll(List(p), p ∈ pi),

    pi.card ≡ n,

    ForAll(List (p), KeySet(mbox(p)) ⊆ pi),
    ForAll(List (p), KeySet(send(p)) ⊆ pi),
    act ⊆ pi,
    ForAll(List (p), ho(p) ⊆ pi),

    // only active processes can send messages
    ForAll(List (p), KeySet(mbox(p)) ⊆ act),

    ForAll(List(p), KeySet(mbox(p)).card <= n),
    ForAll(List(p), KeySet(mbox(p)).card >= 0),
    act.card <= n,

    ForAll(List(p), (ho(p)).card <= n),
    ForAll(List(p), (ho(p)).card >= 0),

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

  // }}}
  // Initial invariant {{{
  //
  val inv0 = And(
    // everyone is active (for now)
    ForAll(List(p), p ∈ act),

    // all processes share same lastIndex
    ForAll(List(p), lastIndex(p) ≡ lastIndex(leader)),

    // each process has entries up to lastIndex(p),
    // and they are equal to entries in log(leader)
    ForAll(List(p, i),
      ((IntLit(0) <= i) ∧ (i < lastIndex(p))) ==>
        ((i ∈ KeySet(log(p))) ∧ (log(p).lookUp(i) ≡ log(leader).lookUp(i)))),
  )

  // }}}
  // Round 1 {{{

  val send1 = UnInterpretedFct("send", Some(pid ~> FMap(pid, cmdType)))
  val mbox1 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, cmdType)))

  val round1 = And(
    // active processes after round1 were active prior to round1
    act1 ⊆ act,

    // SEND ==========================================================================

    // non-leaders do not send anything
    ForAll(List(p), (p ≠ leader) ==> (Size(send1(p)) ≡ 0)),

    // leader sends current command to all processes
    ForAll(List(q), (q ∈ KeySet(send1(leader))) ∧ (send1(leader).lookUp(q) ≡ log(leader).lookUp(lastIndex(leader))._1)),


    // UPDATE ========================================================================

    // leader stays active and conserves values
    leader ∈ act1,
    log1(leader) ≡ log(leader),

    // all nodes keep the same lastIndex
    ForAll(List(p), lastIndex1(p) ≡ lastIndex(p)),

    // if active process receives msg from leader,
    // update log and stay active
    ForAll(List (p),
      ((p ∈ act) ∧ (Size(mbox1(p)) > 0)) ==>
        ((log1(p) ≡ log(p).updated(lastIndex(p), Tuple(mbox1(p).lookUp(leader), False())))
         ∧ (p ∈ act1))
    ),

    // otherwise, becomes inactive, and conserves values
    ForAll(List (p), (p ∉ act) ==> ((p ∉ act1) ∧ (log1(p) ≡ log(p)))),
    ForAll(List (p), ((p ∈ act) ∧ (Size(mbox1(p)) ≡ 0)) ==> ((p ∉ act1) ∧ (log1(p) ≡ log(p)))),
  )


  /* Invariant Post-Round1
   * - leader is active
   * - if node is active, it has the same command (on lastIndex(p)) as the leader, uncommitted
   * - for every process, the log prior to lastIndex is left unchanged
   */
  val inv1 = And(
    // leader active
    leader ∈ act,

    // all processes share same lastIndex
    ForAll(List(p), lastIndex(p) ≡ lastIndex(leader)),

    // all active processes have same command
    ForAll(List(p),
      (p ∈ act) ==> (log(p).lookUp(lastIndex(p))._1 ≡ log(leader).lookUp(lastIndex(leader))._1)
    ),

    // all processes have the same values in the log (before lastIndex(i))
    ForAll(List(p, i),
      ((IntLit(0) <= i) ∧ (i < lastIndex(leader))) ==> ((i ∈ KeySet(log(p))) ∧ (log(p).lookUp(i) ≡ log(leader).lookUp(i)))),
  )

  test("inv0 ∧ round1 ⇒ inv1") {
    val fs = List(
      axioms(send1, mbox1),
      inv0,
      round1,
      Not(prime(inv1))
    )

    assertUnsat(fs, debug=false, to=60000, onlyAxioms=true, reducer=c1e1)
  }

  // }}}
  // Round 2 {{{

  val send2 = UnInterpretedFct("send", Some(pid ~> FMap(pid, Int)))
  val mbox2 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, Int)))

  val round2 = And(
    act1 ⊆ act,

    // SEND ==========================================================================

    // leader do not send anything
    Size(send2(leader)) ≡ 0,

    // non-leaders send receipt to leader
    ForAll(List(p), ((p ∈ act) ∧ (p ≠ leader)) ==>
        ((leader ∈ KeySet(send2(p))) ∧ (send2(p).lookUp(leader) ≡ IntLit(1)))),

    // non-active nodes do nothing
    ForAll(List(p), (p ∉ act) ==> Size(send2(p)) ≡ 0),


    // UPDATE ======================

    // active processes that aren't the leader stay active
    ForAll(List(p), ((p ∈ act) ∧ (p ≠ leader)) ==> (p ∈ act1)),

    ForAll(List(p), (p ∉ act) ==> (p ∉ act1)),

    // non-leaders keep same log
    ForAll(List(p), (p ≠ leader) ==> (log1(p) ≡ log(p))),

    // all nodes keep same lastIndex
    ForAll(List(p), lastIndex1(p) ≡ lastIndex(p)),

    // if leader receives majority, commits and stays active
    (Size(mbox2(leader)) >= (n / 2)) ==> (
      (log1(leader) ≡ log(leader).updated(lastIndex(leader),
        Tuple((log(leader).lookUp(lastIndex(leader)))._1, True())))
      ∧ (leader ∈ act1)
    ),

    // otherwise, leader no longer active
    // keeps same log
    (Size(mbox2(leader)) < (n / 2)) ==> ((log1(leader) ≡ log(leader)) ∧ (leader ∉ act1)),
  )

  /* Invariant Post-Round2
   * - if leader is active, it has committed the value
   * - if leader is active, a majority of nodes have the same active command as the leader,
   * - other nodes have the same prefix-log (?)
   */
  val inv2_maj = And(
    (leader ∈ act) ==> (act.card > n / 2),
  )

  val inv2_misc = And(
    (leader ∈ act) ==> (log(leader).lookUp(lastIndex(leader))._2 ≡ True()),

    // all processes share same lastIndex
    ForAll(List(p), lastIndex(p) ≡ lastIndex(leader)),

    // active processes have same command as leader
    ForAll (List(p), p ∈ act ==>
        (log(p).lookUp(lastIndex(p))._1 ≡ log(leader).lookUp(lastIndex(leader))._1)
    ),

    ForAll(List(p, i),
      ((IntLit(0) <= i) ∧ (i < lastIndex(leader))) ==> (log(p).lookUp(i) ≡ log(leader).lookUp(i))),
  )

  val inv2 = And(inv2_maj, inv2_misc)

  test("inv1 ∧ round2 ⇒ inv2") {
    val fs_maj = List(
      axioms(send2, mbox2),
      inv1,
      round2,
      Not(prime(inv2_maj))
    )

    val fs_misc = List(
      inv1,
      round2,
      Not(prime(inv2_misc))
    )

    assertUnsat(fs_misc, debug=false, onlyAxioms=true, to=10000, reducer=c1e1)
    assertUnsat(fs_maj, debug=false, onlyAxioms=false, to=60000, reducer=c2e1)
  }

  // }}}
  // Round 3 {{{

  val send3 = UnInterpretedFct("send", Some(pid ~> FMap(pid, Int)))
  val mbox3 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, Int)))

  val round3 = And(
    act1 ⊆ act,

    // SEND ==========================================================================

    // non-leaders do not send anything
    ForAll(List(p), (p ≠ leader) ==> (Size(send3(p)) ≡ 0)),

    // if leader active, leader sends msg to everyone
    (leader ∈ act) ==> ForAll(List(p), send3(leader).lookUp(p) ≡ IntLit(1)),

    // UPDATE ========================================================================

    // if leader active, leader stays active
    (leader ∈ act) ==> (leader ∈ act1),
    // leader keeps same log
    log1(leader) ≡ log(leader),
    // leader keeps same lastIndex
    lastIndex1(leader) ≡ lastIndex(leader),

    // inactive processes remain inactive
    // and keep same values
    ForAll(List(p), (p ∉ act) ==> And(
      p ∉ act1,
      log1(p) ≡ log(p),
      lastIndex1(p) ≡ lastIndex(p),
    )),

    // if active process receives msg from leader:
    // - commit last cmd
    // - stay active
    // - keep same index
    ForAll(List (p),
      ((p ≠ leader) ∧ (p ∈ act) ∧ Not(Size(mbox3(p)) ≡ 0)) ==> And(
        log1(p) ≡ log(p).updated(lastIndex(p), Tuple(log(p).lookUp(lastIndex(p))._1, True())),
        p ∈ act1,
        lastIndex1(p) ≡ lastIndex(p),
    )),

    // otherwise, becomes inactive, and conserves values
    ForAll(List (p),
      ((p ≠ leader) ∧ (p ∈ act) ∧ (Size(mbox3(p)) ≡ 0)) ==> And(
        log1(p) ≡ log(p),
        lastIndex1(p) ≡ lastIndex(p),
        p ∉ act1,
    )),
  )

  /* Invariant Post-Round3
   */
  val inv3 = And(
    // every active process has committed the command
    (leader ∈ act) ==> ForAll(List(p), (p ∈ act) ==> And(
        log(p).lookUp(lastIndex(p))._1 ≡ log(leader).lookUp(lastIndex(leader))._1,
        log(p).lookUp(lastIndex(p))._2 ≡ True()
    )),

    ForAll(List(p), lastIndex(p) ≡ lastIndex(leader))
  )

  ignore("inv2 ∧ round3 ⇒ inv3") {
    val fs = List(
      axioms(send3, mbox3),
      inv2,
      round3,
      Not(prime(inv3))
    )

    val reducer = c1e1
    assertUnsat(fs, debug=false, to=60000, reducer=reducer)
    // val f0 = reduce(c2e1, fs, true, true)
    // getModel(fs, to=60000, reducer=reducer)
  }

  // }}}

}
