package psync.logic

import psync.formula._
import psync.formula.InlineOps._
import TestCommon._

import org.scalatest._

class Zab extends FunSuite {

  // DEFINITIONS

  // Housekeeping {{{
  val p  = Variable("p").setType(pid)
  val q  = Variable("q").setType(pid)
  val coord = Variable("coord").setType(pid)
  val pi = Variable("pi").setType(FSet(pid))
  val leader = Variable("leader").setType(FMap(pid, pid))
  val leader1 = Variable("leader").setType(FMap(pid, pid))
  var act  = Variable("act").setType(FSet(pid))
  var act1 = Variable("act1").setType(FSet(pid))

  // log-related types & uninterpreted functions
  val cmdType  = UnInterpreted("command")
  val logEntry = Product(cmdType, Bool)
  val keyType  = Int
  val logType  = FMap(keyType, logEntry)

  val log  = UnInterpretedFct("log", Some(pid ~> logType))
  val log1 = UnInterpretedFct("log1", Some(pid ~> logType))

  def lI (p : Formula) : Formula = Size(log(p))
  def lI1 (p : Formula) : Formula = Size(log1(p))

  val max_log = UnInterpretedFct("max_log", Some(FMap(pid, logType) ~> logType))
  // val send = UnInterpretedFct("send", Some(pid ~> FMap(pid, logType)))
  // val mbox = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, logType)))

  // quantified variables
  val S   = Variable("S").setType(FMap(pid, logType))
  val k   = Variable("k").setType(keyType)
  val i   = Variable("i").setType(keyType)
  val j   = Variable("j").setType(keyType)
  val cmd = Variable("cmd").setType(cmdType)


  def prime(f: Formula) : Formula = {
    val symMap = Map[Symbol, Symbol](
      log       -> log1,
    )

    val varMap = Map[Variable, Variable](
      leader    -> leader1,
    )

    val f1 = FormulaUtils.mapSymbol(x => symMap.getOrElse(x, x), f)
    FormulaUtils.alpha(varMap, f1)
  }
  // }}}
  // Axioms {{{

  // MBOX AXIOMS

  def axioms(send: UnInterpretedFct, mbox: UnInterpretedFct) = And(
    ForAll(List(p), p ∈ pi),

    pi.card ≡ n,

    ForAll(List(p), KeySet(mbox(p)) ⊆ pi),
    ForAll(List(p), KeySet(send(p)) ⊆ pi),
    ForAll(List(p), ho(p) ⊆ pi),


    ForAll(List(p), KeySet(mbox(p)).card <= n),
    ForAll(List(p), KeySet(mbox(p)).card >= 0),

    ForAll(List(p), (ho(p)).card <= n),
    ForAll(List(p), (ho(p)).card >= 0),

    ForAll(List(p, q), mbox(p).isDefinedAt(q) ≡ ((q ∈ ho(p)) ∧ send(q).isDefinedAt(p))),
    ForAll(List(p, q), ((q ∈ ho(p)) ∧ send(q).isDefinedAt(p)) ==> (mbox(p).lookUp(q) ≡ send(q).lookUp(p))),
    ForAll(List(p, q), (mbox(p).isDefinedAt(q)) ≡ ((q ∈ ho(p) ∧ send(q).isDefinedAt(p)))),
    ForAll(List(p), (Size(send(p)) ≡ 0) ==> (ForAll(List(q), Not(mbox(q).isDefinedAt(p))))),
    ForAll(List(p), (KeySet(mbox(p)) ⊆ ho(p))),
  )


  // LOG AXIOMS

  val logAxioms = And(
    ForAll(List(p, i), ((IntLit(1) <= i) ∧ (i <= lI(p)) ==> log(p).isDefinedAt(i)))
  )

  // MAX_LOG AXIOMS

  val maxLogAxioms = And(
    ForAll(List(S, p), S.isDefinedAt(p) ==> {
      val L = S.lookUp(p)
      val M = max_log(S)

      ForAll(List(k), Or(
        Not(L.isDefinedAt(k)),
        L.isDefinedAt(k) ∧ Not(L.lookUp(k)._2),
        L.isDefinedAt(k) ∧ M.isDefinedAt(k) ∧ (L.lookUp(k)._1 ≡ M.lookUp(k)._1) ∧ M.lookUp(k)._2,
      ))
    }),

    // if the max_log is defined somewhere, then this value must have come from the input
    ForAll(List(S, k), max_log(S).isDefinedAt(k) ==> Exists(List(p), And(
      S.isDefinedAt(p),
      S.lookUp(p).isDefinedAt(k),
      max_log(S).lookUp(k) ≡ S.lookUp(p).lookUp(k)
    )))
  )

  // }}}
  // Invariants {{{

  // nodes agree on committed values
  val agreement = And(
    ForAll(List(p, q, k), Or(
      Not(log(p).isDefinedAt(k)),
      Not(log(q).isDefinedAt(k)),
      Not(log(p).lookUp(k)._2),
      Not(log(q).lookUp(k)._2),
      log(p).lookUp(k)._1 ≡ log(q).lookUp(k)._1
    )),

    // Every committed value in some log is shared by a majority
    // ForAll(List(p, k), (log(p).isDefinedAt(k) ∧ log(p).lookUp(k)._2) ==> 
    //     (Comprehension(List(q),
    //       (log(q).isDefinedAt(k) ∧ (log(q).lookUp(k)._1 ≡ log(p).lookUp(k)._1))
    //     ).card > n / 2))
  )

  // committed values never change
  val irrevocability = ForAll(List(p, k), (log(p).isDefinedAt(k) ∧ log(p).lookUp(k)._2) ==> And(
    log1(p).isDefinedAt(k),
    log1(p).lookUp(k)._2,
    log1(p).lookUp(k)._1 ≡ log(p).lookUp(k)._1,
  ))

  // }}}
  // Round 1: New Ballot {{{

  val send1 = UnInterpretedFct("send", Some(pid ~> FMap(pid, pid)))
  val mbox1 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, pid)))
  
  val newBallot = {
    val sendCond = (p ≡ coord)

    var sendPhase = ForAll(List(p), And(
      // coord sends pid
      sendCond ==> ForAll(List(q), And(
        send1(p).isDefinedAt(q),
        send1(p).lookUp(q) ≡ p,
      )),

      // others send nothing
      Not(sendCond) ==> (Size(send1(p)) ≡ 0)
    ))

    val updatePhase = ForAll(List(p), And(
      // coord does nothing
      (p ≡ coord)  ==> And(
        log1(p) ≡ log(p),
        leader1.isDefinedAt(p),
        leader1.lookUp(p) ≡ p
      ),

      // others pick leader
      ((p ≠ coord) ∧ (Size(mbox1(p)) > 0))  ==> And(
        log1(p) ≡ log(p),
        leader1.isDefinedAt(p),
        leader1.lookUp(p) ∈ KeySet(mbox1(p)) // we are cheating here
      ),

      // others do nothing
      ((p ≠ coord) ∧ (Size(mbox1(p)) ≡ 0))  ==> And(
        log1(p) ≡ log(p),
        Not(leader1.isDefinedAt(p))
      ),
    ))

    And(sendPhase, updatePhase)
  }

  // }}}
  // Round 2: Acknowledge Ballot {{{

  val send2 = UnInterpretedFct("send", Some(pid ~> FMap(pid, logType)))
  val mbox2 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, logType)))

  val ackBallot = {
    val sendCond = leader.isDefinedAt(p)

    var sendPhase = ForAll(List(p), And(
      // everyone sends log to their leader
      sendCond ==> And(
        send2(p).isDefinedAt(leader.lookUp(p)),
        send2(p).lookUp(leader.lookUp(p)) ≡ log(p),
        ForAll(List(q), (q ≠ leader.lookUp(p)) ==> Not(send2(p).isDefinedAt(q))),
      ),

      // others send nothing
      Not(sendCond) ==> (Size(send2(p)) ≡ 0)
    ))

    val updateCond = ((p ≡ coord))

    val updatePhase = ForAll(List(p), And(
      // coord with quorum computes max log
      updateCond ==> And(
        log1(p) ≡ max_log(mbox2(p)),
      ),

      // others do nothing
      Not(updateCond) ==> And(
        log1(p) ≡ log(p),
      )
    ))

    And(sendPhase, updatePhase)
  }

  // }}}
  // Round 3: New Leader {{{

  val send3 = UnInterpretedFct("send", Some(pid ~> FMap(pid, logType)))
  val mbox3 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, logType)))

  val newLeader = {
    // TODO: take care of inactive leader (without quorum)
    val sendCond = p ≡ coord

    var sendPhase = ForAll(List(p), And(
      // leader sends its log to everyone
      sendCond ==> ForAll(List(q), And(
        send2(p).isDefinedAt(q),
        send2(p).lookUp(q) ≡ log(p),
      )),

      // others send nothing
      Not(sendCond) ==> (Size(send2(p)) ≡ 0)
    ))

    val updateCond = (p ≠ coord) ∧ (mbox3(p).isDefinedAt(leader.lookUp(p)))

    val updatePhase = ForAll(List(p), And(
      // coord with quorum computes max log
      updateCond ==> And(
        log1(p) ≡ mbox3(p).lookUp(leader.lookUp(p)),
      ),

      // others do nothing
      Not(updateCond) ==> And(
        log1(p) ≡ log(p),
      )
    ))

    And(sendPhase, updatePhase)
  }

  // }}}
  // BROADCAST {{{

  // Round 1 {{{

  val send4 = UnInterpretedFct("send", Some(pid ~> FMap(pid, cmdType)))
  val mbox4 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, cmdType)))

  val round1 = {
    val sendPhase = ForAll(List(p), And(
      (p ≡ coord) ==> ForAll(List(q), And(
        send4(p).isDefinedAt(q),
        send4(p).lookUp(q) ≡ cmd
      )),
      (p ≠ coord) ==> (Size(send4(p)) ≡ 0) 
    ))

    val updatePhase = ForAll(List(p), And(
      (p ≡ coord) ∧ (p ∈ act) ==> And(
        p ∈ act1,
        log1(p) ≡ log(p).updated(lI(p) + IntLit(1), Tuple(cmd, False()))
      ),

      (p ≠ coord) ∧ (p ∈ act) ∧ (mbox4(p).isDefinedAt(coord)) ==> And(
        p ∈ act1,
        log1(p) ≡ log(p).updated(lI(p) + IntLit(1), Tuple(mbox4(p).lookUp(coord), False()))
      ),

      (p ∉ act) ∨ Not(mbox4(p).isDefinedAt(coord)) ==> And(
        p ∉ act1,
        log1(p) ≡ log(p)
      )
    ))

    And(sendPhase, updatePhase)
  }

  // }}}
  // Round 2 {{{

  // TODO: add invariant that every committed value in log must have a majority around it
  //       therefore we prove that the leader's log is the longest
  val send5 = UnInterpretedFct("send", Some(pid ~> FMap(pid, Int)))
  val mbox5 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, Int)))

  val round2 = {

    val sendPhase = ForAll(List(p), And(
      (p ∈ act) ==> And(
        send5(p).isDefinedAt(coord),
        send5(p).lookUp(coord) ≡ IntLit(0)
      ),

      (p ∉ act) ==> And(
        Size(send5(p)) ≡ 0
      )
    ))

    val updatePhase = ForAll(List(p), And(
      (p ≡ coord) ∧ (p ∈ act) ∧ (Size(mbox5(coord)) > (n / 2)) ==> And(
        p ∈ act1,
        log1(p) ≡ log(p).updated(lI(p), Tuple(
          log(p).lookUp(lI(p))._1,
          True()
        ))
      ),

      (p ≡ coord) ∧ (p ∈ act) ∧ (Size(mbox5(coord)) <= (n / 2)) ==> And(
        p ∉ act1,
        log1(p) ≡ log(p)
      ),

      (p ≠ coord) ∧ (p ∈ act) ==> And(
        p ∈ act1,
        log1(p) ≡ log(p)
      ),

      (p ∉ act) ==> And(
        p ∉ act1,
        log1(p) ≡ log(p)
      )
    ))

    And(sendPhase, updatePhase)
  }

  // }}}

  // }}}

  // TESTS

  // Outer algorithm agreement {{{
  test("round 1 preserves agreement & irrevocability") {
    assertUnsat(List(
      agreement,
      logAxioms,
      newBallot,
      Not(And(prime(agreement), irrevocability))
    ), onlyAxioms = true)
  }

  ignore("round 2 preserves agreement") {
    assertUnsat(List(
      axioms(send2, mbox2),
      maxLogAxioms,
      agreement,
      ackBallot,
      Not(And(prime(agreement)))
    ), to=120000, onlyAxioms = true)
  }

  ignore("round 3 preserves agreement") {
    assertUnsat(List(
      axioms(send3, mbox3),
      agreement,
      newLeader,
      Not(prime(agreement))
    ), onlyAxioms = true)
  }
  // }}}
  // Broadcast algorithm agreement {{{
  ignore("BCAST round 1 preserves agreement") {
    assertUnsat(List(
      axioms(send4, mbox4),
      agreement,
      ForAll(List(p), (p ∈ act) ==> (log(p) ≡ log(coord))),
      logAxioms,
      round1,
      Not(And(
        prime(agreement),
        ForAll(List(p, q), ((p ∈ act1) ∧ (q ∈ act1)) ==>
            log1(p).lookUp(lI1(p))._1 ≡ log1(q).lookUp(lI1(q))._1)
      ))
    ), onlyAxioms = true)
  }

  ignore("BCAST round 2 preserves agreement") {
    assertUnsat(List(
      axioms(send5, mbox5),
      agreement,
      logAxioms,
      ForAll(List(p, q), ((q ∈ act) ∧ (p ∈ act)) ==> ((lI(p) ≡ lI(q)) ∧ (log(p).lookUp(lI(p))._1 ≡ log(q).lookUp(lI(q))._1))),
      round2,
      Not(prime(agreement))
    ), to=60000, onlyAxioms = true)
  }
  // }}}
}
