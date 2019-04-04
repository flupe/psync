package psync.logic

import psync.formula._
import psync.formula.InlineOps._
import TestCommon._

import org.scalatest._

class Zab extends FunSuite {

  // Housekeeping {{{
  val p  = Variable("p").setType(pid)
  val q  = Variable("q").setType(pid)
  val coord = Variable("coord").setType(pid)
  val pi = Variable("pi").setType(FSet(pid))
  val leader = Variable("leader").setType(FMap(pid, pid))
  val leader1 = Variable("leader").setType(FMap(pid, pid))

  // log-related types & uninterpreted functions
  val cmdType  = UnInterpreted("command")
  val logEntry = Product(cmdType, Bool)
  val keyType  = Int
  val logType  = FMap(keyType, logEntry)

  val log  = UnInterpretedFct("log", Some(pid ~> logType))
  val log1 = UnInterpretedFct("log1", Some(pid ~> logType))

  val lI = UnInterpretedFct("lastIndex", Some(pid ~> keyType))
  val lI1 = UnInterpretedFct("lastIndex1", Some(pid ~> keyType))

  val max_log = UnInterpretedFct("max_log", Some(FMap(pid, logType) ~> logType))
  // val send = UnInterpretedFct("send", Some(pid ~> FMap(pid, logType)))
  // val mbox = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, logType)))

  // quantified variables
  val S = Variable("S").setType(FMap(pid, logType))
  val k = Variable("k").setType(keyType)
  val i = Variable("i").setType(keyType)
  val j = Variable("j").setType(keyType)


  def prime(f: Formula) : Formula = {
    val symMap = Map[Symbol, Symbol](
      log       -> log1,
      lI        -> lI1
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
    ForAll(List(p), lI(p) ≡ Size(log(p))),
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
  val agreement = ForAll(List(p, q, k), Or(
    Not(log(p).isDefinedAt(k)),
    Not(log(q).isDefinedAt(k)),
    Not(log(p).lookUp(k)._2),
    Not(log(q).lookUp(k)._2),
    log(p).lookUp(k)._1 ≡ log(q).lookUp(k)._1
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

  test("round 1 preserves agreement") {
    assertUnsat(List(
      agreement,
      newBallot,
      Not(prime(agreement))
    ), onlyAxioms = true)
  }

  test("round 2 preserves agreement") {
    assertUnsat(List(
      axioms(send2, mbox2),
      maxLogAxioms,
      agreement,
      ackBallot,
      Not(prime(agreement))
    ), onlyAxioms = true)
  }
}
