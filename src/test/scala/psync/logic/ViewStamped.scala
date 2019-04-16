package psync.logic

import psync.formula._
import psync.formula.InlineOps._
import TestCommon._

import org.scalatest._

class ViewStamped extends FunSuite {

  // DEFINITIONS

  // Housekeeping {{{

  // log-related types & uninterpreted functions
  val cmdType   = UnInterpreted("command")
  val epochType = Int
  val logEntry = Product(cmdType, Bool, epochType)
  val keyType  = Int
  val logType  = FMap(keyType, logEntry)

  val p  = Variable("p").setType(pid)
  val q  = Variable("q").setType(pid)
  val coord = Variable("coord").setType(pid)
  val epoch = Variable("epoch").setType(epochType)
  val pi = Variable("pi").setType(FSet(pid))

  var act  = Variable("act").setType(FSet(pid))
  var act1 = Variable("act1").setType(FSet(pid))
  var act2 = Variable("act2").setType(FSet(pid))

  val log  = UnInterpretedFct("log", Some(pid ~> logType))
  val log1 = UnInterpretedFct("log1", Some(pid ~> logType))
  val log2 = UnInterpretedFct("log2", Some(pid ~> logType))

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

  // leader local variables
  val cmd = Variable("cmd").setType(cmdType)
  val has_cmd = Variable("has_cmd").setType(Bool)

  def prime(f: Formula) : Formula = {
    val symMap = Map[Symbol, Symbol](
      log       -> log1,
      log1      -> log2,
    )

    val varMap = Map[Variable, Variable](
      act       -> act1,
      act1      -> act2,
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
    ForAll(List(p, i), (((IntLit(1) <= i) ∧ (i <= lI(p))) ≡ log(p).isDefinedAt(i)))
  )

  // MAX_LOG AXIOMS

  val maxLogAxioms = And(
    ForAll(List(S, p), S.isDefinedAt(p) ==> {
      val L = S.lookUp(p)
      val M = max_log(S)

      // If the at some position in the input log, a value is committed, then it is kept in the max_log
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
    ))),

    ForAll(List(S, k), {
      val M = max_log(S)

      // If for some position in the logs, no command is committed, we take the max
      ForAll(List(p), Or(Not(S.has(p)), Not(S.at(p).has(k)), Not(S.at(p).at(k)._2))) ==> (
        ForAll(List(p), And(S.has(p), S.at(p).has(k)) ==> (S.at(p).at(k)._3 <= M.at(k)._3))
      )
    }),
  )

  // }}}
  // Invariants {{{

  val initialState = And(
    // empty logs for everyone
    ForAll(List(p), log(p).size ≡ IntLit(0))
  )

  val logInv = And(
    ForAll(List(p, q, k), And(log(p).has(k), log(q).has(k), log(p).at(k)._3 ≡ log(q).at(k)._3) ==>
      log(p).at(k)._1 ≡ log(q).at(k)._1
    ),

    // there cannot be two different committed commands at the same position in the logs
    ForAll(List(p, q, k), And(
      log(p).isDefinedAt(k),
      log(q).isDefinedAt(k),
      log(p).lookUp(k)._2,
      log(q).lookUp(k)._2,
    ) ==> (log(p).lookUp(k)._1 ≡ log(q).lookUp(k)._1)),

    // if there is a committed command, then every different command under the same position has a lower epoch
    ForAll(List(p, k), And(
        log(p).isDefinedAt(k),
        log(p).lookUp(k)._2,
      ) ==> ForAll(List(q),
        (log(q).isDefinedAt(k) ∧ (log(q).lookUp(k)._1 ≠ log(p).lookUp(k)._1))
          ==> (log(q).lookUp(k)._3 < log(p).lookUp(k)._3)
    ))
  )

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
    ForAll(List(p, k), (log(p).has(k) ∧ log(p).at(k)._2) ==> 
        (Comprehension(List(q),
          (log(q).has(k) ∧ (log(q).at(k)._1 ≡ log(p).at(k)._1))
        ).card > n / 2))
  )

  // committed values never change
  val irrevocability = ForAll(List(p, k), (log(p).isDefinedAt(k) ∧ log(p).lookUp(k)._2) ==> And(
    log1(p).isDefinedAt(k),
    log1(p).lookUp(k)._2,
    log1(p).lookUp(k)._1 ≡ log(p).lookUp(k)._1,
  ))

  // }}}
  // Round 1: Acknowledge Ballot {{{

  val send2 = UnInterpretedFct("send", Some(pid ~> FMap(pid, logType)))
  val mbox2 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, logType)))

  val ackBallot = {
    var sendPhase = ForAll(List(p), And(
      // everyone sends log to the coordinator
      send2(p).isDefinedAt(coord),
      send2(p).lookUp(coord) ≡ log(p),
      ForAll(List(q), (q ≠ coord) ==> Not(send2(p).isDefinedAt(q))),
    ))

    val updateCond = (p ≡ coord)

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
  // Round 2: New Leader {{{

  val send3 = UnInterpretedFct("send", Some(pid ~> FMap(pid, logType)))
  val mbox3 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, logType)))

  val newLeader = {
    // TODO: take care of inactive leader (without quorum)
    val sendCond = (p ≡ coord)

    var sendPhase = ForAll(List(p), And(
      // leader sends its log to everyone
      sendCond ==> ForAll(List(q), And(
        send2(p).isDefinedAt(q),
        send2(p).lookUp(q) ≡ log(p),
      )),

      // others send nothing
      Not(sendCond) ==> (Size(send2(p)) ≡ 0)
    ))

    val updateCond = (p ≠ coord) ∧ (mbox3(p).isDefinedAt(coord))

    val updatePhase = ForAll(List(p), And(
      // coord with quorum computes max log
      updateCond ==> And(
        log1(p) ≡ mbox3(p).lookUp(coord),
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
  // Round 3 {{{

  val send6 = UnInterpretedFct("send", Some(pid ~> FMap(pid, Int)))
  val mbox6 = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, Int)))

  val round3 = {

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
        // TODO: We get usr command
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

  test("initial state implies Agreement invariant") {
    assertUnsat(List(initialState, Not(agreement)), onlyAxioms = true)
  }

  test("initial state implies Log invariant") {
    assertUnsat(List(initialState, Not(logInv)), onlyAxioms = true)
  }

  test("Log invariant is preserved through round1") {
    assertUnsat(List(
      logInv,
      axioms(send2, mbox2),
      maxLogAxioms,
      ackBallot,
      Not(prime(logInv))
    ), onlyAxioms = true)
  }

  // Outer algorithm agreement {{{
  ignore("round 1 preserves agreement") {
    assertUnsat(List(
      logInv,
      axioms(send2, mbox2),
      maxLogAxioms,
      agreement,
      ackBallot,
      Not(prime(agreement))
    ), to=60000, onlyAxioms = true)
  }

  // TODO: is this reasonnable?
  // I fear reusing ho/send/mbox does not work as intended
  test("round 2 preserves agreement") {
    assertUnsat(List(
      axioms(send2, mbox2),
      axioms(send3, mbox3),
      agreement,
      ackBallot,
      prime(newLeader),
      Not(prime(prime(agreement)))
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
