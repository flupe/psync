package psync.logic

import psync.formula._
import psync.formula.InlineOps._
import TestCommon._

import org.scalatest._

class MaxLog extends FunSuite {

  // Housekeeping {{{

  val p  = Variable("p").setType(pid)
  val q  = Variable("q").setType(pid)
  val leader = Variable("leader").setType(pid)
  val pi = Variable("pi").setType(FSet(pid))

  // log-related types & uninterpreted functions
  val cmdType  = UnInterpreted("command")
  val logEntry = Product(cmdType, Bool)
  val keyType  = Int
  val logType  = FMap(keyType, logEntry)

  val log  = UnInterpretedFct("log", Some(pid ~> logType))
  val log1 = UnInterpretedFct("log1", Some(pid ~> logType))
  // val lastIndex  = UnInterpretedFct("lastIndex", Some(pid ~> Int))
  // val lastIndex1 = UnInterpretedFct("lastIndex1", Some(pid ~> Int))

  val max = UnInterpretedFct("max", Some(FMap(pid, logType) ~> logType))
  val send = UnInterpretedFct("send", Some(pid ~> FMap(pid, logType)))
  val mbox = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, logType)))

  val S = Variable("S").setType(FMap(pid, logType))
  val k = Variable("k").setType(keyType)

  // }}}
  // Axioms {{{

  def axioms(send: UnInterpretedFct, mbox: UnInterpretedFct) = And(
    ForAll(List(p), p ∈ pi),

    pi.card ≡ n,

    ForAll(List (p), KeySet(mbox(p)) ⊆ pi),
    ForAll(List (p), KeySet(send(p)) ⊆ pi),
    ForAll(List (p), ho(p) ⊆ pi),

    ForAll(List(p), KeySet(mbox(p)).card <= n),
    ForAll(List(p), KeySet(mbox(p)).card >= 0),
    ForAll(List(p), (ho(p)).card <= n),
    ForAll(List(p), (ho(p)).card >= 0),

    ForAll(List(p, q), (q ∈ KeySet(mbox(p))) ≡ ((q ∈ ho(p) ∧ (p ∈ KeySet(send(q)))))),
    ForAll(List(p, q), ((q ∈ ho(p)) ∧ (p ∈ KeySet(send(q)))) ==> (mbox(p).lookUp(q) ≡ send(q).lookUp(p))),
    ForAll(List(p), (Size(send(p)) ≡ 0) ==> (ForAll(List(q), p ∉ KeySet(mbox(q))))),
    ForAll(List(p), (Size(send(p)) ≡ 0) ≡ (ForAll(List(q), q ∉ KeySet(send(q))))),
    ForAll(List(p), (KeySet(mbox(p)) ⊆ ho(p))),
    ForAll(List(p, q), (q ∈ KeySet(mbox(p))) ≡ ((q ∈ ho(p) ∧ (p ∈ KeySet(send(q)))))),
  )

  // }}}

  val maxInvariants = And(
    ForAll(List(S, p), S.isDefinedAt(p) ==> {
      val L = S.lookUp(p)
      val M = max(S)

      ForAll(List(k), Or(
        Not(L.isDefinedAt(k)),
        L.isDefinedAt(k) ∧ Not(L.lookUp(k)._2),
        L.isDefinedAt(k) ∧ M.isDefinedAt(k) ∧ (L.lookUp(k)._1 ≡ M.lookUp(k)._1) ∧ M.lookUp(k)._2,
      ))
    }),

    // if the max_log is defined somewhere, then this value must have come from the input
    ForAll(List(S, k), max(S).isDefinedAt(k) ==> Exists(List(p), And(
      S.isDefinedAt(p),
      S.lookUp(p).isDefinedAt(k),
      max(S).lookUp(k) ≡ S.lookUp(p).lookUp(k)
    )))
  )

  // log invariants
  val preInv = {
    ForAll(List(p, q, k), Or(
      Not(log(p).isDefinedAt(k)),
      Not(log(q).isDefinedAt(k)),
      Not(log(p).lookUp(k)._2),
      Not(log(q).lookUp(k)._2),
      log(p).lookUp(k)._1 ≡ log(q).lookUp(k)._1
    ))
  }

  val round = {
    val sendPhase = ForAll(List(p), And(
      send(p).isDefinedAt(leader),
      send(p).lookUp(leader) ≡ log(p)
    ))

    val updatePhase = ForAll(List(p), And(
      (p ≠ leader) ==> (log1(p) ≡ log(p)),
      (p ≡ leader) ==> (log1(p) ≡ max(mbox(p))),
    ))

    And(sendPhase, updatePhase)
  }

  val postInv = And(
    // leader has a max log
    ForAll(List(p), (p ∈ ho(leader)) ==> And(
      ForAll(List(k), Or(
        Not(log1(p).isDefinedAt(k)),
        Not(log1(p).lookUp(k)._2),
        (log1(p).lookUp(k)._1 ≡ log1(leader).lookUp(k)._1)
      ))
    )),

    ForAll(List(p, q, k), Or(
      Not(log1(p).isDefinedAt(k)),
      Not(log1(q).isDefinedAt(k)),
      Not(log1(p).lookUp(k)._2),
      Not(log1(q).lookUp(k)._2),
      log1(p).lookUp(k)._1 ≡ log1(q).lookUp(k)._1
    ))
  )

  test("compute max log") {
    val fs = List(
      axioms(send, mbox),
      preInv,
      maxInvariants,
      round,
      Not(postInv)
    )

    assertUnsat(fs, to = 200000, onlyAxioms=true)
  }

}
