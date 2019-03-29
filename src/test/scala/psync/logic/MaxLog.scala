package psync.logic

import psync.formula._
import psync.formula.InlineOps._
import TestCommon._

import org.scalatest._

class MaxLog extends FunSuite {

  // Housekeeping {{{

  val p  = Variable("p").setType(pid)
  val q  = Variable("q").setType(pid)
  val leader  = Variable("leader").setType(pid)
  val pi = Variable("pi").setType(FSet(pid))
  val value = UnInterpretedFct("value", Some(pid ~> Int))
  val value1 = UnInterpretedFct("value1", Some(pid ~> Int))
  val max = UnInterpretedFct("max", Some(FMap(pid, Int) ~> Int))
  val send = UnInterpretedFct("send", Some(pid ~> FMap(pid, Int)))
  val mbox = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, Int)))
  val S = Variable("S").setType(FMap(pid, Int))

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
    ForAll(List(p, S), S.isDefinedAt(p) ==> (S.lookUp(p) <= max(S)))
  )

  val round = {
    val sendPhase = ForAll(List(p), And(
      send(p).isDefinedAt(leader),
      send(p).lookUp(leader) ≡ value(p)
    ))

    val updatePhase = ForAll(List(p), And(
      (p ≠ leader) ==> (value1(p) ≡ value(p)),
      (p ≡ leader) ==> (value1(p) ≡ max(mbox(p)))
    ))

    And(sendPhase, updatePhase)
  }

  val postInv = And(
    ForAll(List(p), (p ∈ ho(leader)) ==> (value1(p) <= value1(leader)))
  )

  test("compute max") {
    val fs = List(
      axioms(send, mbox),
      maxInvariants,
      round,
      Not(postInv)
    )

    assertUnsat(fs, to = 60000, onlyAxioms=true)
  }

}
