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
  // val send = UnInterpretedFct("send", Some(pid ~> Product(payloadType, FSet(pid))))
  val mbox = UnInterpretedFct("mbox", Some(pid ~> FMap(pid, commandType)))

  val axioms = And(
    // π is the set of all processes
    ForAll(List (p), (p ∈ π)),

    // all processes in ho are in the keyset of the mbox
    // and the converse is true (keyset of send)
    ForAll(List (p, q),
      (q ∈ ho(p)) ==> ((q ∈ KeySet(mbox(p))) ∧ (p ∈ KeySet(send(q))))),

    ForAll(List (p, q),
      (q ∈ ho(p)) ==> (IsDefinedAt(mbox(p), q) ∧ IsDefinedAt(send(q), p))),

    // process p receives from q what q sent to p
    ForAll(List (p, q), (q ∈ ho(p)) ==> (LookUp(mbox(p), q) ≡ LookUp(send(q), p))),
  )

  // invariant pre-broadcast
  val inv0 = And(
    leader ∈ act,
    ForAll(List(p), lastIndex(p) ≡ lastIndex(leader))
  )


  // Inner algorithm, round 1
  val round1 = And(
    act1 ⊆ act,

    // SEND ========================

    // non-leaders do not send anything
    ForAll(List (p), (p ≠ leader) ==> (Size(send(p)) ≡ 0)),

    // leader sends current cmd
    ForAll(List (p), (p ≡ leader) ==>
      ForAll(List(q),
        send(p).lookUp(q) ≡ log(p).lookUp(lastIndex(p))._1)
    ),


    // UPDATE ======================

    // leader stays active and conserves values
    (leader ∈ act1),
    (log1(leader) ≡ log(leader)),

    // all nodes keep same lastIndex
    ForAll(List(p), lastIndex1(p) ≡ lastIndex(p)),

    // if active non leader process receives msg
    // update log and stay active
    ForAll(List (p),
      ((p ∈ act) ∧ (Size(mbox(p)) > 0)) ==>
        (Exists(List(q),
          log1(p) ≡ log(p).updated(lastIndex(p), Tuple(mbox(p).lookUp(q), False()))
        ) ∧ (p ∈ act1))
    ),

    // otherwise, becomes inactive, and conserves values
    ForAll(List (p), (p ∉ act) ==> ((p ∉ act1) ∧ (log1(p) ≡ log(p)))),
    ForAll(List (p), ((p ∈ act) ∧ (Size(mbox(p)) ≡ 0)) ==>
        ((p ∉ act1) ∧ (log1(p) ≡ log(p)))),

  )

  // invariant post-round1
  val inv1 = And(
    ForAll(List(p),
      (p ∈ act1) ==> (log1(p).lookUp(lastIndex1(p))._1 ≡ log(leader).lookUp(lastIndex(leader))._1)
    )
  )

  test("inv0 ∧ round1 ⇒ inv1") {
    val fs = List(
      axioms,
      round1,
      Not(inv1)
    )

    assertUnsat(fs, to=60000, reducer=c2e1)
    // getModel(fs, reducer=c2e1)
  }

}
