package round.predicate

import round._
import Algorithm._
import round.runtime._
import round.utils.Timer

import io.netty.buffer.ByteBuf
import io.netty.channel._
import io.netty.channel.socket._
import io.netty.util.{TimerTask, Timeout}

import round.utils.Logger
import round.utils.LogLevel._
  
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.Semaphore


/* Same principle as ToPredicate but allows more concurrency in msg reception. */
class ToPredicateFineGrained(
      grp: Group,
      instance: Short,
      channel: Channel,
      dispatcher: InstanceDispatcher,
      proc: Process,
      options: Map[String, String] = Map.empty
    ) extends ToPredicate(grp, instance, channel, dispatcher, proc, options)
{

  private val from2 = Array.ofDim[AtomicBoolean](n)
  for (i <- 0 until n) from2(i) = new AtomicBoolean(false)
  private var _received2 = new AtomicInteger(0)
  override def received = _received2.intValue
  override def resetReceived { _received2.set(0) }

  private val maxPermits = 1000
  private val lock2 = new Semaphore(1000, true)

  override val tt = new TimerTask {
    def run(to: Timeout) {
      if (active) {
        if (changed) {
          changed = false
        } else {
          Logger("Predicate", Debug, "delivering because of timeout")
          deliver
          changed = false
        }
        timeout = Timer.newTimeout(this, defaultTO)
      }
    }
  }

  override protected def clear {
    super.clear
    for (i <- 0 until n) {
      from2(i).set(false)
    }
  }
  
  //assume the thread has one permit
  override protected def deliver {
    lock2.release //need to release to avoid deadlock
    lock2.acquire(maxPermits)
    //need to test again the delivery condition
    if (_received2.intValue >= expected) {
      super.deliver
      expected = proc.expectedNbrMessages
    }
    lock2.release(maxPermits -1)
  }

  override protected def normalReceive(pkt: DatagramPacket) {
    val id = grp.inetToId(pkt.sender)
    //protect from duplicate packet
    if (!from2(id).getAndSet(true)) {
      val r = _received2.getAndIncrement()
      messages(r) = pkt
      if (r >= expected) {
        deliver
      }
    }
    changed = true
  }

  override def receive(pkt: DatagramPacket) {
    val tag = Message.getTag(pkt.content)
    val round = tag.roundNbr
    lock2.acquire
    try {
      if(round == currentRound) {
        normalReceive(pkt)
      } else if (round > currentRound) {
        //we are late, need to catch up
        for (i <- currentRound until round) {
          deliver //TODO skip the sending ?
        }
        //then back to normal
        normalReceive(pkt)
      } else {
        //late message, drop it
      }
    } finally {
      lock2.release
    }
  }

}