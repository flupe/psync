package example

import round._
import round.runtime._
import round.macros.Macros._

//http://link.springer.com/chapter/10.1007%2F11535294_5
class KSetEarlyStopping(t: Int, k: Int) extends Algorithm[ConsensusIO] {
  
  import VarHelper._
  import SpecHelper._

  
  val est = new LocalVariable[Int](0)
  val canDecide = new LocalVariable[Boolean](false)
  val lastNb = new LocalVariable[Int](0)
  //
  val callback = new LocalVariable[ConsensusIO](null)

  val spec = TrivialSpec

  def process = p(new Process[ConsensusIO]{

    def init(io: ConsensusIO) {
      canDecide <~ false
      lastNb <~ n
      est <~ io.initialValue
      callback <~ io
    }

    val rounds = Array[Round](
      rnd(new Round{
      
        type A = (Int, Boolean)

        def send: Set[((Int, Boolean),ProcessID)] = {
          broadcast( (est: Int) -> (canDecide: Boolean) )
        }

        def update(mailbox: Set[((Int, Boolean), ProcessID)]) {
          val currNb = mailbox.size
          if (r > t/k || canDecide) {
            callback.decide(est)
            terminate
          } else {
            est <~ mailbox.map(_._1._1).min
            canDecide <~ (mailbox.exists(_._1._2) || lastNb - currNb < k)
            lastNb <~ currNb
          }
        }

      })
    )
  })
}

object KSetESRunner extends round.utils.DefaultOptions {
  
  var id = -1
  newOption("-id", dzufferey.arg.Int( i => id = i), "the replica ID")

  var k = 2
  newOption("-k", dzufferey.arg.Int( i => k = i), "k (default = 2)")

  var t = 2
  newOption("-t", dzufferey.arg.Int( i => k = i), "t (default = 2)")

  var confFile = "src/test/resources/3replicas-conf.xml"
  newOption("--conf", dzufferey.arg.String(str => confFile = str ), "config file")
  
  val usage = "..."
  
  var rt: RunTime[ConsensusIO] = null

  def defaultHandler(msg: Message) {
    msg.release
  }
  
  def main(args: Array[java.lang.String]) {
    apply(args)
    val alg = new KSetEarlyStopping(t, k)
    rt = new RunTime(alg)
    rt.startService(defaultHandler(_), confFile, Map("id" -> id.toString))

    import scala.util.Random
    val init = Random.nextInt
    val io = new ConsensusIO {
      val initialValue = init
      def decide(value: Int) {
        Console.println("replica " + id + " decided " + value)
      }
    }
    Thread.sleep(100)
    Console.println("replica " + id + " starting with " + init)
    rt.startInstance(0, io)
  }
  
  Runtime.getRuntime().addShutdownHook(
    new Thread() {
      override def run() {
        rt.shutdown
      }
    }
  )
}
