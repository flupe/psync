package psync.runtime.server

import psync.runtime._
import psync.ProcessID
import io.netty.channel.Channel
import io.netty.channel.socket.DatagramPacket
import io.netty.buffer.ByteBuf
import io.netty.channel.EventLoopGroup
import io.netty.channel.nio.NioEventLoopGroup
import io.netty.channel.epoll.EpollEventLoopGroup
import io.netty.channel.oio.OioEventLoopGroup

abstract class PacketServer(
    executor: java.util.concurrent.Executor,
    port: Int,
    initGroup: Group,
    _defaultHandler: Message => Unit, //defaultHandler is responsible for releasing the ByteBuf payload
    options: RuntimeOptions)
{

  protected val directory = new Directory(initGroup)

  def group = directory.group
  /** The group should not be changed while instances are running */
  def group_=(grp: Group) {
    directory.group = grp
  }

  protected[psync] def defaultHandler(pkt: DatagramPacket) {
    val msg = new Message(pkt, directory.group)
    _defaultHandler(msg)
  }

  protected def evtGroup: EventLoopGroup = options.group match {
    case NetworkGroup.NIO => new NioEventLoopGroup(0, executor)
    case NetworkGroup.OIO => new OioEventLoopGroup(0, executor)
    case NetworkGroup.EPOLL => new EpollEventLoopGroup(0, executor)
  }


  protected[psync] val dispatcher = new Dispatcher(options.dispatch)
  protected[psync] def addToDispatch(inst: Short, handler: InstHandler) {
    dispatcher.add(inst, handler)
  }
  protected[psync] def removeFromDispatch(instance: Short) {
    dispatcher.remove(instance)
  }

  def close: Unit

  def start: Unit

  def send(to: ProcessID, buf: ByteBuf): Unit

}
