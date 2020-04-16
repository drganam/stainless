import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof._

object TraceInductTest {

  def size(l: IList): BigInt = (l match {
    case INil()      => BigInt(0)
    case ICons(_, t) => 1 + size(t)
  }) //ensuring(res => res >= 0)

  @traceInduct("")
  def nonNegSize(l: IList): Boolean = {
    size(l) >= 0
  }.holds
}

