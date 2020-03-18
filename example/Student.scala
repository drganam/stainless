import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Student {

  def f(l: List[BigInt]): BigInt = { 
    if(!l.isEmpty) BigInt(1) + f(l.tail) 
    else BigInt(0)
  }

}
