import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Check {
  
  @funEq
  def check(l: List[BigInt]): Boolean = {
    Student.f(l) == Model.f(l)/* because {
      if(l.isEmpty) true
      else size_check(l.tail)
    }*/
  }.holds

}
  