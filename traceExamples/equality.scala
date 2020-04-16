import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object Examples {


//////////////////////////////////////////////////////////////////////////////////////////////////////////

  def size1(l: List[BigInt]): BigInt = { 
    //val e = 2
    if(!l.isEmpty) BigInt(1) + size1(l.tail) 
    else BigInt(0)
  }//ensuring(res => res == size2(l))

  def size2(l: List[BigInt]): BigInt = {
    l.size
  }//ensuring(res => res == size1(l))
  
  @traceInduct("")
  def size_check(l: List[BigInt]): Boolean = {
    size1(l) == size2(l)
  }.holds
  
//////////////////////////////////////////////////////////////////////////////////////////////////////////

  def filter1(p: BigInt => Boolean, l: List[BigInt]): List[BigInt] = { 
    if(l.isEmpty) Nil()
    else if(p(l.head)) l.head::filter1(p, l.tail)
    else filter1(p, l.tail)
  }
  
  def filter2(p: BigInt => Boolean, l: List[BigInt]): List[BigInt] = {
    l.filter(p)
  }
  
  @traceInduct("")
  def filter_check(p: BigInt => Boolean, l: List[BigInt]): Boolean = {
    filter1(p, l) == filter2(p, l)
  }.holds

//////////////////////////////////////////////////////////////////////////////////////////////////////////

  def count1(p: BigInt => Boolean, l: List[BigInt]): BigInt = {
    l match {
      case Nil() => BigInt(0)
      case h::t => (if (p(l.head)) BigInt(1) else BigInt(0)) + count1(p, l.tail)
    }
  }//ensuring(res => res == count2(p, l))

  def count2(p: BigInt => Boolean, l: List[BigInt]): BigInt = {
    l.filter(p).size 
  }//ensuring(res => res == count1(p, l))

  @traceInduct("")
  def count_check(p: BigInt => Boolean, l: List[BigInt]): Boolean = {
    count1(p, l) == count2(p, l)
  }.holds
   
//////////////////////////////////////////////////////////////////////////////////////////////////////////

  def map1(p: BigInt => BigInt, l: List[BigInt]): List[BigInt] = { 
    l.map(p)
  }

  def map2(p:BigInt => BigInt, l: List[BigInt]): List[BigInt] = {
    if(l.isEmpty) Nil()
    else p(l.head)::map2(p, l.tail)
  }

  @traceInduct("")
  def map_check(p: BigInt => BigInt, l: List[BigInt]): Boolean = {
    map1(p, l) == map2(p, l)
  }.holds
  
//////////////////////////////////////////////////////////////////////////////////////////////////////////

  def sorted1(l: List[BigInt]): Boolean = {
    if(l.isEmpty) true
    else if (l.size == 1) true
    else if (l.head > l.tail.head) false
    else sorted1(l.tail)
  }//ensuring(res => res == sorted2(l))

  def sorted2(l: List[BigInt]): Boolean = {
    l match {
      case Nil() => true
      case Cons(_, Nil()) => true
      case Cons(h1, Cons(h2, _)) if(h1 > h2) => false
      case Cons(_, t) => sorted2(t)
    }
  }//ensuring(res => res == sorted1(l))

  @traceInduct("")
  def sorted_check(l: List[BigInt]): Boolean = {
    sorted1(l) == sorted2(l)
  }.holds
  
//////////////////////////////////////////////////////////////////////////////////////////////////////////

  def zero1(arg: BigInt): BigInt = { 
    if(arg > 0) zero1(arg -1)
    else BigInt(0)
  }//ensuring(res => res == zero2(arg))

  def zero2(arg: BigInt): BigInt = {
    BigInt(0)
  }//ensuring(res => res == zero1(arg))
  
  @traceInduct("")
  def zero_check(arg: BigInt): Boolean = {
    zero1(arg) == zero2(arg)
  }.holds
   
//////////////////////////////////////////////////////////////////////////////////////////////////////////

}
