
  def example(a: BigInt, b: Boolean, c: BigInt): Boolean = {
    require(b)
    val d = a - c
    val e = d * a
    b && d == d
  } ensuring (res => res == true)
