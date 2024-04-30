object PDDL_Checker_Exported {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def equal_num(x0: num, x1: num): Boolean = (x0, x1) match {
  case (Bit0(x2), Bit1(x3)) => false
  case (Bit1(x3), Bit0(x2)) => false
  case (One(), Bit1(x3)) => false
  case (Bit1(x3), One()) => false
  case (One(), Bit0(x2)) => false
  case (Bit0(x2), One()) => false
  case (Bit1(x3), Bit1(y3)) => equal_num(x3, y3)
  case (Bit0(x2), Bit0(y2)) => equal_num(x2, y2)
  case (One(), One()) => true
}

abstract sealed class int
final case class zero_inta() extends int
final case class Pos(a: num) extends int
final case class Neg(a: num) extends int

def equal_inta(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => equal_num(k, l)
  case (Neg(k), Pos(l)) => false
  case (Neg(k), zero_inta()) => false
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => equal_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => false
  case (zero_inta(), zero_inta()) => true
}

trait equal[A] {
  val `PDDL_Checker_Exported.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
  A.`PDDL_Checker_Exported.equal`(a, b)
object equal {
  implicit def `PDDL_Checker_Exported.equal_object`: equal[objecta] = new
    equal[objecta] {
    val `PDDL_Checker_Exported.equal` = (a: objecta, b: objecta) =>
      equal_objecta(a, b)
  }
  implicit def `PDDL_Checker_Exported.equal_term`[A : equal]: equal[term[A]] =
    new equal[term[A]] {
    val `PDDL_Checker_Exported.equal` = (a: term[A], b: term[A]) =>
      equal_terma[A](a, b)
  }
  implicit def `PDDL_Checker_Exported.equal_unit`: equal[Unit] = new equal[Unit]
    {
    val `PDDL_Checker_Exported.equal` = (a: Unit, b: Unit) => equal_unita(a, b)
  }
  implicit def `PDDL_Checker_Exported.equal_char`: equal[char] = new equal[char]
    {
    val `PDDL_Checker_Exported.equal` = (a: char, b: char) => equal_chara(a, b)
  }
  implicit def `PDDL_Checker_Exported.equal_list`[A : equal]: equal[List[A]] =
    new equal[List[A]] {
    val `PDDL_Checker_Exported.equal` = (a: List[A], b: List[A]) =>
      equal_lista[A](a, b)
  }
  implicit def `PDDL_Checker_Exported.equal_int`: equal[int] = new equal[int] {
    val `PDDL_Checker_Exported.equal` = (a: int, b: int) => equal_inta(a, b)
  }
}

def one_inta: int = Pos(One())

trait one[A] {
  val `PDDL_Checker_Exported.one`: A
}
def one[A](implicit A: one[A]): A = A.`PDDL_Checker_Exported.one`
object one {
  implicit def `PDDL_Checker_Exported.one_integer`: one[BigInt] = new
    one[BigInt] {
    val `PDDL_Checker_Exported.one` = one_integera
  }
  implicit def `PDDL_Checker_Exported.one_int`: one[int] = new one[int] {
    val `PDDL_Checker_Exported.one` = one_inta
  }
}

trait zero[A] {
  val `PDDL_Checker_Exported.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`PDDL_Checker_Exported.zero`
object zero {
  implicit def `PDDL_Checker_Exported.zero_integer`: zero[BigInt] = new
    zero[BigInt] {
    val `PDDL_Checker_Exported.zero` = BigInt(0)
  }
  implicit def `PDDL_Checker_Exported.zero_int`: zero[int] = new zero[int] {
    val `PDDL_Checker_Exported.zero` = zero_inta()
  }
}

trait zero_neq_one[A] extends one[A] with zero[A] {
}
object zero_neq_one {
  implicit def
    `PDDL_Checker_Exported.zero_neq_one_integer`: zero_neq_one[BigInt] = new
    zero_neq_one[BigInt] {
    val `PDDL_Checker_Exported.zero` = BigInt(0)
    val `PDDL_Checker_Exported.one` = one_integera
  }
  implicit def `PDDL_Checker_Exported.zero_neq_one_int`: zero_neq_one[int] = new
    zero_neq_one[int] {
    val `PDDL_Checker_Exported.zero` = zero_inta()
    val `PDDL_Checker_Exported.one` = one_inta
  }
}

abstract sealed class ordera
final case class Eq() extends ordera
final case class Lt() extends ordera
final case class Gt() extends ordera

trait ccompare[A] {
  val `PDDL_Checker_Exported.ccompare`: Option[A => A => ordera]
}
def ccompare[A](implicit A: ccompare[A]): Option[A => A => ordera] =
  A.`PDDL_Checker_Exported.ccompare`
object ccompare {
  implicit def `PDDL_Checker_Exported.ccompare_variable`: ccompare[variable] =
    new ccompare[variable] {
    val `PDDL_Checker_Exported.ccompare` = ccompare_variablea
  }
  implicit def `PDDL_Checker_Exported.ccompare_object`: ccompare[objecta] = new
    ccompare[objecta] {
    val `PDDL_Checker_Exported.ccompare` = ccompare_objecta
  }
  implicit def
    `PDDL_Checker_Exported.ccompare_term`[A : ccompare]: ccompare[term[A]] = new
    ccompare[term[A]] {
    val `PDDL_Checker_Exported.ccompare` = ccompare_terma[A]
  }
  implicit def
    `PDDL_Checker_Exported.ccompare_pred`[A : ccompare]: ccompare[pred[A]] = new
    ccompare[pred[A]] {
    val `PDDL_Checker_Exported.ccompare` = ccompare_preda[A]
  }
  implicit def `PDDL_Checker_Exported.ccompare_char`: ccompare[char] = new
    ccompare[char] {
    val `PDDL_Checker_Exported.ccompare` = ccompare_chara
  }
  implicit def
    `PDDL_Checker_Exported.ccompare_list`[A : ccompare]: ccompare[List[A]] = new
    ccompare[List[A]] {
    val `PDDL_Checker_Exported.ccompare` = ccompare_lista[A]
  }
  implicit def
    `PDDL_Checker_Exported.ccompare_set`[A : finite_UNIV : ceq : cproper_interval : set_impl]:
      ccompare[set[A]]
    = new ccompare[set[A]] {
    val `PDDL_Checker_Exported.ccompare` = ccompare_seta[A]
  }
}

trait ceq[A] {
  val `PDDL_Checker_Exported.ceq`: Option[A => A => Boolean]
}
def ceq[A](implicit A: ceq[A]): Option[A => A => Boolean] =
  A.`PDDL_Checker_Exported.ceq`
object ceq {
  implicit def `PDDL_Checker_Exported.ceq_variable`: ceq[variable] = new
    ceq[variable] {
    val `PDDL_Checker_Exported.ceq` = ceq_variablea
  }
  implicit def `PDDL_Checker_Exported.ceq_term`[A : equal]: ceq[term[A]] = new
    ceq[term[A]] {
    val `PDDL_Checker_Exported.ceq` = ceq_terma[A]
  }
  implicit def `PDDL_Checker_Exported.ceq_pred`[A : equal]: ceq[pred[A]] = new
    ceq[pred[A]] {
    val `PDDL_Checker_Exported.ceq` = ceq_preda[A]
  }
  implicit def `PDDL_Checker_Exported.ceq_char`: ceq[char] = new ceq[char] {
    val `PDDL_Checker_Exported.ceq` = ceq_chara
  }
  implicit def `PDDL_Checker_Exported.ceq_list`[A : ceq]: ceq[List[A]] = new
    ceq[List[A]] {
    val `PDDL_Checker_Exported.ceq` = ceq_lista[A]
  }
  implicit def
    `PDDL_Checker_Exported.ceq_set`[A : cenum : ceq : ccompare]: ceq[set[A]] =
    new ceq[set[A]] {
    val `PDDL_Checker_Exported.ceq` = ceq_seta[A]
  }
}

abstract sealed class set_dlist[A]
final case class Abs_dlist[A](a: List[A]) extends set_dlist[A]

def list_of_dlist[A : ceq](x0: set_dlist[A]): List[A] = x0 match {
  case Abs_dlist(x) => x
}

def list_member[A](equal: A => A => Boolean, x1: List[A], y: A): Boolean =
  (equal, x1, y) match {
  case (equal, x :: xs, y) => (equal(x))(y) || list_member[A](equal, xs, y)
  case (equal, Nil, y) => false
}

abstract sealed class color
final case class R() extends color
final case class B() extends color

abstract sealed class rbt[A, B]
final case class Empty[A, B]() extends rbt[A, B]
final case class Branch[A, B](a: color, b: rbt[A, B], c: A, d: B, e: rbt[A, B])
  extends rbt[A, B]

abstract sealed class mapping_rbt[B, A]
final case class Mapping_RBT[B, A](a: rbt[B, A]) extends mapping_rbt[B, A]

abstract sealed class set[A]
final case class Collect_set[A](a: A => Boolean) extends set[A]
final case class DList_set[A](a: set_dlist[A]) extends set[A]
final case class RBT_set[A](a: mapping_rbt[A, Unit]) extends set[A]
final case class Set_Monad[A](a: List[A]) extends set[A]
final case class Complement[A](a: set[A]) extends set[A]

def uminus_set[A](a: set[A]): set[A] = a match {
  case Complement(b) => b
  case Collect_set(p) => Collect_set[A](((x: A) => ! (p(x))))
  case a => Complement[A](a)
}

def balance[A, B](x0: rbt[A, B], s: A, t: B, x3: rbt[A, B]): rbt[A, B] =
  (x0, s, t, x3) match {
  case (Branch(R(), a, w, x, b), s, t, Branch(R(), c, y, z, d)) =>
    Branch[A, B](R(), Branch[A, B](B(), a, w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, d))
  case (Branch(R(), Branch(R(), a, w, x, b), s, t, c), y, z, Empty()) =>
    Branch[A, B](R(), Branch[A, B](B(), a, w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(R(), Branch(R(), a, w, x, b), s, t, c), y, z,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), Branch[A, B](B(), a, w, x, b), s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Branch(R(), Empty(), w, x, Branch(R(), b, s, t, c)), y, z, Empty()) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(R(), Branch(B(), va, vb, vc, vd), w, x, Branch(R(), b, s, t, c)),
         y, z, Empty())
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t, Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(R(), Empty(), w, x, Branch(R(), b, s, t, c)), y, z,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Branch(R(), Branch(B(), ve, vf, vg, vh), w, x, Branch(R(), b, s, t, c)),
         y, z, Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), ve, vf, vg, vh), w,
                                       x, b),
                     s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Empty(), w, x, Branch(R(), b, s, t, Branch(R(), c, y, z, d))) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, d))
  case (Branch(B(), va, vb, vc, vd), w, x,
         Branch(R(), b, s, t, Branch(R(), c, y, z, d)))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t, Branch[A, B](B(), c, y, z, d))
  case (Empty(), w, x, Branch(R(), Branch(R(), b, s, t, c), y, z, Empty())) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                  Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Empty(), w, x,
         Branch(R(), Branch(R(), b, s, t, c), y, z,
                 Branch(B(), va, vb, vc, vd)))
    => Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), w, x, b), s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Branch(B(), va, vb, vc, vd), w, x,
         Branch(R(), Branch(R(), b, s, t, c), y, z, Empty()))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t, Branch[A, B](B(), c, y, z, Empty[A, B]()))
  case (Branch(B(), va, vb, vc, vd), w, x,
         Branch(R(), Branch(R(), b, s, t, c), y, z,
                 Branch(B(), ve, vf, vg, vh)))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), w,
                                       x, b),
                     s, t,
                     Branch[A, B](B(), c, y, z,
                                   Branch[A, B](B(), ve, vf, vg, vh)))
  case (Empty(), s, t, Empty()) =>
    Branch[A, B](B(), Empty[A, B](), s, t, Empty[A, B]())
  case (Empty(), s, t, Branch(B(), va, vb, vc, vd)) =>
    Branch[A, B](B(), Empty[A, B](), s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Empty(), s, t, Branch(v, Empty(), vb, vc, Empty())) =>
    Branch[A, B](B(), Empty[A, B](), s, t,
                  Branch[A, B](v, Empty[A, B](), vb, vc, Empty[A, B]()))
  case (Empty(), s, t, Branch(v, Branch(B(), ve, vf, vg, vh), vb, vc, Empty()))
    => Branch[A, B](B(), Empty[A, B](), s, t,
                     Branch[A, B](v, Branch[A, B](B(), ve, vf, vg, vh), vb, vc,
                                   Empty[A, B]()))
  case (Empty(), s, t, Branch(v, Empty(), vb, vc, Branch(B(), vf, vg, vh, vi)))
    => Branch[A, B](B(), Empty[A, B](), s, t,
                     Branch[A, B](v, Empty[A, B](), vb, vc,
                                   Branch[A, B](B(), vf, vg, vh, vi)))
  case (Empty(), s, t,
         Branch(v, Branch(B(), ve, vj, vk, vl), vb, vc,
                 Branch(B(), vf, vg, vh, vi)))
    => Branch[A, B](B(), Empty[A, B](), s, t,
                     Branch[A, B](v, Branch[A, B](B(), ve, vj, vk, vl), vb, vc,
                                   Branch[A, B](B(), vf, vg, vh, vi)))
  case (Branch(B(), va, vb, vc, vd), s, t, Empty()) =>
    Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t, Empty[A, B]())
  case (Branch(B(), va, vb, vc, vd), s, t, Branch(B(), ve, vf, vg, vh)) =>
    Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                  Branch[A, B](B(), ve, vf, vg, vh))
  case (Branch(B(), va, vb, vc, vd), s, t, Branch(v, Empty(), vf, vg, Empty()))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Empty[A, B](), vf, vg, Empty[A, B]()))
  case (Branch(B(), va, vb, vc, vd), s, t,
         Branch(v, Branch(B(), vi, vj, vk, vl), vf, vg, Empty()))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Branch[A, B](B(), vi, vj, vk, vl), vf, vg,
                                   Empty[A, B]()))
  case (Branch(B(), va, vb, vc, vd), s, t,
         Branch(v, Empty(), vf, vg, Branch(B(), vj, vk, vl, vm)))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Empty[A, B](), vf, vg,
                                   Branch[A, B](B(), vj, vk, vl, vm)))
  case (Branch(B(), va, vb, vc, vd), s, t,
         Branch(v, Branch(B(), vi, vn, vo, vp), vf, vg,
                 Branch(B(), vj, vk, vl, vm)))
    => Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), s, t,
                     Branch[A, B](v, Branch[A, B](B(), vi, vn, vo, vp), vf, vg,
                                   Branch[A, B](B(), vj, vk, vl, vm)))
  case (Branch(v, Empty(), vb, vc, Empty()), s, t, Empty()) =>
    Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vb, vc, Empty[A, B]()), s,
                  t, Empty[A, B]())
  case (Branch(v, Empty(), vb, vc, Branch(B(), ve, vf, vg, vh)), s, t, Empty())
    => Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vb, vc,
                                       Branch[A, B](B(), ve, vf, vg, vh)),
                     s, t, Empty[A, B]())
  case (Branch(v, Branch(B(), vf, vg, vh, vi), vb, vc, Empty()), s, t, Empty())
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vf, vg, vh, vi), vb,
                                       vc, Empty[A, B]()),
                     s, t, Empty[A, B]())
  case (Branch(v, Branch(B(), vf, vg, vh, vi), vb, vc,
                Branch(B(), ve, vj, vk, vl)),
         s, t, Empty())
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vf, vg, vh, vi), vb,
                                       vc, Branch[A, B](B(), ve, vj, vk, vl)),
                     s, t, Empty[A, B]())
  case (Branch(v, Empty(), vf, vg, Empty()), s, t, Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vf, vg, Empty[A, B]()),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(v, Empty(), vf, vg, Branch(B(), vi, vj, vk, vl)), s, t,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vf, vg,
                                       Branch[A, B](B(), vi, vj, vk, vl)),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(v, Branch(B(), vj, vk, vl, vm), vf, vg, Empty()), s, t,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vj, vk, vl, vm), vf,
                                       vg, Empty[A, B]()),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(v, Branch(B(), vj, vk, vl, vm), vf, vg,
                Branch(B(), vi, vn, vo, vp)),
         s, t, Branch(B(), va, vb, vc, vd))
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vj, vk, vl, vm), vf,
                                       vg, Branch[A, B](B(), vi, vn, vo, vp)),
                     s, t, Branch[A, B](B(), va, vb, vc, vd))
}

def rbt_comp_ins[A, B](c: A => A => ordera, f: A => B => B => B, k: A, v: B,
                        x4: rbt[A, B]):
      rbt[A, B]
  =
  (c, f, k, v, x4) match {
  case (c, f, k, v, Empty()) =>
    Branch[A, B](R(), Empty[A, B](), k, v, Empty[A, B]())
  case (c, f, k, v, Branch(B(), l, x, y, r)) =>
    ((c(k))(x) match {
       case Eq() => Branch[A, B](B(), l, x, ((f(k))(y))(v), r)
       case Lt() => balance[A, B](rbt_comp_ins[A, B](c, f, k, v, l), x, y, r)
       case Gt() => balance[A, B](l, x, y, rbt_comp_ins[A, B](c, f, k, v, r))
     })
  case (c, f, k, v, Branch(R(), l, x, y, r)) =>
    ((c(k))(x) match {
       case Eq() => Branch[A, B](R(), l, x, ((f(k))(y))(v), r)
       case Lt() =>
         Branch[A, B](R(), rbt_comp_ins[A, B](c, f, k, v, l), x, y, r)
       case Gt() =>
         Branch[A, B](R(), l, x, y, rbt_comp_ins[A, B](c, f, k, v, r))
     })
}

def paint[A, B](c: color, x1: rbt[A, B]): rbt[A, B] = (c, x1) match {
  case (c, Empty()) => Empty[A, B]()
  case (c, Branch(uu, l, k, v, r)) => Branch[A, B](c, l, k, v, r)
}

def rbt_comp_insert_with_key[A, B](c: A => A => ordera, f: A => B => B => B,
                                    k: A, v: B, t: rbt[A, B]):
      rbt[A, B]
  =
  paint[A, B](B(), rbt_comp_ins[A, B](c, f, k, v, t))

def rbt_comp_insert[A, B](c: A => A => ordera):
      A => B => (rbt[A, B]) => rbt[A, B]
  =
  ((a: A) => (b: B) => (d: rbt[A, B]) =>
    rbt_comp_insert_with_key[A, B](c, ((_: A) => (_: B) => (nv: B) => nv), a, b,
                                    d))

def impl_ofa[B : ccompare, A](x0: mapping_rbt[B, A]): rbt[B, A] = x0 match {
  case Mapping_RBT(x) => x
}

def the[A](x0: Option[A]): A = x0 match {
  case Some(x2) => x2
}

def insertb[A : ccompare, B](xc: A, xd: B, xe: mapping_rbt[A, B]):
      mapping_rbt[A, B]
  =
  Mapping_RBT[A, B]((rbt_comp_insert[A, B](the[A =>
         A => ordera](ccompare[A]))).apply(xc).apply(xd).apply(impl_ofa[A,
                                 B](xe)))

abstract sealed class nat
final case class Nat(a: BigInt) extends nat

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nat(x) => x
}

def less_nat(m: nat, n: nat): Boolean = integer_of_nat(m) < integer_of_nat(n)

def less_eq_nat(m: nat, n: nat): Boolean =
  integer_of_nat(m) <= integer_of_nat(n)

def rbt_baliR[A, B](t1: rbt[A, B], ab: A, bb: B, x3: rbt[A, B]): rbt[A, B] =
  (t1, ab, bb, x3) match {
  case (t1, ab, bb, Branch(R(), t2, aa, ba, Branch(R(), t3, a, b, t4))) =>
    Branch[A, B](R(), Branch[A, B](B(), t1, ab, bb, t2), aa, ba,
                  Branch[A, B](B(), t3, a, b, t4))
  case (t1, ab, bb, Branch(R(), Branch(R(), t2, aa, ba, t3), a, b, Empty())) =>
    Branch[A, B](R(), Branch[A, B](B(), t1, ab, bb, t2), aa, ba,
                  Branch[A, B](B(), t3, a, b, Empty[A, B]()))
  case (t1, ab, bb,
         Branch(R(), Branch(R(), t2, aa, ba, t3), a, b,
                 Branch(B(), va, vb, vc, vd)))
    => Branch[A, B](R(), Branch[A, B](B(), t1, ab, bb, t2), aa, ba,
                     Branch[A, B](B(), t3, a, b,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (t1, a, b, Empty()) => Branch[A, B](B(), t1, a, b, Empty[A, B]())
  case (t1, a, b, Branch(B(), va, vb, vc, vd)) =>
    Branch[A, B](B(), t1, a, b, Branch[A, B](B(), va, vb, vc, vd))
  case (t1, a, b, Branch(v, Empty(), vb, vc, Empty())) =>
    Branch[A, B](B(), t1, a, b,
                  Branch[A, B](v, Empty[A, B](), vb, vc, Empty[A, B]()))
  case (t1, a, b, Branch(v, Branch(B(), ve, vf, vg, vh), vb, vc, Empty())) =>
    Branch[A, B](B(), t1, a, b,
                  Branch[A, B](v, Branch[A, B](B(), ve, vf, vg, vh), vb, vc,
                                Empty[A, B]()))
  case (t1, a, b, Branch(v, Empty(), vb, vc, Branch(B(), vf, vg, vh, vi))) =>
    Branch[A, B](B(), t1, a, b,
                  Branch[A, B](v, Empty[A, B](), vb, vc,
                                Branch[A, B](B(), vf, vg, vh, vi)))
  case (t1, a, b,
         Branch(v, Branch(B(), ve, vj, vk, vl), vb, vc,
                 Branch(B(), vf, vg, vh, vi)))
    => Branch[A, B](B(), t1, a, b,
                     Branch[A, B](v, Branch[A, B](B(), ve, vj, vk, vl), vb, vc,
                                   Branch[A, B](B(), vf, vg, vh, vi)))
}

def equal_color(x0: color, x1: color): Boolean = (x0, x1) match {
  case (R(), B()) => false
  case (B(), R()) => false
  case (B(), B()) => true
  case (R(), R()) => true
}

def zero_nat: nat = Nat(BigInt(0))

def plus_nat(m: nat, n: nat): nat = Nat(integer_of_nat(m) + integer_of_nat(n))

def one_nat: nat = Nat(BigInt(1))

def Suc(n: nat): nat = plus_nat(n, one_nat)

def bheight[A, B](x0: rbt[A, B]): nat = x0 match {
  case Empty() => zero_nat
  case Branch(c, lt, k, v, rt) =>
    (if (equal_color(c, B())) Suc(bheight[A, B](lt)) else bheight[A, B](lt))
}

def rbt_joinR[A, B](l: rbt[A, B], a: A, b: B, r: rbt[A, B]): rbt[A, B] =
  (if (less_eq_nat(bheight[A, B](l), bheight[A, B](r)))
    Branch[A, B](R(), l, a, b, r)
    else (l match {
            case Branch(R(), la, ab, ba, ra) =>
              Branch[A, B](R(), la, ab, ba, rbt_joinR[A, B](ra, a, b, r))
            case Branch(B(), la, ab, ba, ra) =>
              rbt_baliR[A, B](la, ab, ba, rbt_joinR[A, B](ra, a, b, r))
          }))

def rbt_baliL[A, B](x0: rbt[A, B], a: A, b: B, t4: rbt[A, B]): rbt[A, B] =
  (x0, a, b, t4) match {
  case (Branch(R(), Branch(R(), t1, ab, bb, t2), aa, ba, t3), a, b, t4) =>
    Branch[A, B](R(), Branch[A, B](B(), t1, ab, bb, t2), aa, ba,
                  Branch[A, B](B(), t3, a, b, t4))
  case (Branch(R(), Empty(), ab, bb, Branch(R(), t2, aa, ba, t3)), a, b, t4) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), ab, bb, t2), aa, ba,
                  Branch[A, B](B(), t3, a, b, t4))
  case (Branch(R(), Branch(B(), va, vb, vc, vd), ab, bb,
                Branch(R(), t2, aa, ba, t3)),
         a, b, t4)
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd),
                                       ab, bb, t2),
                     aa, ba, Branch[A, B](B(), t3, a, b, t4))
  case (Empty(), a, b, t2) => Branch[A, B](B(), Empty[A, B](), a, b, t2)
  case (Branch(B(), va, vb, vc, vd), a, b, t2) =>
    Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), a, b, t2)
  case (Branch(v, Empty(), vb, vc, Empty()), a, b, t2) =>
    Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vb, vc, Empty[A, B]()), a,
                  b, t2)
  case (Branch(v, Empty(), vb, vc, Branch(B(), ve, vf, vg, vh)), a, b, t2) =>
    Branch[A, B](B(), Branch[A, B](v, Empty[A, B](), vb, vc,
                                    Branch[A, B](B(), ve, vf, vg, vh)),
                  a, b, t2)
  case (Branch(v, Branch(B(), vf, vg, vh, vi), vb, vc, Empty()), a, b, t2) =>
    Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vf, vg, vh, vi), vb, vc,
                                    Empty[A, B]()),
                  a, b, t2)
  case (Branch(v, Branch(B(), vf, vg, vh, vi), vb, vc,
                Branch(B(), ve, vj, vk, vl)),
         a, b, t2)
    => Branch[A, B](B(), Branch[A, B](v, Branch[A, B](B(), vf, vg, vh, vi), vb,
                                       vc, Branch[A, B](B(), ve, vj, vk, vl)),
                     a, b, t2)
}

def rbt_joinL[A, B](l: rbt[A, B], a: A, b: B, r: rbt[A, B]): rbt[A, B] =
  (if (less_eq_nat(bheight[A, B](r), bheight[A, B](l)))
    Branch[A, B](R(), l, a, b, r)
    else (r match {
            case Branch(R(), la, ab, ba, ra) =>
              Branch[A, B](R(), rbt_joinL[A, B](l, a, b, la), ab, ba, ra)
            case Branch(B(), la, ab, ba, ra) =>
              rbt_baliL[A, B](rbt_joinL[A, B](l, a, b, la), ab, ba, ra)
          }))

def rbt_join[A, B](l: rbt[A, B], a: A, b: B, r: rbt[A, B]): rbt[A, B] =
  {
    val bhl = bheight[A, B](l): nat
    val bhr = bheight[A, B](r): nat;
    (if (less_nat(bhr, bhl)) paint[A, B](B(), rbt_joinR[A, B](l, a, b, r))
      else (if (less_nat(bhl, bhr))
             paint[A, B](B(), rbt_joinL[A, B](l, a, b, r))
             else Branch[A, B](B(), l, a, b, r)))
  }

def rbt_split_comp[A, B](c: A => A => ordera, x1: rbt[A, B], k: A):
      (rbt[A, B], (Option[B], rbt[A, B]))
  =
  (c, x1, k) match {
  case (c, Empty(), k) => (Empty[A, B](), (None, Empty[A, B]()))
  case (c, Branch(uu, l, a, b, r), x) =>
    ((c(x))(a) match {
       case Eq() => (l, (Some[B](b), r))
       case Lt() =>
         {
           val (l1, (beta, l2)) =
             rbt_split_comp[A, B](c, l, x):
               ((rbt[A, B], (Option[B], rbt[A, B])));
           (l1, (beta, rbt_join[A, B](l2, a, b, r)))
         }
       case Gt() =>
         {
           val (r1, (beta, r2)) =
             rbt_split_comp[A, B](c, r, x):
               ((rbt[A, B], (Option[B], rbt[A, B])));
           (rbt_join[A, B](l, a, b, r1), (beta, r2))
         }
     })
}

trait ord[A] {
  val `PDDL_Checker_Exported.less_eq`: (A, A) => Boolean
  val `PDDL_Checker_Exported.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`PDDL_Checker_Exported.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`PDDL_Checker_Exported.less`(a, b)
object ord {
  implicit def `PDDL_Checker_Exported.ord_integer`: ord[BigInt] = new
    ord[BigInt] {
    val `PDDL_Checker_Exported.less_eq` = (a: BigInt, b: BigInt) => a <= b
    val `PDDL_Checker_Exported.less` = (a: BigInt, b: BigInt) => a < b
  }
  implicit def `PDDL_Checker_Exported.ord_char`: ord[char] = new ord[char] {
    val `PDDL_Checker_Exported.less_eq` = (a: char, b: char) =>
      less_eq_char(a, b)
    val `PDDL_Checker_Exported.less` = (a: char, b: char) => less_char(a, b)
  }
  implicit def `PDDL_Checker_Exported.ord_bool`: ord[Boolean] = new ord[Boolean]
    {
    val `PDDL_Checker_Exported.less_eq` = (a: Boolean, b: Boolean) =>
      less_eq_bool(a, b)
    val `PDDL_Checker_Exported.less` = (a: Boolean, b: Boolean) =>
      less_bool(a, b)
  }
  implicit def
    `PDDL_Checker_Exported.ord_set`[A : cenum : ceq : ccompare]: ord[set[A]] =
    new ord[set[A]] {
    val `PDDL_Checker_Exported.less_eq` = (a: set[A], b: set[A]) =>
      less_eq_set[A](a, b)
    val `PDDL_Checker_Exported.less` = (a: set[A], b: set[A]) =>
      less_set[A](a, b)
  }
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def nat_of_integer(k: BigInt): nat = Nat(max[BigInt](BigInt(0), k))

def folda[A, B, C](f: A => B => C => C, xa1: rbt[A, B], x: C): C = (f, xa1, x)
  match {
  case (f, Branch(c, lt, k, v, rt), x) =>
    folda[A, B, C](f, rt, ((f(k))(v))(folda[A, B, C](f, lt, x)))
  case (f, Empty(), x) => x
}

def rbt_comp_union_swap_rec[A, B](c: A => A => ordera, f: A => B => B => B,
                                   gamma: Boolean, t1: rbt[A, B],
                                   t2: rbt[A, B]):
      rbt[A, B]
  =
  {
    val bh1 = bheight[A, B](t1): nat
    val bh2 = bheight[A, B](t2): nat
    val (gammaa, (t2a, (bh2a, (t1a, _)))) =
      (if (less_nat(bh1, bh2)) (! gamma, (t1, (bh1, (t2, bh2))))
        else (gamma, (t2, (bh2, (t1, bh1))))):
        ((Boolean, (rbt[A, B], (nat, (rbt[A, B], nat)))))
    val fa =
      (if (gammaa) ((k: A) => (v: B) => (va: B) => ((f(k))(va))(v)) else f):
        (A => B => B => B);
    (if (less_nat(bh2a, nat_of_integer(BigInt(4))))
      folda[A, B,
             rbt[A, B]](((a: A) => (b: B) => (d: rbt[A, B]) =>
                          rbt_comp_insert_with_key[A, B](c, fa, a, b, d)),
                         t2a, t1a)
      else (t1a match {
              case Empty() => t2a
              case Branch(_, l1, a, b, r1) =>
                {
                  val (l2, (beta, r2)) =
                    rbt_split_comp[A, B](c, t2a, a):
                      ((rbt[A, B], (Option[B], rbt[A, B])));
                  rbt_join[A, B](rbt_comp_union_swap_rec[A,
                  B](c, f, gammaa, l1, l2),
                                  a, (beta match {
case None => b
case Some(ca) => ((fa(a))(b))(ca)
                                      }),
                                  rbt_comp_union_swap_rec[A,
                   B](c, f, gammaa, r1, r2))
                }
            }))
  }

def rbt_comp_union_with_key[A, B](c: A => A => ordera, f: A => B => B => B,
                                   t1: rbt[A, B], t2: rbt[A, B]):
      rbt[A, B]
  =
  paint[A, B](B(), rbt_comp_union_swap_rec[A, B](c, f, false, t1, t2))

def join[A : ccompare,
          B](xc: A => B => B => B, xd: mapping_rbt[A, B],
              xe: mapping_rbt[A, B]):
      mapping_rbt[A, B]
  =
  Mapping_RBT[A, B](rbt_comp_union_with_key[A,
     B](the[A => A => ordera](ccompare[A]), xc, impl_ofa[A, B](xd),
         impl_ofa[A, B](xe)))

def list_insert[A](equal: A => A => Boolean, x: A, xs: List[A]): List[A] =
  (if (list_member[A](equal, xs, x)) xs else x :: xs)

def inserta[A : ceq](xb: A, xc: set_dlist[A]): set_dlist[A] =
  Abs_dlist[A](list_insert[A](the[A => A => Boolean](ceq[A]), xb,
                               list_of_dlist[A](xc)))

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def foldc[A : ceq, B](x: A => B => B, xc: set_dlist[A]): B => B =
  ((a: B) => fold[A, B](x, list_of_dlist[A](xc), a))

def union[A : ceq]: (set_dlist[A]) => (set_dlist[A]) => set_dlist[A] =
  ((a: set_dlist[A]) =>
    foldc[A, set_dlist[A]](((aa: A) => (b: set_dlist[A]) => inserta[A](aa, b)),
                            a))

def memberb[A : ceq](xa: set_dlist[A]): A => Boolean =
  ((a: A) =>
    list_member[A](the[A => A => Boolean](ceq[A]), list_of_dlist[A](xa), a))

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def equal_option[A : equal](x0: Option[A], x1: Option[A]): Boolean = (x0, x1)
  match {
  case (None, Some(x2)) => false
  case (Some(x2), None) => false
  case (Some(x2), Some(y2)) => eq[A](x2, y2)
  case (None, None) => true
}

def rbt_comp_lookup[A, B](c: A => A => ordera, x1: rbt[A, B], k: A): Option[B] =
  (c, x1, k) match {
  case (c, Empty(), k) => None
  case (c, Branch(uu, l, x, y, r), k) =>
    ((c(k))(x) match {
       case Eq() => Some[B](y)
       case Lt() => rbt_comp_lookup[A, B](c, l, k)
       case Gt() => rbt_comp_lookup[A, B](c, r, k)
     })
}

def lookupb[A : ccompare, B](xa: mapping_rbt[A, B]): A => Option[B] =
  ((a: A) =>
    rbt_comp_lookup[A, B](the[A => A => ordera](ccompare[A]),
                           impl_ofa[A, B](xa), a))

def equal_unita(u: Unit, v: Unit): Boolean = true

def membera[A : ccompare](t: mapping_rbt[A, Unit], x: A): Boolean =
  equal_option[Unit]((lookupb[A, Unit](t)).apply(x), Some[Unit](()))

def member[A : ceq : ccompare](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, Set_Monad(xs)) =>
    (ceq[A] match {
       case None =>
         { sys.error("member Set_Monad: ceq = None");
           (((_: Unit) => member[A](x, Set_Monad[A](xs)))).apply(()) }
       case Some(eq) => list_member[A](eq, xs, x)
     })
  case (xa, Complement(x)) => ! (member[A](xa, x))
  case (x, RBT_set(rbt)) => membera[A](rbt, x)
  case (x, DList_set(dxs)) => (memberb[A](dxs)).apply(x)
  case (x, Collect_set(a)) => a(x)
}

def id[A]: A => A = ((x: A) => x)

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def is_none[A](x0: Option[A]): Boolean = x0 match {
  case Some(x) => false
  case None => true
}

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def inter_list[A : ccompare](xb: mapping_rbt[A, Unit], xc: List[A]):
      mapping_rbt[A, Unit]
  =
  Mapping_RBT[A, Unit](fold[A, rbt[A, Unit]](((k: A) =>
       (rbt_comp_insert[A, Unit](the[A => A =>
    ordera](ccompare[A]))).apply(k).apply(())),
      filter[A](((x: A) =>
                  ! (is_none[Unit](rbt_comp_lookup[A,
            Unit](the[A => A => ordera](ccompare[A]), impl_ofa[A, Unit](xb),
                   x)))),
                 xc),
      Empty[A, Unit]()))

def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Suc(n), xs)
  case (n, Nil) => n
}

def size_list[A]: (List[A]) => nat =
  ((a: List[A]) => gen_length[A](zero_nat, a))

def equal_nat(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

def map_prod[A, B, C, D](f: A => B, g: C => D, x2: (A, C)): (B, D) = (f, g, x2)
  match {
  case (f, g, (a, b)) => (f(a), g(b))
}

def divmod_nat(m: nat, n: nat): (nat, nat) =
  {
    val k = integer_of_nat(m): BigInt
    val l = integer_of_nat(n): BigInt;
    map_prod[BigInt, nat, BigInt,
              nat](((a: BigInt) => nat_of_integer(a)),
                    ((a: BigInt) => nat_of_integer(a)),
                    (if (k == BigInt(0)) (BigInt(0), BigInt(0))
                      else (if (l == BigInt(0)) (BigInt(0), k)
                             else ((k: BigInt) => (l: BigInt) => if (l == 0)
                                    (BigInt(0), k) else
                                    (k.abs /% l.abs)).apply(k).apply(l))))
  }

def apfst[A, B, C](f: A => B, x1: (A, C)): (B, C) = (f, x1) match {
  case (f, (x, y)) => (f(x), y)
}

def rbtreeify_f[A, B](n: nat, kvs: List[(A, B)]): (rbt[A, B], List[(A, B)]) =
  (if (equal_nat(n, zero_nat)) (Empty[A, B](), kvs)
    else (if (equal_nat(n, one_nat))
           {
             val ((k, v) :: kvsa) = kvs: (List[(A, B)]);
             (Branch[A, B](R(), Empty[A, B](), k, v, Empty[A, B]()), kvsa)
           }
           else {
                  val (na, r) =
                    divmod_nat(n, nat_of_integer(BigInt(2))): ((nat, nat));
                  (if (equal_nat(r, zero_nat))
                    {
                      val (t1, (k, v) :: kvsa) =
                        rbtreeify_f[A, B](na, kvs): ((rbt[A, B], List[(A, B)]));
                      apfst[rbt[A, B], rbt[A, B],
                             List[(A, B)]](((a: rbt[A, B]) =>
     Branch[A, B](B(), t1, k, v, a)),
    rbtreeify_g[A, B](na, kvsa))
                    }
                    else {
                           val (t1, (k, v) :: kvsa) =
                             rbtreeify_f[A, B](na, kvs):
                               ((rbt[A, B], List[(A, B)]));
                           apfst[rbt[A, B], rbt[A, B],
                                  List[(A,
 B)]](((a: rbt[A, B]) => Branch[A, B](B(), t1, k, v, a)),
       rbtreeify_f[A, B](na, kvsa))
                         })
                }))

def rbtreeify_g[A, B](n: nat, kvs: List[(A, B)]): (rbt[A, B], List[(A, B)]) =
  (if (equal_nat(n, zero_nat) || equal_nat(n, one_nat)) (Empty[A, B](), kvs)
    else {
           val (na, r) = divmod_nat(n, nat_of_integer(BigInt(2))): ((nat, nat));
           (if (equal_nat(r, zero_nat))
             {
               val (t1, (k, v) :: kvsa) =
                 rbtreeify_g[A, B](na, kvs): ((rbt[A, B], List[(A, B)]));
               apfst[rbt[A, B], rbt[A, B],
                      List[(A, B)]](((a: rbt[A, B]) =>
                                      Branch[A, B](B(), t1, k, v, a)),
                                     rbtreeify_g[A, B](na, kvsa))
             }
             else {
                    val (t1, (k, v) :: kvsa) =
                      rbtreeify_f[A, B](na, kvs): ((rbt[A, B], List[(A, B)]));
                    apfst[rbt[A, B], rbt[A, B],
                           List[(A, B)]](((a: rbt[A, B]) =>
   Branch[A, B](B(), t1, k, v, a)),
  rbtreeify_g[A, B](na, kvsa))
                  })
         })

def rbtreeify[A, B](kvs: List[(A, B)]): rbt[A, B] =
  fst[rbt[A, B],
       List[(A, B)]](rbtreeify_g[A, B](Suc(size_list[(A, B)].apply(kvs)), kvs))

def gen_entries[A, B](kvts: List[((A, B), rbt[A, B])], x1: rbt[A, B]):
      List[(A, B)]
  =
  (kvts, x1) match {
  case (kvts, Branch(c, l, k, v, r)) =>
    gen_entries[A, B](((k, v), r) :: kvts, l)
  case ((kv, t) :: kvts, Empty()) => kv :: gen_entries[A, B](kvts, t)
  case (Nil, Empty()) => Nil
}

def entries[A, B]: (rbt[A, B]) => List[(A, B)] =
  ((a: rbt[A, B]) => gen_entries[A, B](Nil, a))

def filterb[A : ccompare, B](xb: ((A, B)) => Boolean, xc: mapping_rbt[A, B]):
      mapping_rbt[A, B]
  =
  Mapping_RBT[A, B](rbtreeify[A, B](filter[(A,
     B)](xb, entries[A, B].apply(impl_ofa[A, B](xc)))))

def map_filter[A, B](f: A => Option[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => (f(x) match {
                          case None => map_filter[A, B](f, xs)
                          case Some(y) => y :: map_filter[A, B](f, xs)
                        })
}

def map_filter_comp_inter[A, B, C,
                           D](c: A => A => ordera, f: A => B => C => D,
                               t1: rbt[A, B], t2: rbt[A, C]):
      List[(A, D)]
  =
  map_filter[(A, C),
              (A, D)](((a: (A, C)) =>
                        {
                          val (k, v) = a: ((A, C));
                          (rbt_comp_lookup[A, B](c, t1, k) match {
                             case None => None
                             case Some(va) => Some[(A, D)]((k, ((f(k))(va))(v)))
                           })
                        }),
                       entries[A, C].apply(t2))

def is_rbt_empty[A, B](t: rbt[A, B]): Boolean =
  (t match {
     case Empty() => true
     case Branch(_, _, _, _, _) => false
   })

def rbt_split_min[A, B](x0: rbt[A, B]): (A, (B, rbt[A, B])) = x0 match {
  case Empty() => sys.error("undefined")
  case Branch(uu, l, a, b, r) =>
    (if (is_rbt_empty[A, B](l)) (a, (b, r))
      else {
             val (aa, (ba, la)) = rbt_split_min[A, B](l): ((A, (B, rbt[A, B])));
             (aa, (ba, rbt_join[A, B](la, a, b, r)))
           })
}

def rbt_join2[A, B](l: rbt[A, B], r: rbt[A, B]): rbt[A, B] =
  (if (is_rbt_empty[A, B](r)) l
    else {
           val (a, (b, c)) = rbt_split_min[A, B](r): ((A, (B, rbt[A, B])));
           rbt_join[A, B](l, a, b, c)
         })

def rbt_comp_inter_swap_rec[A, B](c: A => A => ordera, f: A => B => B => B,
                                   gamma: Boolean, t1: rbt[A, B],
                                   t2: rbt[A, B]):
      rbt[A, B]
  =
  {
    val bh1 = bheight[A, B](t1): nat
    val bh2 = bheight[A, B](t2): nat
    val (gammaa, (t2a, (bh2a, (t1a, _)))) =
      (if (less_nat(bh1, bh2)) (! gamma, (t1, (bh1, (t2, bh2))))
        else (gamma, (t2, (bh2, (t1, bh1))))):
        ((Boolean, (rbt[A, B], (nat, (rbt[A, B], nat)))))
    val fa =
      (if (gammaa) ((k: A) => (v: B) => (va: B) => ((f(k))(va))(v)) else f):
        (A => B => B => B);
    (if (less_nat(bh2a, nat_of_integer(BigInt(4))))
      rbtreeify[A, B](map_filter_comp_inter[A, B, B, B](c, fa, t1a, t2a))
      else (t1a match {
              case Empty() => Empty[A, B]()
              case Branch(_, l1, a, b, r1) =>
                {
                  val (l2, (beta, r2)) =
                    rbt_split_comp[A, B](c, t2a, a):
                      ((rbt[A, B], (Option[B], rbt[A, B])))
                  val l =
                    rbt_comp_inter_swap_rec[A, B](c, f, gammaa, l1, l2):
                      (rbt[A, B])
                  val r =
                    rbt_comp_inter_swap_rec[A, B](c, f, gammaa, r1, r2):
                      (rbt[A, B]);
                  (beta match {
                     case None => rbt_join2[A, B](l, r)
                     case Some(ba) => rbt_join[A, B](l, a, ((fa(a))(b))(ba), r)
                   })
                }
            }))
  }

def rbt_comp_inter_with_key[A, B](c: A => A => ordera, f: A => B => B => B,
                                   t1: rbt[A, B], t2: rbt[A, B]):
      rbt[A, B]
  =
  paint[A, B](B(), rbt_comp_inter_swap_rec[A, B](c, f, false, t1, t2))

def meet[A : ccompare,
          B](xc: A => B => B => B, xd: mapping_rbt[A, B],
              xe: mapping_rbt[A, B]):
      mapping_rbt[A, B]
  =
  Mapping_RBT[A, B](rbt_comp_inter_with_key[A,
     B](the[A => A => ordera](ccompare[A]), xc, impl_ofa[A, B](xd),
         impl_ofa[A, B](xe)))

def filtera[A : ceq](xb: A => Boolean, xc: set_dlist[A]): set_dlist[A] =
  Abs_dlist[A](filter[A](xb, list_of_dlist[A](xc)))

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

def sup_seta[A : ceq : ccompare](ba: set[A], b: set[A]): set[A] = (ba, b) match
  {
  case (ba, Complement(b)) => Complement[A](inf_seta[A](uminus_set[A](ba), b))
  case (Complement(ba), b) => Complement[A](inf_seta[A](ba, uminus_set[A](b)))
  case (b, Collect_set(a)) =>
    Collect_set[A](((x: A) => a(x) || member[A](x, b)))
  case (Collect_set(a), b) =>
    Collect_set[A](((x: A) => a(x) || member[A](x, b)))
  case (Set_Monad(xs), Set_Monad(ys)) => Set_Monad[A](xs ++ ys)
  case (DList_set(dxs1), Set_Monad(ws)) =>
    (ceq[A] match {
       case None =>
         { sys.error("union DList_set Set_Monad: ceq = None");
           (((_: Unit) =>
              sup_seta[A](DList_set[A](dxs1), Set_Monad[A](ws)))).apply(())
           }
       case Some(_) =>
         DList_set[A](fold[A, set_dlist[A]](((a: A) => (b: set_dlist[A]) =>
      inserta[A](a, b)),
     ws, dxs1))
     })
  case (Set_Monad(ws), DList_set(dxs2)) =>
    (ceq[A] match {
       case None =>
         { sys.error("union Set_Monad DList_set: ceq = None");
           (((_: Unit) =>
              sup_seta[A](Set_Monad[A](ws), DList_set[A](dxs2)))).apply(())
           }
       case Some(_) =>
         DList_set[A](fold[A, set_dlist[A]](((a: A) => (b: set_dlist[A]) =>
      inserta[A](a, b)),
     ws, dxs2))
     })
  case (RBT_set(rbt1), Set_Monad(zs)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("union RBT_set Set_Monad: ccompare = None");
           (((_: Unit) =>
              sup_seta[A](RBT_set[A](rbt1), Set_Monad[A](zs)))).apply(())
           }
       case Some(_) =>
         RBT_set[A](fold[A, mapping_rbt[A,
 Unit]](((k: A) => ((a: mapping_rbt[A, Unit]) => insertb[A, Unit](k, (), a))),
         zs, rbt1))
     })
  case (Set_Monad(zs), RBT_set(rbt2)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("union Set_Monad RBT_set: ccompare = None");
           (((_: Unit) =>
              sup_seta[A](Set_Monad[A](zs), RBT_set[A](rbt2)))).apply(())
           }
       case Some(_) =>
         RBT_set[A](fold[A, mapping_rbt[A,
 Unit]](((k: A) => ((a: mapping_rbt[A, Unit]) => insertb[A, Unit](k, (), a))),
         zs, rbt2))
     })
  case (DList_set(dxs1), DList_set(dxs2)) =>
    (ceq[A] match {
       case None =>
         { sys.error("union DList_set DList_set: ceq = None");
           (((_: Unit) =>
              sup_seta[A](DList_set[A](dxs1), DList_set[A](dxs2)))).apply(())
           }
       case Some(_) => DList_set[A](union[A].apply(dxs1).apply(dxs2))
     })
  case (DList_set(dxs), RBT_set(rbt)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("union DList_set RBT_set: ccompare = None");
           (((_: Unit) =>
              sup_seta[A](RBT_set[A](rbt), DList_set[A](dxs)))).apply(())
           }
       case Some(_) =>
         (ceq[A] match {
            case None =>
              { sys.error("union DList_set RBT_set: ceq = None");
                (((_: Unit) =>
                   sup_seta[A](RBT_set[A](rbt), DList_set[A](dxs)))).apply(())
                }
            case Some(_) =>
              RBT_set[A]((foldc[A, mapping_rbt[A,
        Unit]](((k: A) =>
                 ((a: mapping_rbt[A, Unit]) => insertb[A, Unit](k, (), a))),
                dxs)).apply(rbt))
          })
     })
  case (RBT_set(rbt), DList_set(dxs)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("union RBT_set DList_set: ccompare = None");
           (((_: Unit) =>
              sup_seta[A](RBT_set[A](rbt), DList_set[A](dxs)))).apply(())
           }
       case Some(_) =>
         (ceq[A] match {
            case None =>
              { sys.error("union RBT_set DList_set: ceq = None");
                (((_: Unit) =>
                   sup_seta[A](RBT_set[A](rbt), DList_set[A](dxs)))).apply(())
                }
            case Some(_) =>
              RBT_set[A]((foldc[A, mapping_rbt[A,
        Unit]](((k: A) =>
                 ((a: mapping_rbt[A, Unit]) => insertb[A, Unit](k, (), a))),
                dxs)).apply(rbt))
          })
     })
  case (RBT_set(rbt1), RBT_set(rbt2)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("union RBT_set RBT_set: ccompare = None");
           (((_: Unit) =>
              sup_seta[A](RBT_set[A](rbt1), RBT_set[A](rbt2)))).apply(())
           }
       case Some(_) =>
         RBT_set[A](join[A, Unit](((_: A) => (_: Unit) => id[Unit]), rbt1,
                                   rbt2))
     })
}

def inf_seta[A : ceq : ccompare](g: set[A], ga: set[A]): set[A] = (g, ga) match
  {
  case (RBT_set(rbt1), Set_Monad(xs)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("inter RBT_set Set_Monad: ccompare = None");
           (((_: Unit) =>
              inf_seta[A](RBT_set[A](rbt1), Set_Monad[A](xs)))).apply(())
           }
       case Some(_) => RBT_set[A](inter_list[A](rbt1, xs))
     })
  case (RBT_set(rbt), DList_set(dxs)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("inter RBT_set DList_set: ccompare = None");
           (((_: Unit) =>
              inf_seta[A](RBT_set[A](rbt), DList_set[A](dxs)))).apply(())
           }
       case Some(_) =>
         (ceq[A] match {
            case None =>
              { sys.error("inter RBT_set DList_set: ceq = None");
                (((_: Unit) =>
                   inf_seta[A](RBT_set[A](rbt), DList_set[A](dxs)))).apply(())
                }
            case Some(_) =>
              RBT_set[A](inter_list[A](rbt, list_of_dlist[A](dxs)))
          })
     })
  case (RBT_set(rbt1), RBT_set(rbt2)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("inter RBT_set RBT_set: ccompare = None");
           (((_: Unit) =>
              inf_seta[A](RBT_set[A](rbt1), RBT_set[A](rbt2)))).apply(())
           }
       case Some(_) =>
         RBT_set[A](meet[A, Unit](((_: A) => (_: Unit) => id[Unit]), rbt1,
                                   rbt2))
     })
  case (DList_set(dxs1), Set_Monad(xs)) =>
    (ceq[A] match {
       case None =>
         { sys.error("inter DList_set Set_Monad: ceq = None");
           (((_: Unit) =>
              inf_seta[A](DList_set[A](dxs1), Set_Monad[A](xs)))).apply(())
           }
       case Some(eq) =>
         DList_set[A](filtera[A](((a: A) => list_member[A](eq, xs, a)), dxs1))
     })
  case (DList_set(dxs1), DList_set(dxs2)) =>
    (ceq[A] match {
       case None =>
         { sys.error("inter DList_set DList_set: ceq = None");
           (((_: Unit) =>
              inf_seta[A](DList_set[A](dxs1), DList_set[A](dxs2)))).apply(())
           }
       case Some(_) => DList_set[A](filtera[A](memberb[A](dxs2), dxs1))
     })
  case (DList_set(dxs), RBT_set(rbt)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("inter DList_set RBT_set: ccompare = None");
           (((_: Unit) =>
              inf_seta[A](DList_set[A](dxs), RBT_set[A](rbt)))).apply(())
           }
       case Some(_) =>
         (ceq[A] match {
            case None =>
              { sys.error("inter DList_set RBT_set: ceq = None");
                (((_: Unit) =>
                   inf_seta[A](DList_set[A](dxs), RBT_set[A](rbt)))).apply(())
                }
            case Some(_) =>
              RBT_set[A](inter_list[A](rbt, list_of_dlist[A](dxs)))
          })
     })
  case (Set_Monad(xs1), Set_Monad(xs2)) =>
    (ceq[A] match {
       case None =>
         { sys.error("inter Set_Monad Set_Monad: ceq = None");
           (((_: Unit) =>
              inf_seta[A](Set_Monad[A](xs1), Set_Monad[A](xs2)))).apply(())
           }
       case Some(eq) =>
         Set_Monad[A](filter[A](((a: A) => list_member[A](eq, xs2, a)), xs1))
     })
  case (Set_Monad(xs), DList_set(dxs2)) =>
    (ceq[A] match {
       case None =>
         { sys.error("inter Set_Monad DList_set: ceq = None");
           (((_: Unit) =>
              inf_seta[A](Set_Monad[A](xs), DList_set[A](dxs2)))).apply(())
           }
       case Some(eq) =>
         DList_set[A](filtera[A](((a: A) => list_member[A](eq, xs, a)), dxs2))
     })
  case (Set_Monad(xs), RBT_set(rbt1)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("inter Set_Monad RBT_set: ccompare = None");
           (((_: Unit) =>
              inf_seta[A](RBT_set[A](rbt1), Set_Monad[A](xs)))).apply(())
           }
       case Some(_) => RBT_set[A](inter_list[A](rbt1, xs))
     })
  case (Complement(ba), Complement(b)) => Complement[A](sup_seta[A](ba, b))
  case (g, RBT_set(rbt2)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("inter RBT_set2: ccompare = None");
           (((_: Unit) => inf_seta[A](g, RBT_set[A](rbt2)))).apply(()) }
       case Some(_) =>
         RBT_set[A](filterb[A, Unit](comp[A, Boolean,
   (A, Unit)](((x: A) => member[A](x, g)), ((a: (A, Unit)) => fst[A, Unit](a))),
                                      rbt2))
     })
  case (RBT_set(rbt1), g) =>
    (ccompare[A] match {
       case None =>
         { sys.error("inter RBT_set1: ccompare = None");
           (((_: Unit) => inf_seta[A](RBT_set[A](rbt1), g))).apply(()) }
       case Some(_) =>
         RBT_set[A](filterb[A, Unit](comp[A, Boolean,
   (A, Unit)](((x: A) => member[A](x, g)), ((a: (A, Unit)) => fst[A, Unit](a))),
                                      rbt1))
     })
  case (h, DList_set(dxs2)) =>
    (ceq[A] match {
       case None =>
         { sys.error("inter DList_set2: ceq = None");
           (((_: Unit) => inf_seta[A](h, DList_set[A](dxs2)))).apply(()) }
       case Some(_) =>
         DList_set[A](filtera[A](((x: A) => member[A](x, h)), dxs2))
     })
  case (DList_set(dxs1), h) =>
    (ceq[A] match {
       case None =>
         { sys.error("inter DList_set1: ceq = None");
           (((_: Unit) => inf_seta[A](DList_set[A](dxs1), h))).apply(()) }
       case Some(_) =>
         DList_set[A](filtera[A](((x: A) => member[A](x, h)), dxs1))
     })
  case (i, Set_Monad(xs)) =>
    Set_Monad[A](filter[A](((x: A) => member[A](x, i)), xs))
  case (Set_Monad(xs), i) =>
    Set_Monad[A](filter[A](((x: A) => member[A](x, i)), xs))
  case (j, Collect_set(a)) =>
    Collect_set[A](((x: A) => a(x) && member[A](x, j)))
  case (Collect_set(a), j) =>
    Collect_set[A](((x: A) => a(x) && member[A](x, j)))
}

trait inf[A] {
  val `PDDL_Checker_Exported.inf`: (A, A) => A
}
def inf[A](a: A, b: A)(implicit A: inf[A]): A =
  A.`PDDL_Checker_Exported.inf`(a, b)
object inf {
  implicit def `PDDL_Checker_Exported.inf_set`[A : ceq : ccompare]: inf[set[A]]
    = new inf[set[A]] {
    val `PDDL_Checker_Exported.inf` = (a: set[A], b: set[A]) =>
      inf_seta[A](a, b)
  }
}

trait sup[A] {
  val `PDDL_Checker_Exported.sup`: (A, A) => A
}
def sup[A](a: A, b: A)(implicit A: sup[A]): A =
  A.`PDDL_Checker_Exported.sup`(a, b)
object sup {
  implicit def `PDDL_Checker_Exported.sup_set`[A : ceq : ccompare]: sup[set[A]]
    = new sup[set[A]] {
    val `PDDL_Checker_Exported.sup` = (a: set[A], b: set[A]) =>
      sup_seta[A](a, b)
  }
}

def equal_order(x0: ordera, x1: ordera): Boolean = (x0, x1) match {
  case (Lt(), Gt()) => false
  case (Gt(), Lt()) => false
  case (Eq(), Gt()) => false
  case (Gt(), Eq()) => false
  case (Eq(), Lt()) => false
  case (Lt(), Eq()) => false
  case (Gt(), Gt()) => true
  case (Lt(), Lt()) => true
  case (Eq(), Eq()) => true
}

abstract sealed class generator[A, B]
final case class Generator[B, A](a: (B => Boolean, B => (A, B))) extends
  generator[A, B]

def generator[A, B](x0: generator[A, B]): (B => Boolean, B => (A, B)) = x0 match
  {
  case Generator(x) => x
}

def has_next[A, B](g: generator[A, B]): B => Boolean =
  fst[B => Boolean, B => (A, B)](generator[A, B](g))

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def next[A, B](g: generator[A, B]): B => (A, B) =
  snd[B => Boolean, B => (A, B)](generator[A, B](g))

def sorted_list_subset_fusion[A, B,
                               C](less: A => A => Boolean,
                                   eq: A => A => Boolean, g1: generator[A, B],
                                   g2: generator[A, C], s1: B, s2: C):
      Boolean
  =
  (if ((has_next[A, B](g1)).apply(s1))
    {
      val (x, s1a) = (next[A, B](g1)).apply(s1): ((A, B));
      (has_next[A, C](g2)).apply(s2) &&
        {
          val (y, s2a) = (next[A, C](g2)).apply(s2): ((A, C));
          (if ((eq(x))(y))
            sorted_list_subset_fusion[A, B, C](less, eq, g1, g2, s1a, s2a)
            else (less(y))(x) &&
                   sorted_list_subset_fusion[A, B,
      C](less, eq, g1, g2, s1, s2a))
        }
    }
    else true)

def list_all_fusion[A, B](g: generator[A, B], p: A => Boolean, s: B): Boolean =
  (if ((has_next[A, B](g)).apply(s))
    {
      val (x, sa) = (next[A, B](g)).apply(s): ((A, B));
      p(x) && list_all_fusion[A, B](g, p, sa)
    }
    else true)

def rbt_keys_next[A, B](x0: (List[(A, rbt[A, B])], rbt[A, B])):
      (A, (List[(A, rbt[A, B])], rbt[A, B]))
  =
  x0 match {
  case ((k, t) :: kts, Empty()) => (k, (kts, t))
  case (kts, Branch(c, l, k, v, r)) => rbt_keys_next[A, B](((k, r) :: kts, l))
}

def rbt_has_next[A, B, C](x0: (List[(A, rbt[B, C])], rbt[B, C])): Boolean = x0
  match {
  case (Nil, Empty()) => false
  case (vb :: vc, va) => true
  case (v, Branch(vb, vc, vd, ve, vf)) => true
}

def rbt_keys_generator[A, B]: generator[A, (List[(A, rbt[A, B])], rbt[A, B])] =
  Generator[(List[(A, rbt[A, B])], rbt[A, B]),
             A]((((a: (List[(A, rbt[A, B])], rbt[A, B])) =>
                   rbt_has_next[A, A, B](a)),
                  ((a: (List[(A, rbt[A, B])], rbt[A, B])) =>
                    rbt_keys_next[A, B](a))))

def lt_of_comp[A](acomp: A => A => ordera, x: A, y: A): Boolean =
  ((acomp(x))(y) match {
     case Eq() => false
     case Lt() => true
     case Gt() => false
   })

def list_all[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && list_all[A](p, xs)
}

def dlist_all[A : ceq](x: A => Boolean, xc: set_dlist[A]): Boolean =
  list_all[A](x, list_of_dlist[A](xc))

def rbt_init[A, B, C]: (rbt[A, B]) => (List[(C, rbt[A, B])], rbt[A, B]) =
  ((a: rbt[A, B]) => (Nil, a))

def init[A : ccompare, B, C](xa: mapping_rbt[A, B]):
      (List[(C, rbt[A, B])], rbt[A, B])
  =
  rbt_init[A, B, C].apply(impl_ofa[A, B](xa))

trait cenum[A] {
  val `PDDL_Checker_Exported.cEnum`:
        Option[(List[A],
                 ((A => Boolean) => Boolean, (A => Boolean) => Boolean))]
}
def cEnum[A](implicit A: cenum[A]):
      Option[(List[A], ((A => Boolean) => Boolean, (A => Boolean) => Boolean))]
  = A.`PDDL_Checker_Exported.cEnum`
object cenum {
}

def Collect[A : cenum](p: A => Boolean): set[A] =
  (cEnum[A] match {
     case None => Collect_set[A](p)
     case Some((enuma, _)) => Set_Monad[A](filter[A](p, enuma))
   })

def less_eq_set[A : cenum : ceq : ccompare](x0: set[A], c: set[A]): Boolean =
  (x0, c) match {
  case (RBT_set(rbt1), RBT_set(rbt2)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("subset RBT_set RBT_set: ccompare = None");
           (((_: Unit) =>
              less_eq_set[A](RBT_set[A](rbt1), RBT_set[A](rbt2)))).apply(())
           }
       case Some(c) =>
         (ceq[A] match {
            case None =>
              sorted_list_subset_fusion[A,
 (List[(A, rbt[A, Unit])], rbt[A, Unit]),
 (List[(A, rbt[A, Unit])],
   rbt[A, Unit])](((a: A) => (b: A) => lt_of_comp[A](c, a, b)),
                   ((x: A) => (y: A) => equal_order((c(x))(y), Eq())),
                   rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
                   init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
            case Some(eq) =>
              sorted_list_subset_fusion[A,
 (List[(A, rbt[A, Unit])], rbt[A, Unit]),
 (List[(A, rbt[A, Unit])],
   rbt[A, Unit])](((a: A) => (b: A) => lt_of_comp[A](c, a, b)), eq,
                   rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
                   init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
          })
     })
  case (Complement(a1), Complement(a2)) => less_eq_set[A](a2, a1)
  case (Collect_set(p), Complement(a)) =>
    less_eq_set[A](a, Collect[A](((x: A) => ! (p(x)))))
  case (Set_Monad(xs), c) => list_all[A](((x: A) => member[A](x, c)), xs)
  case (DList_set(dxs), c) =>
    (ceq[A] match {
       case None =>
         { sys.error("subset DList_set1: ceq = None");
           (((_: Unit) => less_eq_set[A](DList_set[A](dxs), c))).apply(()) }
       case Some(_) => dlist_all[A](((x: A) => member[A](x, c)), dxs)
     })
  case (RBT_set(rbt), b) =>
    (ccompare[A] match {
       case None =>
         { sys.error("subset RBT_set1: ccompare = None");
           (((_: Unit) => less_eq_set[A](RBT_set[A](rbt), b))).apply(()) }
       case Some(_) =>
         list_all_fusion[A, (List[(A, rbt[A, Unit])],
                              rbt[A, Unit])](rbt_keys_generator[A, Unit],
      ((x: A) => member[A](x, b)), init[A, Unit, A](rbt))
     })
}

def less_set[A : cenum : ceq : ccompare](a: set[A], b: set[A]): Boolean =
  less_eq_set[A](a, b) && ! (less_eq_set[A](b, a))

trait preorder[A] extends ord[A] {
}
object preorder {
  implicit def `PDDL_Checker_Exported.preorder_char`: preorder[char] = new
    preorder[char] {
    val `PDDL_Checker_Exported.less_eq` = (a: char, b: char) =>
      less_eq_char(a, b)
    val `PDDL_Checker_Exported.less` = (a: char, b: char) => less_char(a, b)
  }
  implicit def
    `PDDL_Checker_Exported.preorder_set`[A : cenum : ceq : ccompare]:
      preorder[set[A]]
    = new preorder[set[A]] {
    val `PDDL_Checker_Exported.less_eq` = (a: set[A], b: set[A]) =>
      less_eq_set[A](a, b)
    val `PDDL_Checker_Exported.less` = (a: set[A], b: set[A]) =>
      less_set[A](a, b)
  }
}

trait order[A] extends preorder[A] {
}
object order {
  implicit def `PDDL_Checker_Exported.order_char`: order[char] = new order[char]
    {
    val `PDDL_Checker_Exported.less_eq` = (a: char, b: char) =>
      less_eq_char(a, b)
    val `PDDL_Checker_Exported.less` = (a: char, b: char) => less_char(a, b)
  }
  implicit def
    `PDDL_Checker_Exported.order_set`[A : cenum : ceq : ccompare]: order[set[A]]
    = new order[set[A]] {
    val `PDDL_Checker_Exported.less_eq` = (a: set[A], b: set[A]) =>
      less_eq_set[A](a, b)
    val `PDDL_Checker_Exported.less` = (a: set[A], b: set[A]) =>
      less_set[A](a, b)
  }
}

trait semilattice_sup[A] extends sup[A] with order[A] {
}
object semilattice_sup {
  implicit def
    `PDDL_Checker_Exported.semilattice_sup_set`[A : cenum : ceq : ccompare]:
      semilattice_sup[set[A]]
    = new semilattice_sup[set[A]] {
    val `PDDL_Checker_Exported.less_eq` = (a: set[A], b: set[A]) =>
      less_eq_set[A](a, b)
    val `PDDL_Checker_Exported.less` = (a: set[A], b: set[A]) =>
      less_set[A](a, b)
    val `PDDL_Checker_Exported.sup` = (a: set[A], b: set[A]) =>
      sup_seta[A](a, b)
  }
}

trait semilattice_inf[A] extends inf[A] with order[A] {
}
object semilattice_inf {
  implicit def
    `PDDL_Checker_Exported.semilattice_inf_set`[A : cenum : ceq : ccompare]:
      semilattice_inf[set[A]]
    = new semilattice_inf[set[A]] {
    val `PDDL_Checker_Exported.less_eq` = (a: set[A], b: set[A]) =>
      less_eq_set[A](a, b)
    val `PDDL_Checker_Exported.less` = (a: set[A], b: set[A]) =>
      less_set[A](a, b)
    val `PDDL_Checker_Exported.inf` = (a: set[A], b: set[A]) =>
      inf_seta[A](a, b)
  }
}

trait lattice[A] extends semilattice_inf[A] with semilattice_sup[A] {
}
object lattice {
  implicit def
    `PDDL_Checker_Exported.lattice_set`[A : cenum : ceq : ccompare]:
      lattice[set[A]]
    = new lattice[set[A]] {
    val `PDDL_Checker_Exported.sup` = (a: set[A], b: set[A]) =>
      sup_seta[A](a, b)
    val `PDDL_Checker_Exported.inf` = (a: set[A], b: set[A]) =>
      inf_seta[A](a, b)
    val `PDDL_Checker_Exported.less_eq` = (a: set[A], b: set[A]) =>
      less_eq_set[A](a, b)
    val `PDDL_Checker_Exported.less` = (a: set[A], b: set[A]) =>
      less_set[A](a, b)
  }
}

def list_all2_fusion[A, B, C,
                      D](p: A => B => Boolean, g1: generator[A, C],
                          g2: generator[B, D], s1: C, s2: D):
      Boolean
  =
  (if ((has_next[A, C](g1)).apply(s1))
    (has_next[B, D](g2)).apply(s2) &&
      {
        val (x, s1a) = (next[A, C](g1)).apply(s1): ((A, C))
        val (y, s2a) = (next[B, D](g2)).apply(s2): ((B, D));
        (p(x))(y) && list_all2_fusion[A, B, C, D](p, g1, g2, s1a, s2a)
      }
    else ! (has_next[B, D](g2)).apply(s2))

def set_eq[A : cenum : ceq : ccompare](a: set[A], b: set[A]): Boolean = (a, b)
  match {
  case (RBT_set(rbt1), RBT_set(rbt2)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("set_eq RBT_set RBT_set: ccompare = None");
           (((_: Unit) =>
              set_eq[A](RBT_set[A](rbt1), RBT_set[A](rbt2)))).apply(())
           }
       case Some(c) =>
         (ceq[A] match {
            case None =>
              list_all2_fusion[A, A, (List[(A, rbt[A, Unit])], rbt[A, Unit]),
                                (List[(A, rbt[A, Unit])],
                                  rbt[A, Unit])](((x: A) => (y: A) =>
           equal_order((c(x))(y), Eq())),
          rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
          init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
            case Some(eq) =>
              list_all2_fusion[A, A, (List[(A, rbt[A, Unit])], rbt[A, Unit]),
                                (List[(A, rbt[A, Unit])],
                                  rbt[A, Unit])](eq,
          rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
          init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
          })
     })
  case (Complement(a), Complement(b)) => set_eq[A](a, b)
  case (a, b) => less_eq_set[A](a, b) && less_eq_set[A](b, a)
}

def ceq_seta[A : cenum : ceq : ccompare]:
      Option[(set[A]) => (set[A]) => Boolean]
  =
  (ceq[A] match {
     case None => None
     case Some(_) =>
       Some[(set[A]) =>
              (set[A]) =>
                Boolean](((a: set[A]) => (b: set[A]) => set_eq[A](a, b)))
   })

abstract sealed class phantom[A, B]
final case class phantoma[B, A](a: B) extends phantom[A, B]

abstract sealed class set_impla
final case class set_Choose() extends set_impla
final case class set_Collect() extends set_impla
final case class set_DList() extends set_impla
final case class set_RBT() extends set_impla
final case class set_Monad() extends set_impla

def set_impl_seta[A]: phantom[set[A], set_impla] =
  phantoma[set_impla, set[A]](set_Choose())

trait set_impl[A] {
  val `PDDL_Checker_Exported.set_impl`: phantom[A, set_impla]
}
def set_impl[A](implicit A: set_impl[A]): phantom[A, set_impla] =
  A.`PDDL_Checker_Exported.set_impl`
object set_impl {
  implicit def `PDDL_Checker_Exported.set_impl_term`[A]: set_impl[term[A]] = new
    set_impl[term[A]] {
    val `PDDL_Checker_Exported.set_impl` = set_impl_terma[A]
  }
  implicit def `PDDL_Checker_Exported.set_impl_list`[A]: set_impl[List[A]] = new
    set_impl[List[A]] {
    val `PDDL_Checker_Exported.set_impl` = set_impl_lista[A]
  }
  implicit def `PDDL_Checker_Exported.set_impl_set`[A]: set_impl[set[A]] = new
    set_impl[set[A]] {
    val `PDDL_Checker_Exported.set_impl` = set_impl_seta[A]
  }
}

trait finite_UNIV[A] {
  val `PDDL_Checker_Exported.finite_UNIV`: phantom[A, Boolean]
}
def finite_UNIV[A](implicit A: finite_UNIV[A]): phantom[A, Boolean] =
  A.`PDDL_Checker_Exported.finite_UNIV`
object finite_UNIV {
  implicit def
    `PDDL_Checker_Exported.finite_UNIV_set`[A : finite_UNIV]:
      finite_UNIV[set[A]]
    = new finite_UNIV[set[A]] {
    val `PDDL_Checker_Exported.finite_UNIV` = finite_UNIV_seta[A]
  }
}

def of_phantom[A, B](x0: phantom[A, B]): B = x0 match {
  case phantoma(x) => x
}

def finite_UNIV_seta[A : finite_UNIV]: phantom[set[A], Boolean] =
  phantoma[Boolean, set[A]](of_phantom[A, Boolean](finite_UNIV[A]))

trait cproper_interval[A] extends ccompare[A] {
  val `PDDL_Checker_Exported.cproper_interval`:
        (Option[A], Option[A]) => Boolean
}
def cproper_interval[A](a: Option[A],
                         b: Option[A])(implicit A: cproper_interval[A]):
      Boolean
  = A.`PDDL_Checker_Exported.cproper_interval`(a, b)
object cproper_interval {
}

def set_less_eq_aux_Compl_fusion[A, B,
                                  C](less: A => A => Boolean,
                                      proper_interval:
Option[A] => Option[A] => Boolean,
                                      g1: generator[A, B], g2: generator[A, C],
                                      ao: Option[A], s1: B, s2: C):
      Boolean
  =
  (if ((has_next[A, B](g1)).apply(s1))
    (if ((has_next[A, C](g2)).apply(s2))
      {
        val (x, s1a) = (next[A, B](g1)).apply(s1): ((A, B))
        val (y, s2a) = (next[A, C](g2)).apply(s2): ((A, C));
        (if ((less(x))(y))
          (proper_interval(ao))(Some[A](x)) ||
            set_less_eq_aux_Compl_fusion[A, B,
  C](less, proper_interval, g1, g2, Some[A](x), s1a, s2)
          else (if ((less(y))(x))
                 (proper_interval(ao))(Some[A](y)) ||
                   set_less_eq_aux_Compl_fusion[A, B,
         C](less, proper_interval, g1, g2, Some[A](y), s1, s2a)
                 else (proper_interval(ao))(Some[A](y))))
      }
      else true)
    else true)

def Compl_set_less_eq_aux_fusion[A, B,
                                  C](less: A => A => Boolean,
                                      proper_interval:
Option[A] => Option[A] => Boolean,
                                      g1: generator[A, B], g2: generator[A, C],
                                      ao: Option[A], s1: B, s2: C):
      Boolean
  =
  (if ((has_next[A, B](g1)).apply(s1))
    {
      val (x, s1a) = (next[A, B](g1)).apply(s1): ((A, B));
      (if ((has_next[A, C](g2)).apply(s2))
        {
          val (y, s2a) = (next[A, C](g2)).apply(s2): ((A, C));
          (if ((less(x))(y))
            ! ((proper_interval(ao))(Some[A](x))) &&
              Compl_set_less_eq_aux_fusion[A, B,
    C](less, proper_interval, g1, g2, Some[A](x), s1a, s2)
            else (if ((less(y))(x))
                   ! ((proper_interval(ao))(Some[A](y))) &&
                     Compl_set_less_eq_aux_fusion[A, B,
           C](less, proper_interval, g1, g2, Some[A](y), s1, s2a)
                   else ! ((proper_interval(ao))(Some[A](y)))))
        }
        else ! ((proper_interval(ao))(Some[A](x))) &&
               Compl_set_less_eq_aux_fusion[A, B,
     C](less, proper_interval, g1, g2, Some[A](x), s1a, s2))
    }
    else (if ((has_next[A, C](g2)).apply(s2))
           {
             val (y, s2a) = (next[A, C](g2)).apply(s2): ((A, C));
             ! ((proper_interval(ao))(Some[A](y))) &&
               Compl_set_less_eq_aux_fusion[A, B,
     C](less, proper_interval, g1, g2, Some[A](y), s1, s2a)
           }
           else ! ((proper_interval(ao))(None))))

def set_less_eq_aux_Compl[A](less: A => A => Boolean,
                              proper_interval:
                                Option[A] => Option[A] => Boolean,
                              ao: Option[A], xs: List[A], ys: List[A]):
      Boolean
  =
  (less, proper_interval, ao, xs, ys) match {
  case (less, proper_interval, ao, x :: xs, y :: ys) =>
    (if ((less(x))(y))
      (proper_interval(ao))(Some[A](x)) ||
        set_less_eq_aux_Compl[A](less, proper_interval, Some[A](x), xs, y :: ys)
      else (if ((less(y))(x))
             (proper_interval(ao))(Some[A](y)) ||
               set_less_eq_aux_Compl[A](less, proper_interval, Some[A](y),
 x :: xs, ys)
             else (proper_interval(ao))(Some[A](y))))
  case (less, proper_interval, ao, xs, Nil) => true
  case (less, proper_interval, ao, Nil, ys) => true
}

def Compl_set_less_eq_aux[A](less: A => A => Boolean,
                              proper_interval:
                                Option[A] => Option[A] => Boolean,
                              ao: Option[A], x3: List[A], x4: List[A]):
      Boolean
  =
  (less, proper_interval, ao, x3, x4) match {
  case (less, proper_interval, ao, x :: xs, y :: ys) =>
    (if ((less(x))(y))
      ! ((proper_interval(ao))(Some[A](x))) &&
        Compl_set_less_eq_aux[A](less, proper_interval, Some[A](x), xs, y :: ys)
      else (if ((less(y))(x))
             ! ((proper_interval(ao))(Some[A](y))) &&
               Compl_set_less_eq_aux[A](less, proper_interval, Some[A](y),
 x :: xs, ys)
             else ! ((proper_interval(ao))(Some[A](y)))))
  case (less, proper_interval, ao, x :: xs, Nil) =>
    ! ((proper_interval(ao))(Some[A](x))) &&
      Compl_set_less_eq_aux[A](less, proper_interval, Some[A](x), xs, Nil)
  case (less, proper_interval, ao, Nil, y :: ys) =>
    ! ((proper_interval(ao))(Some[A](y))) &&
      Compl_set_less_eq_aux[A](less, proper_interval, Some[A](y), Nil, ys)
  case (less, proper_interval, ao, Nil, Nil) => ! ((proper_interval(ao))(None))
}

def lexord_eq_fusion[A, B,
                      C](less: A => A => Boolean, g1: generator[A, B],
                          g2: generator[A, C], s1: B, s2: C):
      Boolean
  =
  (if ((has_next[A, B](g1)).apply(s1))
    (has_next[A, C](g2)).apply(s2) &&
      {
        val (x, s1a) = (next[A, B](g1)).apply(s1): ((A, B))
        val (y, s2a) = (next[A, C](g2)).apply(s2): ((A, C));
        (less(x))(y) ||
          ! ((less(y))(x)) && lexord_eq_fusion[A, B, C](less, g1, g2, s1a, s2a)
      }
    else true)

def remdups_sorted[A](less: A => A => Boolean, x1: List[A]): List[A] =
  (less, x1) match {
  case (less, x :: y :: xs) =>
    (if ((less(x))(y)) x :: remdups_sorted[A](less, y :: xs)
      else remdups_sorted[A](less, y :: xs))
  case (less, List(x)) => List(x)
  case (less, Nil) => Nil
}

def quicksort_part[A](less: A => A => Boolean, ac: List[A], x: A, lts: List[A],
                       eqs: List[A], gts: List[A], xa6: List[A]):
      List[A]
  =
  (less, ac, x, lts, eqs, gts, xa6) match {
  case (less, ac, x, lts, eqs, gts, z :: zs) =>
    (if ((less(x))(z)) quicksort_part[A](less, ac, x, lts, eqs, z :: gts, zs)
      else (if ((less(z))(x))
             quicksort_part[A](less, ac, x, z :: lts, eqs, gts, zs)
             else quicksort_part[A](less, ac, x, lts, z :: eqs, gts, zs)))
  case (less, ac, x, lts, eqs, gts, Nil) =>
    quicksort_acc[A](less, eqs ++ (x :: quicksort_acc[A](less, ac, gts)), lts)
}

def quicksort_acc[A](less: A => A => Boolean, ac: List[A], x2: List[A]): List[A]
  =
  (less, ac, x2) match {
  case (less, ac, x :: v :: va) =>
    quicksort_part[A](less, ac, x, Nil, Nil, Nil, v :: va)
  case (less, ac, List(x)) => x :: ac
  case (less, ac, Nil) => ac
}

def quicksort[A](less: A => A => Boolean): (List[A]) => List[A] =
  ((a: List[A]) => quicksort_acc[A](less, Nil, a))

def gen_keys[A, B](kts: List[(A, rbt[A, B])], x1: rbt[A, B]): List[A] =
  (kts, x1) match {
  case (kts, Branch(c, l, k, v, r)) => gen_keys[A, B]((k, r) :: kts, l)
  case ((k, t) :: kts, Empty()) => k :: gen_keys[A, B](kts, t)
  case (Nil, Empty()) => Nil
}

def keys[A, B]: (rbt[A, B]) => List[A] =
  ((a: rbt[A, B]) => gen_keys[A, B](Nil, a))

def keysa[A : ccompare](xa: mapping_rbt[A, Unit]): List[A] =
  keys[A, Unit].apply(impl_ofa[A, Unit](xa))

def csorted_list_of_set[A : ceq : ccompare](x0: set[A]): List[A] = x0 match {
  case Set_Monad(xs) =>
    (ccompare[A] match {
       case None =>
         { sys.error("csorted_list_of_set Set_Monad: ccompare = None");
           (((_: Unit) => csorted_list_of_set[A](Set_Monad[A](xs)))).apply(()) }
       case Some(c) =>
         remdups_sorted[A](((a: A) => (b: A) => lt_of_comp[A](c, a, b)),
                            (quicksort[A](((a: A) => (b: A) =>
    lt_of_comp[A](c, a, b)))).apply(xs))
     })
  case DList_set(dxs) =>
    (ceq[A] match {
       case None =>
         { sys.error("csorted_list_of_set DList_set: ceq = None");
           (((_: Unit) => csorted_list_of_set[A](DList_set[A](dxs)))).apply(())
           }
       case Some(_) =>
         (ccompare[A] match {
            case None =>
              { sys.error("csorted_list_of_set DList_set: ccompare = None");
                (((_: Unit) =>
                   csorted_list_of_set[A](DList_set[A](dxs)))).apply(())
                }
            case Some(c) =>
              (quicksort[A](((a: A) => (b: A) =>
                              lt_of_comp[A](c, a,
     b)))).apply(list_of_dlist[A](dxs))
          })
     })
  case RBT_set(rbt) =>
    (ccompare[A] match {
       case None =>
         { sys.error("csorted_list_of_set RBT_set: ccompare = None");
           (((_: Unit) => csorted_list_of_set[A](RBT_set[A](rbt)))).apply(()) }
       case Some(_) => keysa[A](rbt)
     })
}

def emptyc[A : ccompare, B]: mapping_rbt[A, B] =
  Mapping_RBT[A, B](Empty[A, B]())

def emptyb[A : ceq]: set_dlist[A] = Abs_dlist[A](Nil)

def set_empty_choose[A : ceq : ccompare]: set[A] =
  (ccompare[A] match {
     case None => (ceq[A] match {
                     case None => Set_Monad[A](Nil)
                     case Some(_) => DList_set[A](emptyb[A])
                   })
     case Some(_) => RBT_set[A](emptyc[A, Unit])
   })

def set_empty[A : ceq : ccompare](x0: set_impla): set[A] = x0 match {
  case set_Choose() => set_empty_choose[A]
  case set_Monad() => Set_Monad[A](Nil)
  case set_RBT() => RBT_set[A](emptyc[A, Unit])
  case set_DList() => DList_set[A](emptyb[A])
  case set_Collect() => Collect_set[A](((_: A) => false))
}

def bot_set[A : ceq : ccompare : set_impl]: set[A] =
  set_empty[A](of_phantom[A, set_impla](set_impl[A]))

def top_set[A : ceq : ccompare : set_impl]: set[A] = uminus_set[A](bot_set[A])

def le_of_comp[A](acomp: A => A => ordera, x: A, y: A): Boolean =
  ((acomp(x))(y) match {
     case Eq() => true
     case Lt() => true
     case Gt() => false
   })

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def lexordp_eq[A](less: A => A => Boolean, xs: List[A], ys: List[A]): Boolean =
  (less, xs, ys) match {
  case (less, x :: xs, y :: ys) =>
    (less(x))(y) || ! ((less(y))(x)) && lexordp_eq[A](less, xs, ys)
  case (less, x :: xs, Nil) => false
  case (less, xs, Nil) => nulla[A](xs)
  case (less, Nil, ys) => true
}

def finite[A : finite_UNIV : ceq : ccompare](x0: set[A]): Boolean = x0 match {
  case Collect_set(p) =>
    of_phantom[A, Boolean](finite_UNIV[A]) ||
      { sys.error("finite Collect_set");
        (((_: Unit) => finite[A](Collect_set[A](p)))).apply(()) }
  case Set_Monad(xs) => true
  case Complement(a) =>
    (if (of_phantom[A, Boolean](finite_UNIV[A])) true
      else (if (finite[A](a)) false
             else { sys.error("finite Complement: infinite set");
                    (((_: Unit) => finite[A](Complement[A](a)))).apply(()) }))
  case RBT_set(rbt) =>
    (ccompare[A] match {
       case None =>
         { sys.error("finite RBT_set: ccompare = None");
           (((_: Unit) => finite[A](RBT_set[A](rbt)))).apply(()) }
       case Some(_) => true
     })
  case DList_set(dxs) =>
    (ceq[A] match {
       case None =>
         { sys.error("finite DList_set: ceq = None");
           (((_: Unit) => finite[A](DList_set[A](dxs)))).apply(()) }
       case Some(_) => true
     })
}

def set_less_aux_Compl_fusion[A, B,
                               C](less: A => A => Boolean,
                                   proper_interval:
                                     Option[A] => Option[A] => Boolean,
                                   g1: generator[A, B], g2: generator[A, C],
                                   ao: Option[A], s1: B, s2: C):
      Boolean
  =
  (if ((has_next[A, B](g1)).apply(s1))
    {
      val (x, s1a) = (next[A, B](g1)).apply(s1): ((A, B));
      (if ((has_next[A, C](g2)).apply(s2))
        {
          val (y, s2a) = (next[A, C](g2)).apply(s2): ((A, C));
          (if ((less(x))(y))
            (proper_interval(ao))(Some[A](x)) ||
              set_less_aux_Compl_fusion[A, B,
 C](less, proper_interval, g1, g2, Some[A](x), s1a, s2)
            else (if ((less(y))(x))
                   (proper_interval(ao))(Some[A](y)) ||
                     set_less_aux_Compl_fusion[A, B,
        C](less, proper_interval, g1, g2, Some[A](y), s1, s2a)
                   else (proper_interval(ao))(Some[A](y))))
        }
        else (proper_interval(ao))(Some[A](x)) ||
               set_less_aux_Compl_fusion[A, B,
  C](less, proper_interval, g1, g2, Some[A](x), s1a, s2))
    }
    else (if ((has_next[A, C](g2)).apply(s2))
           {
             val (y, s2a) = (next[A, C](g2)).apply(s2): ((A, C));
             (proper_interval(ao))(Some[A](y)) ||
               set_less_aux_Compl_fusion[A, B,
  C](less, proper_interval, g1, g2, Some[A](y), s1, s2a)
           }
           else (proper_interval(ao))(None)))

def Compl_set_less_aux_fusion[A, B,
                               C](less: A => A => Boolean,
                                   proper_interval:
                                     Option[A] => Option[A] => Boolean,
                                   g1: generator[A, B], g2: generator[A, C],
                                   ao: Option[A], s1: B, s2: C):
      Boolean
  =
  (has_next[A, B](g1)).apply(s1) &&
    ((has_next[A, C](g2)).apply(s2) &&
      {
        val (x, s1a) = (next[A, B](g1)).apply(s1): ((A, B))
        val (y, s2a) = (next[A, C](g2)).apply(s2): ((A, C));
        (if ((less(x))(y))
          ! ((proper_interval(ao))(Some[A](x))) &&
            Compl_set_less_aux_fusion[A, B,
                                       C](less, proper_interval, g1, g2,
   Some[A](x), s1a, s2)
          else (if ((less(y))(x))
                 ! ((proper_interval(ao))(Some[A](y))) &&
                   Compl_set_less_aux_fusion[A, B,
      C](less, proper_interval, g1, g2, Some[A](y), s1, s2a)
                 else ! ((proper_interval(ao))(Some[A](y)))))
      })

def set_less_aux_Compl[A](less: A => A => Boolean,
                           proper_interval: Option[A] => Option[A] => Boolean,
                           ao: Option[A], x3: List[A], x4: List[A]):
      Boolean
  =
  (less, proper_interval, ao, x3, x4) match {
  case (less, proper_interval, ao, x :: xs, y :: ys) =>
    (if ((less(x))(y))
      (proper_interval(ao))(Some[A](x)) ||
        set_less_aux_Compl[A](less, proper_interval, Some[A](x), xs, y :: ys)
      else (if ((less(y))(x))
             (proper_interval(ao))(Some[A](y)) ||
               set_less_aux_Compl[A](less, proper_interval, Some[A](y), x :: xs,
                                      ys)
             else (proper_interval(ao))(Some[A](y))))
  case (less, proper_interval, ao, x :: xs, Nil) =>
    (proper_interval(ao))(Some[A](x)) ||
      set_less_aux_Compl[A](less, proper_interval, Some[A](x), xs, Nil)
  case (less, proper_interval, ao, Nil, y :: ys) =>
    (proper_interval(ao))(Some[A](y)) ||
      set_less_aux_Compl[A](less, proper_interval, Some[A](y), Nil, ys)
  case (less, proper_interval, ao, Nil, Nil) => (proper_interval(ao))(None)
}

def Compl_set_less_aux[A](less: A => A => Boolean,
                           proper_interval: Option[A] => Option[A] => Boolean,
                           ao: Option[A], xs: List[A], ys: List[A]):
      Boolean
  =
  (less, proper_interval, ao, xs, ys) match {
  case (less, proper_interval, ao, x :: xs, y :: ys) =>
    (if ((less(x))(y))
      ! ((proper_interval(ao))(Some[A](x))) &&
        Compl_set_less_aux[A](less, proper_interval, Some[A](x), xs, y :: ys)
      else (if ((less(y))(x))
             ! ((proper_interval(ao))(Some[A](y))) &&
               Compl_set_less_aux[A](less, proper_interval, Some[A](y), x :: xs,
                                      ys)
             else ! ((proper_interval(ao))(Some[A](y)))))
  case (less, proper_interval, ao, xs, Nil) => false
  case (less, proper_interval, ao, Nil, ys) => false
}

def lexord_fusion[A, B,
                   C](less: A => A => Boolean, g1: generator[A, B],
                       g2: generator[A, C], s1: B, s2: C):
      Boolean
  =
  (if ((has_next[A, B](g1)).apply(s1))
    (if ((has_next[A, C](g2)).apply(s2))
      {
        val (x, s1a) = (next[A, B](g1)).apply(s1): ((A, B))
        val (y, s2a) = (next[A, C](g2)).apply(s2): ((A, C));
        (less(x))(y) ||
          ! ((less(y))(x)) && lexord_fusion[A, B, C](less, g1, g2, s1a, s2a)
      }
      else false)
    else (has_next[A, C](g2)).apply(s2))

def lexordp[A](less: A => A => Boolean, xs: List[A], ys: List[A]): Boolean =
  (less, xs, ys) match {
  case (less, x :: xs, y :: ys) =>
    (less(x))(y) || ! ((less(y))(x)) && lexordp[A](less, xs, ys)
  case (less, xs, Nil) => false
  case (less, Nil, ys) => ! (nulla[A](ys))
}

def comp_of_ords[A](le: A => A => Boolean, lt: A => A => Boolean, x: A, y: A):
      ordera
  =
  (if ((lt(x))(y)) Lt() else (if ((le(x))(y)) Eq() else Gt()))

def cless_eq_set[A : finite_UNIV : ceq : cproper_interval : set_impl](a: set[A],
                               b: set[A]):
      Boolean
  =
  (a, b) match {
  case (Complement(RBT_set(rbt1)), RBT_set(rbt2)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_eq_set (Complement RBT_set) RBT_set: ccompare = None");
           (((_: Unit) =>
              cless_eq_set[A](Complement[A](RBT_set[A](rbt1)),
                               RBT_set[A](rbt2)))).apply(())
           }
       case Some(c) =>
         finite[A](top_set[A]) &&
           Compl_set_less_eq_aux_fusion[A,
 (List[(A, rbt[A, Unit])], rbt[A, Unit]),
 (List[(A, rbt[A, Unit])],
   rbt[A, Unit])](((a: A) => (b: A) => lt_of_comp[A](c, a, b)),
                   ((a: Option[A]) => (b: Option[A]) =>
                     cproper_interval[A](a, b)),
                   rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
                   None, init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
     })
  case (RBT_set(rbt1), Complement(RBT_set(rbt2))) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_eq_set RBT_set (Complement RBT_set): ccompare = None");
           (((_: Unit) =>
              cless_eq_set[A](RBT_set[A](rbt1),
                               Complement[A](RBT_set[A](rbt2))))).apply(())
           }
       case Some(c) =>
         (if (finite[A](top_set[A]))
           set_less_eq_aux_Compl_fusion[A,
 (List[(A, rbt[A, Unit])], rbt[A, Unit]),
 (List[(A, rbt[A, Unit])],
   rbt[A, Unit])](((a: A) => (b: A) => lt_of_comp[A](c, a, b)),
                   ((a: Option[A]) => (b: Option[A]) =>
                     cproper_interval[A](a, b)),
                   rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
                   None, init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
           else true)
     })
  case (RBT_set(rbta), RBT_set(rbt)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_eq_set RBT_set RBT_set: ccompare = None");
           (((_: Unit) =>
              cless_eq_set[A](RBT_set[A](rbta), RBT_set[A](rbt)))).apply(())
           }
       case Some(c) =>
         lexord_eq_fusion[A, (List[(A, rbt[A, Unit])], rbt[A, Unit]),
                           (List[(A, rbt[A, Unit])],
                             rbt[A, Unit])](((x: A) => (y: A) =>
      lt_of_comp[A](c, y, x)),
     rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
     init[A, Unit, A](rbta), init[A, Unit, A](rbt))
     })
  case (Complement(a), Complement(b)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_eq_set Complement Complement: ccompare = None");
           (((_: Unit) =>
              le_of_comp[set[A]](the[(set[A]) =>
                                       (set[A]) => ordera](ccompare_seta[A]),
                                  Complement[A](a),
                                  Complement[A](b)))).apply(())
           }
       case Some(_) => cless_eq_set[A](b, a)
     })
  case (Complement(a), b) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_eq_set Complement1: ccompare = None");
           (((_: Unit) => cless_eq_set[A](Complement[A](a), b))).apply(()) }
       case Some(c) =>
         (if (finite[A](a) && finite[A](b))
           finite[A](top_set[A]) &&
             Compl_set_less_eq_aux[A](((aa: A) => (ba: A) =>
lt_of_comp[A](c, aa, ba)),
                                       ((aa: Option[A]) => (ba: Option[A]) =>
 cproper_interval[A](aa, ba)),
                                       None, csorted_list_of_set[A](a),
                                       csorted_list_of_set[A](b))
           else { sys.error("cless_eq_set Complement1: infinite set");
                  (((_: Unit) =>
                     cless_eq_set[A](Complement[A](a), b))).apply(())
                  })
     })
  case (a, Complement(b)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_eq_set Complement2: ccompare = None");
           (((_: Unit) => cless_eq_set[A](a, Complement[A](b)))).apply(()) }
       case Some(c) =>
         (if (finite[A](a) && finite[A](b))
           (if (finite[A](top_set[A]))
             set_less_eq_aux_Compl[A](((aa: A) => (ba: A) =>
lt_of_comp[A](c, aa, ba)),
                                       ((aa: Option[A]) => (ba: Option[A]) =>
 cproper_interval[A](aa, ba)),
                                       None, csorted_list_of_set[A](a),
                                       csorted_list_of_set[A](b))
             else true)
           else { sys.error("cless_eq_set Complement2: infinite set");
                  (((_: Unit) =>
                     cless_eq_set[A](a, Complement[A](b)))).apply(())
                  })
     })
  case (a, b) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_eq_set: ccompare = None");
           (((_: Unit) => cless_eq_set[A](a, b))).apply(()) }
       case Some(c) =>
         (if (finite[A](a) && finite[A](b))
           lexordp_eq[A](((x: A) => (y: A) => lt_of_comp[A](c, y, x)),
                          csorted_list_of_set[A](a), csorted_list_of_set[A](b))
           else { sys.error("cless_eq_set: infinite set");
                  (((_: Unit) => cless_eq_set[A](a, b))).apply(()) })
     })
}

def cless_set[A : finite_UNIV : ceq : cproper_interval : set_impl](a: set[A],
                            b: set[A]):
      Boolean
  =
  (a, b) match {
  case (Complement(RBT_set(rbt1)), RBT_set(rbt2)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_set (Complement RBT_set) RBT_set: ccompare = None");
           (((_: Unit) =>
              cless_set[A](Complement[A](RBT_set[A](rbt1)),
                            RBT_set[A](rbt2)))).apply(())
           }
       case Some(c) =>
         finite[A](top_set[A]) &&
           Compl_set_less_aux_fusion[A, (List[(A, rbt[A, Unit])], rbt[A, Unit]),
                                      (List[(A, rbt[A, Unit])],
rbt[A, Unit])](((a: A) => (b: A) => lt_of_comp[A](c, a, b)),
                ((a: Option[A]) => (b: Option[A]) => cproper_interval[A](a, b)),
                rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit], None,
                init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
     })
  case (RBT_set(rbt1), Complement(RBT_set(rbt2))) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_set RBT_set (Complement RBT_set): ccompare = None");
           (((_: Unit) =>
              cless_set[A](RBT_set[A](rbt1),
                            Complement[A](RBT_set[A](rbt2))))).apply(())
           }
       case Some(c) =>
         (if (finite[A](top_set[A]))
           set_less_aux_Compl_fusion[A, (List[(A, rbt[A, Unit])], rbt[A, Unit]),
                                      (List[(A, rbt[A, Unit])],
rbt[A, Unit])](((a: A) => (b: A) => lt_of_comp[A](c, a, b)),
                ((a: Option[A]) => (b: Option[A]) => cproper_interval[A](a, b)),
                rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit], None,
                init[A, Unit, A](rbt1), init[A, Unit, A](rbt2))
           else true)
     })
  case (RBT_set(rbta), RBT_set(rbt)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_set RBT_set RBT_set: ccompare = None");
           (((_: Unit) =>
              cless_set[A](RBT_set[A](rbta), RBT_set[A](rbt)))).apply(())
           }
       case Some(c) =>
         lexord_fusion[A, (List[(A, rbt[A, Unit])], rbt[A, Unit]),
                        (List[(A, rbt[A, Unit])],
                          rbt[A, Unit])](((x: A) => (y: A) =>
   lt_of_comp[A](c, y, x)),
  rbt_keys_generator[A, Unit], rbt_keys_generator[A, Unit],
  init[A, Unit, A](rbta), init[A, Unit, A](rbt))
     })
  case (Complement(a), Complement(b)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_set Complement Complement: ccompare = None");
           (((_: Unit) =>
              cless_set[A](Complement[A](a), Complement[A](b)))).apply(())
           }
       case Some(_) =>
         lt_of_comp[set[A]](the[(set[A]) =>
                                  (set[A]) => ordera](ccompare_seta[A]),
                             b, a)
     })
  case (Complement(a), b) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_set Complement1: ccompare = None");
           (((_: Unit) => cless_set[A](Complement[A](a), b))).apply(()) }
       case Some(c) =>
         (if (finite[A](a) && finite[A](b))
           finite[A](top_set[A]) &&
             Compl_set_less_aux[A](((aa: A) => (ba: A) =>
                                     lt_of_comp[A](c, aa, ba)),
                                    ((aa: Option[A]) => (ba: Option[A]) =>
                                      cproper_interval[A](aa, ba)),
                                    None, csorted_list_of_set[A](a),
                                    csorted_list_of_set[A](b))
           else { sys.error("cless_set Complement1: infinite set");
                  (((_: Unit) => cless_set[A](Complement[A](a), b))).apply(())
                  })
     })
  case (a, Complement(b)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_set Complement2: ccompare = None");
           (((_: Unit) => cless_set[A](a, Complement[A](b)))).apply(()) }
       case Some(c) =>
         (if (finite[A](a) && finite[A](b))
           (if (finite[A](top_set[A]))
             set_less_aux_Compl[A](((aa: A) => (ba: A) =>
                                     lt_of_comp[A](c, aa, ba)),
                                    ((aa: Option[A]) => (ba: Option[A]) =>
                                      cproper_interval[A](aa, ba)),
                                    None, csorted_list_of_set[A](a),
                                    csorted_list_of_set[A](b))
             else true)
           else { sys.error("cless_set Complement2: infinite set");
                  (((_: Unit) => cless_set[A](a, Complement[A](b)))).apply(())
                  })
     })
  case (a, b) =>
    (ccompare[A] match {
       case None =>
         { sys.error("cless_set: ccompare = None");
           (((_: Unit) => cless_set[A](a, b))).apply(()) }
       case Some(c) =>
         (if (finite[A](a) && finite[A](b))
           lexordp[A](((x: A) => (y: A) => lt_of_comp[A](c, y, x)),
                       csorted_list_of_set[A](a), csorted_list_of_set[A](b))
           else { sys.error("cless_set: infinite set");
                  (((_: Unit) => cless_set[A](a, b))).apply(()) })
     })
}

def ccompare_seta[A : finite_UNIV : ceq : cproper_interval : set_impl]:
      Option[(set[A]) => (set[A]) => ordera]
  =
  (ccompare[A] match {
     case None => None
     case Some(_) =>
       Some[(set[A]) =>
              (set[A]) =>
                ordera](((a: set[A]) => (b: set[A]) =>
                          comp_of_ords[set[A]](((aa: set[A]) => (ba: set[A]) =>
         cless_eq_set[A](aa, ba)),
        ((aa: set[A]) => (ba: set[A]) => cless_set[A](aa, ba)), a, b)))
   })

def less_eq_bool(x0: Boolean, b: Boolean): Boolean = (x0, b) match {
  case (true, b) => b
  case (false, b) => true
}

def less_bool(x0: Boolean, b: Boolean): Boolean = (x0, b) match {
  case (true, b) => false
  case (false, b) => b
}

def equal_lista[A : equal](x0: List[A], x1: List[A]): Boolean = (x0, x1) match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) => eq[A](x21, y21) && equal_lista[A](x22, y22)
  case (Nil, Nil) => true
}

def equality_list[A](eq_a: A => A => Boolean, x1: List[A], x2: List[A]): Boolean
  =
  (eq_a, x1, x2) match {
  case (eq_a, x :: xa, y :: ya) =>
    (eq_a(x))(y) && equality_list[A](eq_a, xa, ya)
  case (eq_a, x :: xa, Nil) => false
  case (eq_a, Nil, y :: ya) => false
  case (eq_a, Nil, Nil) => true
}

def ceq_lista[A : ceq]: Option[(List[A]) => (List[A]) => Boolean] =
  (ceq[A] match {
     case None => None
     case Some(eq_a) =>
       Some[(List[A]) =>
              (List[A]) =>
                Boolean](((a: List[A]) => (b: List[A]) =>
                           equality_list[A](eq_a, a, b)))
   })

def set_impl_lista[A]: phantom[List[A], set_impla] =
  phantoma[set_impla, List[A]](set_Choose())

def comparator_list[A](comp_a: A => A => ordera, x1: List[A], x2: List[A]):
      ordera
  =
  (comp_a, x1, x2) match {
  case (comp_a, x :: xa, y :: ya) =>
    ((comp_a(x))(y) match {
       case Eq() => comparator_list[A](comp_a, xa, ya)
       case Lt() => Lt()
       case Gt() => Gt()
     })
  case (comp_a, x :: xa, Nil) => Gt()
  case (comp_a, Nil, y :: ya) => Lt()
  case (comp_a, Nil, Nil) => Eq()
}

def ccompare_lista[A : ccompare]: Option[(List[A]) => (List[A]) => ordera] =
  (ccompare[A] match {
     case None => None
     case Some(comp_a) =>
       Some[(List[A]) =>
              (List[A]) =>
                ordera](((a: List[A]) => (b: List[A]) =>
                          comparator_list[A](comp_a, a, b)))
   })

abstract sealed class mapping_impla
final case class mapping_Choose() extends mapping_impla
final case class mapping_Assoc_List() extends mapping_impla
final case class mapping_RBT() extends mapping_impla
final case class mapping_Mapping() extends mapping_impla

def mapping_impl_lista[A]: phantom[List[A], mapping_impla] =
  phantoma[mapping_impla, List[A]](mapping_Choose())

trait mapping_impl[A] {
  val `PDDL_Checker_Exported.mapping_impl`: phantom[A, mapping_impla]
}
def mapping_impl[A](implicit A: mapping_impl[A]): phantom[A, mapping_impla] =
  A.`PDDL_Checker_Exported.mapping_impl`
object mapping_impl {
  implicit def
    `PDDL_Checker_Exported.mapping_impl_list`[A]: mapping_impl[List[A]] = new
    mapping_impl[List[A]] {
    val `PDDL_Checker_Exported.mapping_impl` = mapping_impl_lista[A]
  }
}

def equal_bool(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

abstract sealed class char
final case class Char(a: Boolean, b: Boolean, c: Boolean, d: Boolean,
                       e: Boolean, f: Boolean, g: Boolean, h: Boolean)
  extends char

def equal_chara(x0: char, x1: char): Boolean = (x0, x1) match {
  case (Char(x1, x2, x3, x4, x5, x6, x7, x8),
         Char(y1, y2, y3, y4, y5, y6, y7, y8))
    => equal_bool(x1, y1) &&
         (equal_bool(x2, y2) &&
           (equal_bool(x3, y3) &&
             (equal_bool(x4, y4) &&
               (equal_bool(x5, y5) &&
                 (equal_bool(x6, y6) &&
                   (equal_bool(x7, y7) && equal_bool(x8, y8)))))))
}

def lexordp_eqa[A : ord](xs: List[A], ys: List[A]): Boolean = (xs, ys) match {
  case (x :: xs, y :: ys) =>
    less[A](x, y) || ! (less[A](y, x)) && lexordp_eqa[A](xs, ys)
  case (x :: xs, Nil) => false
  case (xs, Nil) => nulla[A](xs)
  case (Nil, ys) => true
}

def less_eq_char(x0: char, x1: char): Boolean = (x0, x1) match {
  case (Char(b0, b1, b2, b3, b4, b5, b6, b7),
         Char(c0, c1, c2, c3, c4, c5, c6, c7))
    => lexordp_eqa[Boolean](List(b7, b6, b5, b4, b3, b2, b1, b0),
                             List(c7, c6, c5, c4, c3, c2, c1, c0))
}

def lexordpa[A : ord](xs: List[A], ys: List[A]): Boolean = (xs, ys) match {
  case (x :: xs, y :: ys) =>
    less[A](x, y) || ! (less[A](y, x)) && lexordpa[A](xs, ys)
  case (xs, Nil) => false
  case (Nil, ys) => ! (nulla[A](ys))
}

def less_char(x0: char, x1: char): Boolean = (x0, x1) match {
  case (Char(b0, b1, b2, b3, b4, b5, b6, b7),
         Char(c0, c1, c2, c3, c4, c5, c6, c7))
    => lexordpa[Boolean](List(b7, b6, b5, b4, b3, b2, b1, b0),
                          List(c7, c6, c5, c4, c3, c2, c1, c0))
}

def ceq_chara: Option[char => char => Boolean] =
  Some[char => char => Boolean](((a: char) => (b: char) => equal_chara(a, b)))

trait linorder[A] extends order[A] {
}
object linorder {
  implicit def `PDDL_Checker_Exported.linorder_char`: linorder[char] = new
    linorder[char] {
    val `PDDL_Checker_Exported.less_eq` = (a: char, b: char) =>
      less_eq_char(a, b)
    val `PDDL_Checker_Exported.less` = (a: char, b: char) => less_char(a, b)
  }
}

def comparator_of[A : equal : linorder](x: A, y: A): ordera =
  (if (less[A](x, y)) Lt() else (if (eq[A](x, y)) Eq() else Gt()))

def compare_char: char => char => ordera =
  ((a: char) => (b: char) => comparator_of[char](a, b))

def ccompare_chara: Option[char => char => ordera] =
  Some[char => char => ordera](compare_char)

abstract sealed class predicate
final case class Preda(a: List[char]) extends predicate

def equal_predicate(x0: predicate, x1: predicate): Boolean = (x0, x1) match {
  case (Preda(x), Preda(ya)) => equal_lista[char](x, ya)
}

abstract sealed class pred[A]
final case class Pred[A](a: predicate, b: List[A]) extends pred[A]
final case class Eqa[A](a: A, b: A) extends pred[A]

def equal_pred[A : equal](x0: pred[A], x1: pred[A]): Boolean = (x0, x1) match {
  case (Pred(x11, x12), Eqa(x21, x22)) => false
  case (Eqa(x21, x22), Pred(x11, x12)) => false
  case (Eqa(x21, x22), Eqa(y21, y22)) => eq[A](x21, y21) && eq[A](x22, y22)
  case (Pred(x11, x12), Pred(y11, y12)) =>
    equal_predicate(x11, y11) && equal_lista[A](x12, y12)
}

def ceq_preda[A : equal]: Option[(pred[A]) => (pred[A]) => Boolean] =
  Some[(pred[A]) =>
         (pred[A]) =>
           Boolean](((a: pred[A]) => (b: pred[A]) => equal_pred[A](a, b)))

def comparator_predicate(x0: predicate, x1: predicate): ordera = (x0, x1) match
  {
  case (Preda(x), Preda(y)) =>
    comparator_list[char](((a: char) => (b: char) => comparator_of[char](a, b)),
                           x, y)
}

def comparator_pred[A](comp_e_n_t: A => A => ordera, x1: pred[A], x2: pred[A]):
      ordera
  =
  (comp_e_n_t, x1, x2) match {
  case (comp_e_n_t, Eqa(x, xa), Eqa(yb, yc)) =>
    ((comp_e_n_t(x))(yb) match {
       case Eq() => (comp_e_n_t(xa))(yc)
       case Lt() => Lt()
       case Gt() => Gt()
     })
  case (comp_e_n_t, Eqa(x, xa), Pred(y, ya)) => Gt()
  case (comp_e_n_t, Pred(x, xa), Eqa(yb, yc)) => Lt()
  case (comp_e_n_t, Pred(x, xa), Pred(y, ya)) =>
    (comparator_predicate(x, y) match {
       case Eq() => comparator_list[A](comp_e_n_t, xa, ya)
       case Lt() => Lt()
       case Gt() => Gt()
     })
}

def ccompare_preda[A : ccompare]: Option[(pred[A]) => (pred[A]) => ordera] =
  (ccompare[A] match {
     case None => None
     case Some(comp_ent) =>
       Some[(pred[A]) =>
              (pred[A]) =>
                ordera](((a: pred[A]) => (b: pred[A]) =>
                          comparator_pred[A](comp_ent, a, b)))
   })

abstract sealed class func
final case class Func(a: List[char]) extends func

def equal_func(x0: func, x1: func): Boolean = (x0, x1) match {
  case (Func(x), Func(ya)) => equal_lista[char](x, ya)
}

abstract sealed class term[A]
final case class Fun[A](a: func, b: List[term[A]]) extends term[A]
final case class Ent[A](a: A) extends term[A]

def equal_terma[A : equal](x0: term[A], x1: term[A]): Boolean = (x0, x1) match {
  case (Fun(x11, x12), Ent(x2)) => false
  case (Ent(x2), Fun(x11, x12)) => false
  case (Ent(x2), Ent(y2)) => eq[A](x2, y2)
  case (Fun(x11, x12), Fun(y11, y12)) =>
    equal_func(x11, y11) && equal_lista[term[A]](x12, y12)
}

def ceq_terma[A : equal]: Option[(term[A]) => (term[A]) => Boolean] =
  Some[(term[A]) =>
         (term[A]) =>
           Boolean](((a: term[A]) => (b: term[A]) => equal_terma[A](a, b)))

def set_impl_terma[A]: phantom[term[A], set_impla] =
  phantoma[set_impla, term[A]](set_RBT())

def comparator_func(x0: func, x1: func): ordera = (x0, x1) match {
  case (Func(x), Func(y)) =>
    comparator_list[char](((a: char) => (b: char) => comparator_of[char](a, b)),
                           x, y)
}

def comparator_term[A](comp_e_n_t: A => A => ordera, x1: term[A], x2: term[A]):
      ordera
  =
  (comp_e_n_t, x1, x2) match {
  case (comp_e_n_t, Ent(x), Ent(yb)) => (comp_e_n_t(x))(yb)
  case (comp_e_n_t, Ent(x), Fun(y, ya)) => Gt()
  case (comp_e_n_t, Fun(x, xa), Ent(yb)) => Lt()
  case (comp_e_n_t, Fun(x, xa), Fun(y, ya)) =>
    (comparator_func(x, y) match {
       case Eq() =>
         comparator_list[term[A]](((a: term[A]) => (b: term[A]) =>
                                    comparator_term[A](comp_e_n_t, a, b)),
                                   xa, ya)
       case Lt() => Lt()
       case Gt() => Gt()
     })
}

def ccompare_terma[A : ccompare]: Option[(term[A]) => (term[A]) => ordera] =
  (ccompare[A] match {
     case None => None
     case Some(comp_ent) =>
       Some[(term[A]) =>
              (term[A]) =>
                ordera](((a: term[A]) => (b: term[A]) =>
                          comparator_term[A](comp_ent, a, b)))
   })

def one_integera: BigInt = BigInt(1)

abstract sealed class objecta
final case class Obj(a: List[char]) extends objecta

def equal_objecta(x0: objecta, x1: objecta): Boolean = (x0, x1) match {
  case (Obj(x), Obj(ya)) => equal_lista[char](x, ya)
}

def comparator_object(x0: objecta, x1: objecta): ordera = (x0, x1) match {
  case (Obj(x), Obj(y)) =>
    comparator_list[char](((a: char) => (b: char) => comparator_of[char](a, b)),
                           x, y)
}

def ccompare_objecta: Option[objecta => objecta => ordera] =
  Some[objecta =>
         objecta =>
           ordera](((a: objecta) => (b: objecta) => comparator_object(a, b)))

abstract sealed class variable
final case class Vara(a: List[char]) extends variable

def equality_variable(x0: variable, x1: variable): Boolean = (x0, x1) match {
  case (Vara(x), Vara(y)) =>
    equality_list[char](((a: char) => (b: char) => equal_chara(a, b)), x, y)
}

def ceq_variablea: Option[variable => variable => Boolean] =
  Some[variable =>
         variable =>
           Boolean](((a: variable) => (b: variable) => equality_variable(a, b)))

def comparator_variable(x0: variable, x1: variable): ordera = (x0, x1) match {
  case (Vara(x), Vara(y)) =>
    comparator_list[char](((a: char) => (b: char) => comparator_of[char](a, b)),
                           x, y)
}

def ccompare_variablea: Option[variable => variable => ordera] =
  Some[variable =>
         variable =>
           ordera](((a: variable) => (b: variable) =>
                     comparator_variable(a, b)))

abstract sealed class rat
final case class Frct(a: (int, int)) extends rat

abstract sealed class alist[B, A]
final case class Alist[B, A](a: List[(B, A)]) extends alist[B, A]

abstract sealed class sum[A, B]
final case class Inl[A, B](a: A) extends sum[A, B]
final case class Inr[B, A](a: B) extends sum[A, B]

abstract sealed class mapping[A, B]
final case class Assoc_List_Mapping[A, B](a: alist[A, B]) extends mapping[A, B]
final case class RBT_Mapping[A, B](a: mapping_rbt[A, B]) extends mapping[A, B]
final case class Mapping[A, B](a: A => Option[B]) extends mapping[A, B]

abstract sealed class formula[A]
final case class Atom[A](a: A) extends formula[A]
final case class Bot[A]() extends formula[A]
final case class Not[A](a: formula[A]) extends formula[A]
final case class And[A](a: formula[A], b: formula[A]) extends formula[A]
final case class Or[A](a: formula[A], b: formula[A]) extends formula[A]
final case class Imp[A](a: formula[A], b: formula[A]) extends formula[A]

abstract sealed class num_fluent[A]
final case class NFun[A](a: func, b: List[A]) extends num_fluent[A]
final case class Num[A](a: rat) extends num_fluent[A]
final case class Add[A](a: num_fluent[A], b: num_fluent[A]) extends
  num_fluent[A]
final case class Sub[A](a: num_fluent[A], b: num_fluent[A]) extends
  num_fluent[A]
final case class Mult[A](a: num_fluent[A], b: num_fluent[A]) extends
  num_fluent[A]
final case class Div[A](a: num_fluent[A], b: num_fluent[A]) extends
  num_fluent[A]

abstract sealed class num_comp[A]
final case class Num_Eq[A](a: num_fluent[A], b: num_fluent[A]) extends
  num_comp[A]
final case class Le[A](a: num_fluent[A], b: num_fluent[A]) extends num_comp[A]
final case class Lta[A](a: num_fluent[A], b: num_fluent[A]) extends num_comp[A]

abstract sealed class atom[A]
final case class PredAtom[A](a: pred[A]) extends atom[A]
final case class NumComp[A](a: num_comp[A]) extends atom[A]

abstract sealed class typea
final case class Either(a: List[List[char]]) extends typea

abstract sealed class upd_op
final case class Assign() extends upd_op
final case class ScaleUp() extends upd_op
final case class ScaleDown() extends upd_op
final case class Increase() extends upd_op
final case class Decrease() extends upd_op

abstract sealed class nf_upd[A]
final case class NF_Upd[A](a: func, b: upd_op, c: List[A], d: num_fluent[A])
  extends nf_upd[A]

abstract sealed class of_upd[A]
final case class OF_Upd[A](a: func, b: List[A], c: Option[A]) extends of_upd[A]

abstract sealed class symbol
final case class Var(a: variable) extends symbol
final case class Const(a: objecta) extends symbol

abstract sealed class comp_fun_idem[B, A]
final case class Abs_comp_fun_idem[B, A](a: B => A => A) extends
  comp_fun_idem[B, A]

abstract sealed class ast_effect[A]
final case class Effect[A](a: List[pred[A]], b: List[pred[A]],
                            c: List[of_upd[A]], d: List[nf_upd[A]])
  extends ast_effect[A]

abstract sealed class ast_action_schema
final case class Action_Schema(a: List[char], b: List[(variable, typea)],
                                c: formula[atom[term[symbol]]],
                                d: List[(formula[atom[term[symbol]]],
  ast_effect[term[symbol]])])
  extends ast_action_schema

abstract sealed class predicate_decl
final case class PredDecl(a: predicate, b: List[typea]) extends predicate_decl

abstract sealed class num_func_decl
final case class NumFunDecl(a: func, b: List[typea]) extends num_func_decl

abstract sealed class obj_fun_decl
final case class ObjFunDecl(a: func, b: List[typea], c: typea) extends
  obj_fun_decl

abstract sealed class ast_domain_decs
final case class DomainDecls(a: List[(List[char], List[char])],
                              b: List[predicate_decl], c: List[obj_fun_decl],
                              d: List[num_func_decl], e: List[(objecta, typea)])
  extends ast_domain_decs

abstract sealed class ast_problem_decs
final case class ProbDecls(a: ast_domain_decs, b: List[(objecta, typea)])
  extends ast_problem_decs

abstract sealed class ast_domain
final case class Domain(a: ast_problem_decs, b: List[ast_action_schema]) extends
  ast_domain

abstract sealed class world_model
final case class World_Model(a: set[pred[objecta]],
                              b: func =>
                                   Option[(List[objecta]) => Option[objecta]],
                              c: func => Option[(List[objecta]) => Option[rat]])
  extends world_model

abstract sealed class ast_problem
final case class Problem(a: ast_domain, b: world_model,
                          c: formula[atom[term[symbol]]])
  extends ast_problem

abstract sealed class plan_action
final case class PAction(a: List[char], b: List[objecta]) extends plan_action

def dup(x0: int): int = x0 match {
  case Neg(n) => Neg(Bit0(n))
  case Pos(n) => Pos(Bit0(n))
  case zero_inta() => zero_inta()
}

def uminus_int(x0: int): int = x0 match {
  case Neg(m) => Pos(m)
  case Pos(m) => Neg(m)
  case zero_inta() => zero_inta()
}

def plus_num(x0: num, x1: num): num = (x0, x1) match {
  case (Bit1(m), Bit1(n)) => Bit0(plus_num(plus_num(m, n), One()))
  case (Bit1(m), Bit0(n)) => Bit1(plus_num(m, n))
  case (Bit1(m), One()) => Bit0(plus_num(m, One()))
  case (Bit0(m), Bit1(n)) => Bit1(plus_num(m, n))
  case (Bit0(m), Bit0(n)) => Bit0(plus_num(m, n))
  case (Bit0(m), One()) => Bit1(m)
  case (One(), Bit1(n)) => Bit0(plus_num(n, One()))
  case (One(), Bit0(n)) => Bit1(n)
  case (One(), One()) => Bit0(One())
}

def BitM(x0: num): num = x0 match {
  case One() => One()
  case Bit0(n) => Bit1(BitM(n))
  case Bit1(n) => Bit1(Bit0(n))
}

def minus_int(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => sub(n, m)
  case (Neg(m), Pos(n)) => Neg(plus_num(m, n))
  case (Pos(m), Neg(n)) => Pos(plus_num(m, n))
  case (Pos(m), Pos(n)) => sub(m, n)
  case (zero_inta(), l) => uminus_int(l)
  case (k, zero_inta()) => k
}

def plus_int(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => Neg(plus_num(m, n))
  case (Neg(m), Pos(n)) => sub(n, m)
  case (Pos(m), Neg(n)) => sub(m, n)
  case (Pos(m), Pos(n)) => Pos(plus_num(m, n))
  case (zero_inta(), l) => l
  case (k, zero_inta()) => k
}

def sub(x0: num, x1: num): int = (x0, x1) match {
  case (Bit0(m), Bit1(n)) => minus_int(dup(sub(m, n)), one_inta)
  case (Bit1(m), Bit0(n)) => plus_int(dup(sub(m, n)), one_inta)
  case (Bit1(m), Bit1(n)) => dup(sub(m, n))
  case (Bit0(m), Bit0(n)) => dup(sub(m, n))
  case (One(), Bit1(n)) => Neg(Bit0(n))
  case (One(), Bit0(n)) => Neg(BitM(n))
  case (Bit1(m), One()) => Pos(Bit0(m))
  case (Bit0(m), One()) => Pos(BitM(m))
  case (One(), One()) => zero_inta()
}

def foldb[A : ccompare, B](x: A => B => B, xc: mapping_rbt[A, Unit]): B => B =
  ((a: B) =>
    folda[A, Unit,
           B](((aa: A) => (_: Unit) => x(aa)), impl_ofa[A, Unit](xc), a))

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def fun_upda[A, B](equal: A => A => Boolean, f: A => B, aa: A, b: B, a: A): B =
  (if ((equal(aa))(a)) b else f(a))

def balance_right[A, B](a: rbt[A, B], k: A, x: B, xa3: rbt[A, B]): rbt[A, B] =
  (a, k, x, xa3) match {
  case (a, k, x, Branch(R(), b, s, y, c)) =>
    Branch[A, B](R(), a, k, x, Branch[A, B](B(), b, s, y, c))
  case (Branch(B(), a, k, x, b), s, y, Empty()) =>
    balance[A, B](Branch[A, B](R(), a, k, x, b), s, y, Empty[A, B]())
  case (Branch(B(), a, k, x, b), s, y, Branch(B(), va, vb, vc, vd)) =>
    balance[A, B](Branch[A, B](R(), a, k, x, b), s, y,
                   Branch[A, B](B(), va, vb, vc, vd))
  case (Branch(R(), a, k, x, Branch(B(), b, s, y, c)), t, z, Empty()) =>
    Branch[A, B](R(), balance[A, B](paint[A, B](R(), a), k, x, b), s, y,
                  Branch[A, B](B(), c, t, z, Empty[A, B]()))
  case (Branch(R(), a, k, x, Branch(B(), b, s, y, c)), t, z,
         Branch(B(), va, vb, vc, vd))
    => Branch[A, B](R(), balance[A, B](paint[A, B](R(), a), k, x, b), s, y,
                     Branch[A, B](B(), c, t, z,
                                   Branch[A, B](B(), va, vb, vc, vd)))
  case (Empty(), k, x, Empty()) => Empty[A, B]()
  case (Branch(R(), va, vb, vc, Empty()), k, x, Empty()) => Empty[A, B]()
  case (Branch(R(), va, vb, vc, Branch(R(), ve, vf, vg, vh)), k, x, Empty()) =>
    Empty[A, B]()
  case (Empty(), k, x, Branch(B(), va, vb, vc, vd)) => Empty[A, B]()
  case (Branch(R(), ve, vf, vg, Empty()), k, x, Branch(B(), va, vb, vc, vd)) =>
    Empty[A, B]()
  case (Branch(R(), ve, vf, vg, Branch(R(), vi, vj, vk, vl)), k, x,
         Branch(B(), va, vb, vc, vd))
    => Empty[A, B]()
}

def balance_left[A, B](x0: rbt[A, B], s: A, y: B, c: rbt[A, B]): rbt[A, B] =
  (x0, s, y, c) match {
  case (Branch(R(), a, k, x, b), s, y, c) =>
    Branch[A, B](R(), Branch[A, B](B(), a, k, x, b), s, y, c)
  case (Empty(), k, x, Branch(B(), a, s, y, b)) =>
    balance[A, B](Empty[A, B](), k, x, Branch[A, B](R(), a, s, y, b))
  case (Branch(B(), va, vb, vc, vd), k, x, Branch(B(), a, s, y, b)) =>
    balance[A, B](Branch[A, B](B(), va, vb, vc, vd), k, x,
                   Branch[A, B](R(), a, s, y, b))
  case (Empty(), k, x, Branch(R(), Branch(B(), a, s, y, b), t, z, c)) =>
    Branch[A, B](R(), Branch[A, B](B(), Empty[A, B](), k, x, a), s, y,
                  balance[A, B](b, t, z, paint[A, B](R(), c)))
  case (Branch(B(), va, vb, vc, vd), k, x,
         Branch(R(), Branch(B(), a, s, y, b), t, z, c))
    => Branch[A, B](R(), Branch[A, B](B(), Branch[A, B](B(), va, vb, vc, vd), k,
                                       x, a),
                     s, y, balance[A, B](b, t, z, paint[A, B](R(), c)))
  case (Empty(), k, x, Empty()) => Empty[A, B]()
  case (Empty(), k, x, Branch(R(), Empty(), vb, vc, vd)) => Empty[A, B]()
  case (Empty(), k, x, Branch(R(), Branch(R(), ve, vf, vg, vh), vb, vc, vd)) =>
    Empty[A, B]()
  case (Branch(B(), va, vb, vc, vd), k, x, Empty()) => Empty[A, B]()
  case (Branch(B(), va, vb, vc, vd), k, x, Branch(R(), Empty(), vf, vg, vh)) =>
    Empty[A, B]()
  case (Branch(B(), va, vb, vc, vd), k, x,
         Branch(R(), Branch(R(), vi, vj, vk, vl), vf, vg, vh))
    => Empty[A, B]()
}

def combine[A, B](xa0: rbt[A, B], x: rbt[A, B]): rbt[A, B] = (xa0, x) match {
  case (Empty(), x) => x
  case (Branch(v, va, vb, vc, vd), Empty()) => Branch[A, B](v, va, vb, vc, vd)
  case (Branch(R(), a, k, x, b), Branch(R(), c, s, y, d)) =>
    (combine[A, B](b, c) match {
       case Empty() =>
         Branch[A, B](R(), a, k, x, Branch[A, B](R(), Empty[A, B](), s, y, d))
       case Branch(R(), b2, t, z, c2) =>
         Branch[A, B](R(), Branch[A, B](R(), a, k, x, b2), t, z,
                       Branch[A, B](R(), c2, s, y, d))
       case Branch(B(), b2, t, z, c2) =>
         Branch[A, B](R(), a, k, x,
                       Branch[A, B](R(), Branch[A, B](B(), b2, t, z, c2), s, y,
                                     d))
     })
  case (Branch(B(), a, k, x, b), Branch(B(), c, s, y, d)) =>
    (combine[A, B](b, c) match {
       case Empty() =>
         balance_left[A, B](a, k, x, Branch[A, B](B(), Empty[A, B](), s, y, d))
       case Branch(R(), b2, t, z, c2) =>
         Branch[A, B](R(), Branch[A, B](B(), a, k, x, b2), t, z,
                       Branch[A, B](B(), c2, s, y, d))
       case Branch(B(), b2, t, z, c2) =>
         balance_left[A, B](a, k, x,
                             Branch[A, B](B(), Branch[A, B](B(), b2, t, z, c2),
   s, y, d))
     })
  case (Branch(B(), va, vb, vc, vd), Branch(R(), b, k, x, c)) =>
    Branch[A, B](R(), combine[A, B](Branch[A, B](B(), va, vb, vc, vd), b), k, x,
                  c)
  case (Branch(R(), a, k, x, b), Branch(B(), va, vb, vc, vd)) =>
    Branch[A, B](R(), a, k, x,
                  combine[A, B](b, Branch[A, B](B(), va, vb, vc, vd)))
}

def rbt_comp_del_from_right[A, B](c: A => A => ordera, x: A, a: rbt[A, B], y: A,
                                   s: B, xa5: rbt[A, B]):
      rbt[A, B]
  =
  (c, x, a, y, s, xa5) match {
  case (c, x, a, y, s, Branch(B(), lt, z, v, rt)) =>
    balance_right[A, B](a, y, s,
                         rbt_comp_del[A, B](c, x,
     Branch[A, B](B(), lt, z, v, rt)))
  case (c, x, a, y, s, Empty()) =>
    Branch[A, B](R(), a, y, s, rbt_comp_del[A, B](c, x, Empty[A, B]()))
  case (c, x, a, y, s, Branch(R(), va, vb, vc, vd)) =>
    Branch[A, B](R(), a, y, s,
                  rbt_comp_del[A, B](c, x, Branch[A, B](R(), va, vb, vc, vd)))
}

def rbt_comp_del_from_left[A, B](c: A => A => ordera, x: A, xa2: rbt[A, B],
                                  y: A, s: B, b: rbt[A, B]):
      rbt[A, B]
  =
  (c, x, xa2, y, s, b) match {
  case (c, x, Branch(B(), lt, z, v, rt), y, s, b) =>
    balance_left[A, B](rbt_comp_del[A, B](c, x,
   Branch[A, B](B(), lt, z, v, rt)),
                        y, s, b)
  case (c, x, Empty(), y, s, b) =>
    Branch[A, B](R(), rbt_comp_del[A, B](c, x, Empty[A, B]()), y, s, b)
  case (c, x, Branch(R(), va, vb, vc, vd), y, s, b) =>
    Branch[A, B](R(), rbt_comp_del[A, B](c, x,
  Branch[A, B](R(), va, vb, vc, vd)),
                  y, s, b)
}

def rbt_comp_del[A, B](c: A => A => ordera, x: A, xa2: rbt[A, B]): rbt[A, B] =
  (c, x, xa2) match {
  case (c, x, Empty()) => Empty[A, B]()
  case (c, x, Branch(uu, a, y, s, b)) =>
    ((c(x))(y) match {
       case Eq() => combine[A, B](a, b)
       case Lt() => rbt_comp_del_from_left[A, B](c, x, a, y, s, b)
       case Gt() => rbt_comp_del_from_right[A, B](c, x, a, y, s, b)
     })
}

def rbt_comp_delete[A, B](c: A => A => ordera, k: A, t: rbt[A, B]): rbt[A, B] =
  paint[A, B](B(), rbt_comp_del[A, B](c, k, t))

def delete[A : ccompare, B](xb: A, xc: mapping_rbt[A, B]): mapping_rbt[A, B] =
  Mapping_RBT[A, B](rbt_comp_delete[A, B](the[A => A => ordera](ccompare[A]),
   xb, impl_ofa[A, B](xc)))

def list_remove1[A](equal: A => A => Boolean, x: A, xa2: List[A]): List[A] =
  (equal, x, xa2) match {
  case (equal, x, y :: xs) =>
    (if ((equal(x))(y)) xs else y :: list_remove1[A](equal, x, xs))
  case (equal, x, Nil) => Nil
}

def removea[A : ceq](xb: A, xc: set_dlist[A]): set_dlist[A] =
  Abs_dlist[A](list_remove1[A](the[A => A => Boolean](ceq[A]), xb,
                                list_of_dlist[A](xc)))

def remove[A : ceq : ccompare](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, Complement(a)) => Complement[A](insert[A](x, a))
  case (x, RBT_set(rbt)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("remove RBT_set: ccompare = None");
           (((_: Unit) => remove[A](x, RBT_set[A](rbt)))).apply(()) }
       case Some(_) => RBT_set[A](delete[A, Unit](x, rbt))
     })
  case (x, DList_set(dxs)) =>
    (ceq[A] match {
       case None =>
         { sys.error("remove DList_set: ceq = None");
           (((_: Unit) => remove[A](x, DList_set[A](dxs)))).apply(()) }
       case Some(_) => DList_set[A](removea[A](x, dxs))
     })
  case (x, Collect_set(a)) =>
    (ceq[A] match {
       case None =>
         { sys.error("remove Collect: ceq = None");
           (((_: Unit) => remove[A](x, Collect_set[A](a)))).apply(()) }
       case Some(eq) =>
         Collect_set[A](((b: A) => fun_upda[A, Boolean](eq, a, x, false, b)))
     })
}

def insert[A : ceq : ccompare](xa: A, x1: set[A]): set[A] = (xa, x1) match {
  case (xa, Complement(x)) => Complement[A](remove[A](xa, x))
  case (x, RBT_set(rbt)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("insert RBT_set: ccompare = None");
           (((_: Unit) => insert[A](x, RBT_set[A](rbt)))).apply(()) }
       case Some(_) => RBT_set[A](insertb[A, Unit](x, (), rbt))
     })
  case (x, DList_set(dxs)) =>
    (ceq[A] match {
       case None =>
         { sys.error("insert DList_set: ceq = None");
           (((_: Unit) => insert[A](x, DList_set[A](dxs)))).apply(()) }
       case Some(_) => DList_set[A](inserta[A](x, dxs))
     })
  case (x, Set_Monad(xs)) => Set_Monad[A](x :: xs)
  case (x, Collect_set(a)) =>
    (ceq[A] match {
       case None =>
         { sys.error("insert Collect_set: ceq = None");
           (((_: Unit) => insert[A](x, Collect_set[A](a)))).apply(()) }
       case Some(eq) =>
         Collect_set[A](((b: A) => fun_upda[A, Boolean](eq, a, x, true, b)))
     })
}

def image[A : ceq : ccompare,
           B : ceq : ccompare : set_impl](h: A => B, x1: set[A]):
      set[B]
  =
  (h, x1) match {
  case (h, RBT_set(rbt)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("image RBT_set: ccompare = None");
           (((_: Unit) => image[A, B](h, RBT_set[A](rbt)))).apply(()) }
       case Some(_) =>
         (foldb[A, set[B]](comp[B, (set[B]) => set[B],
                                 A](((a: B) => (b: set[B]) => insert[B](a, b)),
                                     h),
                            rbt)).apply(bot_set[B])
     })
  case (g, DList_set(dxs)) =>
    (ceq[A] match {
       case None =>
         { sys.error("image DList_set: ceq = None");
           (((_: Unit) => image[A, B](g, DList_set[A](dxs)))).apply(()) }
       case Some(_) =>
         (foldc[A, set[B]](comp[B, (set[B]) => set[B],
                                 A](((a: B) => (b: set[B]) => insert[B](a, b)),
                                     g),
                            dxs)).apply(bot_set[B])
     })
  case (f, Complement(Complement(b))) => image[A, B](f, b)
  case (f, Collect_set(a)) =>
    { sys.error("image Collect_set");
      (((_: Unit) => image[A, B](f, Collect_set[A](a)))).apply(()) }
  case (f, Set_Monad(xs)) => Set_Monad[B](map[A, B](f, xs))
}

def foldl[A, B](f: A => B => A, a: A, x2: List[B]): A = (f, a, x2) match {
  case (f, a, Nil) => a
  case (f, a, x :: xs) => foldl[A, B](f, (f(a))(x), xs)
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def map_of[A : equal, B](x0: List[(A, B)], k: A): Option[B] = (x0, k) match {
  case ((l, v) :: ps, k) =>
    (if (eq[A](l, k)) Some[B](v) else map_of[A, B](ps, k))
  case (Nil, k) => None
}

def fun_upd[A : equal, B](f: A => B, a: A, b: B): A => B =
  ((x: A) => (if (eq[A](x, a)) b else f(x)))

def update[A : equal, B](k: A, v: B, x2: List[(A, B)]): List[(A, B)] =
  (k, v, x2) match {
  case (k, v, Nil) => List((k, v))
  case (k, v, p :: ps) =>
    (if (eq[A](fst[A, B](p), k)) (k, v) :: ps else p :: update[A, B](k, v, ps))
}

def empty[A, B]: alist[A, B] = Alist[A, B](Nil)

def impl_of[B, A](x0: alist[B, A]): List[(B, A)] = x0 match {
  case Alist(x) => x
}

def lookup[A : equal, B](xa: alist[A, B]): A => Option[B] =
  ((a: A) => map_of[A, B](impl_of[A, B](xa), a))

def updatea[A : equal, B](xc: A, xd: B, xe: alist[A, B]): alist[A, B] =
  Alist[A, B](update[A, B](xc, xd, impl_of[A, B](xe)))

def set_aux[A : ceq : ccompare](impl: set_impla): (List[A]) => set[A] = impl
  match {
  case set_Monad() => ((a: List[A]) => Set_Monad[A](a))
  case set_Choose() =>
    (ccompare[A] match {
       case None =>
         (ceq[A] match {
            case None => ((a: List[A]) => Set_Monad[A](a))
            case Some(_) =>
              ((a: List[A]) =>
                foldl[set[A],
                       A](((s: set[A]) => (x: A) => insert[A](x, s)),
                           DList_set[A](emptyb[A]), a))
          })
       case Some(_) =>
         ((a: List[A]) =>
           foldl[set[A],
                  A](((s: set[A]) => (x: A) => insert[A](x, s)),
                      RBT_set[A](emptyc[A, Unit]), a))
     })
  case impl =>
    ((a: List[A]) =>
      foldl[set[A],
             A](((s: set[A]) => (x: A) => insert[A](x, s)), set_empty[A](impl),
                 a))
}

def set[A : ceq : ccompare : set_impl](xs: List[A]): set[A] =
  (set_aux[A](of_phantom[A, set_impla](set_impl[A]))).apply(xs)

def mapping_empty_choose[A : ccompare, B]: mapping[A, B] =
  (ccompare[A] match {
     case None => Assoc_List_Mapping[A, B](empty[A, B])
     case Some(_) => RBT_Mapping[A, B](emptyc[A, B])
   })

def mapping_empty[A : ccompare, B](x0: mapping_impla): mapping[A, B] = x0 match
  {
  case mapping_RBT() => RBT_Mapping[A, B](emptyc[A, B])
  case mapping_Assoc_List() => Assoc_List_Mapping[A, B](empty[A, B])
  case mapping_Mapping() => Mapping[A, B](((_: A) => None))
  case mapping_Choose() => mapping_empty_choose[A, B]
}

def emptya[A : ccompare : mapping_impl, B]: mapping[A, B] =
  mapping_empty[A, B](of_phantom[A, mapping_impla](mapping_impl[A]))

def times_num(m: num, n: num): num = (m, n) match {
  case (Bit1(m), Bit1(n)) =>
    Bit1(plus_num(plus_num(m, n), Bit0(times_num(m, n))))
  case (Bit1(m), Bit0(n)) => Bit0(times_num(Bit1(m), n))
  case (Bit0(m), Bit1(n)) => Bit0(times_num(m, Bit1(n)))
  case (Bit0(m), Bit0(n)) => Bit0(Bit0(times_num(m, n)))
  case (One(), n) => n
  case (m, One()) => m
}

def times_int(k: int, l: int): int = (k, l) match {
  case (Neg(m), Neg(n)) => Pos(times_num(m, n))
  case (Neg(m), Pos(n)) => Neg(times_num(m, n))
  case (Pos(m), Neg(n)) => Neg(times_num(m, n))
  case (Pos(m), Pos(n)) => Pos(times_num(m, n))
  case (zero_inta(), l) => zero_inta()
  case (k, zero_inta()) => zero_inta()
}

def less_num(m: num, x1: num): Boolean = (m, x1) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_num(m, n)
  case (One(), Bit1(n)) => true
  case (One(), Bit0(n)) => true
  case (m, One()) => false
}

def less_eq_num(x0: num, n: num): Boolean = (x0, n) match {
  case (Bit1(m), Bit0(n)) => less_num(m, n)
  case (Bit1(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit1(n)) => less_eq_num(m, n)
  case (Bit0(m), Bit0(n)) => less_eq_num(m, n)
  case (Bit1(m), One()) => false
  case (Bit0(m), One()) => false
  case (One(), n) => true
}

def less_eq_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => less_eq_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), zero_inta()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => less_eq_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => true
  case (zero_inta(), zero_inta()) => true
}

def less_int(x0: int, x1: int): Boolean = (x0, x1) match {
  case (Neg(k), Neg(l)) => less_num(l, k)
  case (Neg(k), Pos(l)) => true
  case (Neg(k), zero_inta()) => true
  case (Pos(k), Neg(l)) => false
  case (Pos(k), Pos(l)) => less_num(k, l)
  case (Pos(k), zero_inta()) => false
  case (zero_inta(), Neg(l)) => false
  case (zero_inta(), Pos(l)) => true
  case (zero_inta(), zero_inta()) => false
}

def abs_int(i: int): int = (if (less_int(i, zero_inta())) uminus_int(i) else i)

def divmod_step_int(l: int, qr: (int, int)): (int, int) =
  {
    val (q, r) = qr: ((int, int));
    (if (less_eq_int(abs_int(l), abs_int(r)))
      (plus_int(times_int(Pos(Bit0(One())), q), one_inta), minus_int(r, l))
      else (times_int(Pos(Bit0(One())), q), r))
  }

def divmod_int(m: num, x1: num): (int, int) = (m, x1) match {
  case (Bit1(m), Bit1(n)) =>
    (if (less_num(m, n)) (zero_inta(), Pos(Bit1(m)))
      else divmod_step_int(Pos(Bit1(n)), divmod_int(Bit1(m), Bit0(Bit1(n)))))
  case (Bit0(m), Bit1(n)) =>
    (if (less_eq_num(m, n)) (zero_inta(), Pos(Bit0(m)))
      else divmod_step_int(Pos(Bit1(n)), divmod_int(Bit0(m), Bit0(Bit1(n)))))
  case (Bit1(m), Bit0(n)) =>
    {
      val (q, r) = divmod_int(m, n): ((int, int));
      (q, plus_int(times_int(Pos(Bit0(One())), r), one_inta))
    }
  case (Bit0(m), Bit0(n)) => {
                               val (q, r) = divmod_int(m, n): ((int, int));
                               (q, times_int(Pos(Bit0(One())), r))
                             }
  case (One(), Bit1(n)) => (zero_inta(), Pos(One()))
  case (One(), Bit0(n)) => (zero_inta(), Pos(One()))
  case (m, One()) => (Pos(m), zero_inta())
}

def of_bool[A : zero_neq_one](x0: Boolean): A = x0 match {
  case true => one[A]
  case false => zero[A]
}

def adjust_div(x0: (int, int)): int = x0 match {
  case (q, r) => plus_int(q, of_bool[int](! (equal_inta(r, zero_inta()))))
}

def divide_int(k: int, ka: int): int = (k, ka) match {
  case (Neg(m), Neg(n)) => fst[int, int](divmod_int(m, n))
  case (Pos(m), Neg(n)) => uminus_int(adjust_div(divmod_int(m, n)))
  case (Neg(m), Pos(n)) => uminus_int(adjust_div(divmod_int(m, n)))
  case (Pos(m), Pos(n)) => fst[int, int](divmod_int(m, n))
  case (k, Neg(One())) => uminus_int(k)
  case (k, Pos(One())) => k
  case (zero_inta(), k) => zero_inta()
  case (k, zero_inta()) => zero_inta()
}

def adjust_mod(l: num, r: int): int =
  (if (equal_inta(r, zero_inta())) zero_inta() else minus_int(Pos(l), r))

def modulo_int(k: int, ka: int): int = (k, ka) match {
  case (Neg(m), Neg(n)) => uminus_int(snd[int, int](divmod_int(m, n)))
  case (Pos(m), Neg(n)) =>
    uminus_int(adjust_mod(n, snd[int, int](divmod_int(m, n))))
  case (Neg(m), Pos(n)) => adjust_mod(n, snd[int, int](divmod_int(m, n)))
  case (Pos(m), Pos(n)) => snd[int, int](divmod_int(m, n))
  case (k, Neg(One())) => zero_inta()
  case (k, Pos(One())) => zero_inta()
  case (zero_inta(), k) => zero_inta()
  case (k, zero_inta()) => k
}

def gcd_int(k: int, l: int): int =
  abs_int((if (equal_inta(l, zero_inta())) k
            else gcd_int(l, modulo_int(abs_int(k), abs_int(l)))))

def normalize(p: (int, int)): (int, int) =
  (if (less_int(zero_inta(), snd[int, int](p)))
    {
      val a = gcd_int(fst[int, int](p), snd[int, int](p)): int;
      (divide_int(fst[int, int](p), a), divide_int(snd[int, int](p), a))
    }
    else (if (equal_inta(snd[int, int](p), zero_inta())) (zero_inta(), one_inta)
           else {
                  val a =
                    uminus_int(gcd_int(fst[int, int](p), snd[int, int](p))):
                      int;
                  (divide_int(fst[int, int](p), a),
                    divide_int(snd[int, int](p), a))
                }))

def BigOr[A](x0: List[formula[A]]): formula[A] = x0 match {
  case Nil => Bot[A]()
  case f :: fs => Or[A](f, BigOr[A](fs))
}

def lookupa[A : ccompare : equal, B](x0: mapping[A, B]): A => Option[B] = x0
  match {
  case RBT_Mapping(t) => lookupb[A, B](t)
  case Assoc_List_Mapping(al) => lookup[A, B](al)
}

def updateb[A : ccompare : equal, B](k: A, v: B, x2: mapping[A, B]):
      mapping[A, B]
  =
  (k, v, x2) match {
  case (k, v, RBT_Mapping(t)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("update RBT_Mapping: ccompare = None");
           (((_: Unit) => updateb[A, B](k, v, RBT_Mapping[A, B](t)))).apply(())
           }
       case Some(_) => RBT_Mapping[A, B](insertb[A, B](k, v, t))
     })
  case (k, v, Assoc_List_Mapping(al)) =>
    Assoc_List_Mapping[A, B](updatea[A, B](k, v, al))
  case (k, v, Mapping(m)) =>
    Mapping[A, B](fun_upd[A, Option[B]](m, k, Some[B](v)))
}

def integer_of_char(x0: char): BigInt = x0 match {
  case Char(b0, b1, b2, b3, b4, b5, b6, b7) =>
    ((((((of_bool[BigInt](b7) * BigInt(2) + of_bool[BigInt](b6)) * BigInt(2) +
          of_bool[BigInt](b5)) *
          BigInt(2) +
         of_bool[BigInt](b4)) *
         BigInt(2) +
        of_bool[BigInt](b3)) *
        BigInt(2) +
       of_bool[BigInt](b2)) *
       BigInt(2) +
      of_bool[BigInt](b1)) *
      BigInt(2) +
      of_bool[BigInt](b0)
}

def implode(cs: List[char]): String =
  "" ++ (map[char,
              BigInt](((a: char) => integer_of_char(a)),
                       cs)).map((k: BigInt) => if (BigInt(0) <= k && k < BigInt(128)) k.charValue else sys.error("Non-ASCII character in literal"))

def BigAnd[A](x0: List[formula[A]]): formula[A] = x0 match {
  case Nil => Not[A](Bot[A]())
  case f :: fs => And[A](f, BigAnd[A](fs))
}

def default[A : ccompare : equal, B](k: A, v: B, m: mapping[A, B]):
      mapping[A, B]
  =
  (if (! (is_none[B]((lookupa[A, B](m)).apply(k)))) m
    else updateb[A, B](k, v, m))

def quotient_of(x0: rat): (int, int) = x0 match {
  case Frct(x) => x
}

def sup_cfi[A : lattice]: comp_fun_idem[A, A] =
  Abs_comp_fun_idem[A, A](((a: A) => (b: A) => sup[A](a, b)))

def map_entry[A : ccompare : equal, B](k: A, f: B => B, m: mapping[A, B]):
      mapping[A, B]
  =
  ((lookupa[A, B](m)).apply(k) match {
     case None => m
     case Some(v) => updateb[A, B](k, f(v), m)
   })

def map_default[A : ccompare : equal,
                 B](k: A, v: B, f: B => B, m: mapping[A, B]):
      mapping[A, B]
  =
  map_entry[A, B](k, f, default[A, B](k, v, m))

def primitives(x0: typea): List[List[char]] = x0 match {
  case Either(x) => x
}

def whilea[A](b: A => Boolean, c: A => A, s: A): A =
  (if (b(s)) whilea[A](b, c, c(s)) else s)

def dfs_reachable[A : ceq : ccompare : set_impl](succ: A => List[A],
          d: A => Boolean, w: List[A]):
      Boolean
  =
  {
    val (_, (_, brk)) =
      whilea[(set[A],
               (List[A],
                 Boolean))](((a: (set[A], (List[A], Boolean))) =>
                              {
                                val (_, (wa, brk)) =
                                  a: ((set[A], (List[A], Boolean)));
                                ! brk && ! (nulla[A](wa))
                              }),
                             ((a: (set[A], (List[A], Boolean))) =>
                               {
                                 val (v, (va :: wa, _)) =
                                   a: ((set[A], (List[A], Boolean)));
                                 (if (d(va)) (v, (va :: wa, true))
                                   else (if (member[A](va, v)) (v, (wa, false))
  else {
         val vb = insert[A](va, v): (set[A])
         val wb = succ(va) ++ wa: (List[A]);
         (vb, (wb, false))
       }))
                               }),
                             (bot_set[A], (w, false))):
        ((set[A], (List[A], Boolean)));
    brk
  }

def of_type(g: (List[char]) => List[List[char]], oT: typea, t: typea): Boolean =
  list_all[List[char]](((pt: List[char]) =>
                         dfs_reachable[List[char]](g,
            ((a: List[char]) => equal_lista[char](pt, a)), primitives(t))),
                        primitives(oT))

def lookup_default[A, B : ccompare : equal](d: A, m: mapping[B, A], k: B): A =
  ((lookupa[B, A](m)).apply(k) match {
     case None => d
     case Some(v) => v
   })

def tab_succ[A : ccompare : equal : mapping_impl, B](l: List[(A, B)]):
      A => List[B]
  =
  ((a: A) =>
    lookup_default[List[B],
                    A](Nil, fold[(A, B),
                                  mapping[A,
   List[B]]](((aa: (A, B)) =>
               {
                 val (u, v) = aa: ((A, B));
                 ((ab: mapping[A, List[B]]) =>
                   map_default[A, List[B]](u, Nil, ((ac: List[B]) => v :: ac),
    ab))
               }),
              l, emptya[A, List[B]]),
                        a))

def less_eq_rat(p: rat, q: rat): Boolean =
  {
    val (a, c) = quotient_of(p): ((int, int))
    val (b, d) = quotient_of(q): ((int, int));
    less_eq_int(times_int(a, d), times_int(c, b))
  }

def equal_prod[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean = (x0, x1)
  match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

def equal_rat(a: rat, b: rat): Boolean =
  equal_prod[int, int](quotient_of(a), quotient_of(b))

def less_rat(p: rat, q: rat): Boolean =
  {
    val (a, c) = quotient_of(p): ((int, int))
    val (b, d) = quotient_of(q): ((int, int));
    less_int(times_int(a, d), times_int(c, b))
  }

def nf_int(x0: world_model): func => Option[(List[objecta]) => Option[rat]] = x0
  match {
  case World_Model(x1, x2, x3) => x3
}

def divide_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((int, int))
         val (b, d) = quotient_of(q): ((int, int));
         normalize((times_int(a, d), times_int(c, b)))
       })

def times_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((int, int))
         val (b, d) = quotient_of(q): ((int, int));
         normalize((times_int(a, b), times_int(c, d)))
       })

def minus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((int, int))
         val (b, d) = quotient_of(q): ((int, int));
         normalize((minus_int(times_int(a, d), times_int(b, c)),
                     times_int(c, d)))
       })

def plus_rat(p: rat, q: rat): rat =
  Frct({
         val (a, c) = quotient_of(p): ((int, int))
         val (b, d) = quotient_of(q): ((int, int));
         normalize((plus_int(times_int(a, d), times_int(b, c)),
                     times_int(c, d)))
       })

def of_int(x0: world_model): func => Option[(List[objecta]) => Option[objecta]]
  =
  x0 match {
  case World_Model(x1, x2, x3) => x2
}

def term_val(m: world_model, x1: term[objecta]): Option[objecta] = (m, x1) match
  {
  case (m, Ent(obj)) => Some[objecta](obj)
  case (m, Fun(fun, as)) =>
    ((of_int(m)).apply(fun) match {
       case None => None
       case Some(f) =>
         {
           val arg_vals =
             map[term[objecta],
                  Option[objecta]](((a: term[objecta]) => term_val(m, a)), as):
               (List[Option[objecta]]);
           (if (list_all[Option[objecta]](((x: Option[objecta]) =>
    ! (is_none[objecta](x))),
   arg_vals))
             f(map[Option[objecta],
                    objecta](((a: Option[objecta]) => the[objecta](a)),
                              arg_vals))
             else None)
         }
     })
}

def combine_options[A](f: A => A => A, x: Option[A], y: Option[A]): Option[A] =
  (x match {
     case None => y
     case Some(xa) => (y match {
                         case None => Some[A](xa)
                         case Some(ya) => Some[A]((f(xa))(ya))
                       })
   })

def nf_val(m: world_model, x1: num_fluent[term[objecta]]): Option[rat] = (m, x1)
  match {
  case (m, NFun(fun, as)) =>
    ((nf_int(m)).apply(fun) match {
       case None => None
       case Some(f) =>
         {
           val arg_vals =
             map[term[objecta],
                  Option[objecta]](((a: term[objecta]) => term_val(m, a)), as):
               (List[Option[objecta]]);
           (if (list_all[Option[objecta]](((x: Option[objecta]) =>
    ! (is_none[objecta](x))),
   arg_vals))
             f(map[Option[objecta],
                    objecta](((a: Option[objecta]) => the[objecta](a)),
                              arg_vals))
             else None)
         }
     })
  case (m, Num(n)) => Some[rat](n)
  case (m, Add(x, y)) =>
    combine_options[rat](((a: rat) => (b: rat) => plus_rat(a, b)), nf_val(m, x),
                          nf_val(m, y))
  case (m, Sub(x, y)) =>
    combine_options[rat](((a: rat) => (b: rat) => minus_rat(a, b)),
                          nf_val(m, x), nf_val(m, y))
  case (m, Mult(x, y)) =>
    combine_options[rat](((a: rat) => (b: rat) => times_rat(a, b)),
                          nf_val(m, x), nf_val(m, y))
  case (m, Div(x, y)) =>
    combine_options[rat](((a: rat) => (b: rat) => divide_rat(a, b)),
                          nf_val(m, x), nf_val(m, y))
}

def nc_val(m: world_model, x1: num_comp[term[objecta]]): Boolean = (m, x1) match
  {
  case (m, Num_Eq(x, y)) => ((nf_val(m, x), nf_val(m, y)) match {
                               case (None, _) => false
                               case (Some(_), None) => false
                               case (Some(xa), Some(a)) => equal_rat(xa, a)
                             })
  case (m, Le(x, y)) => ((nf_val(m, x), nf_val(m, y)) match {
                           case (None, _) => false
                           case (Some(_), None) => false
                           case (Some(xa), Some(a)) => less_eq_rat(xa, a)
                         })
  case (m, Lta(x, y)) => ((nf_val(m, x), nf_val(m, y)) match {
                            case (None, _) => false
                            case (Some(_), None) => false
                            case (Some(xa), Some(a)) => less_rat(xa, a)
                          })
}

def comp_fun_idem_apply[B, A](x0: comp_fun_idem[B, A]): B => A => A = x0 match {
  case Abs_comp_fun_idem(x) => x
}

def set_fold_cfi[A : ceq : ccompare,
                  B](f: comp_fun_idem[A, B], b: B, x2: set[A]):
      B
  =
  (f, b, x2) match {
  case (f, b, RBT_set(rbt)) =>
    (ccompare[A] match {
       case None =>
         { sys.error("set_fold_cfi RBT_set: ccompare = None");
           (((_: Unit) => set_fold_cfi[A, B](f, b, RBT_set[A](rbt)))).apply(())
           }
       case Some(_) => (foldb[A, B](comp_fun_idem_apply[A, B](f), rbt)).apply(b)
     })
  case (f, b, DList_set(dxs)) =>
    (ceq[A] match {
       case None =>
         { sys.error("set_fold_cfi DList_set: ceq = None");
           (((_: Unit) =>
              set_fold_cfi[A, B](f, b, DList_set[A](dxs)))).apply(())
           }
       case Some(_) => (foldc[A, B](comp_fun_idem_apply[A, B](f), dxs)).apply(b)
     })
  case (f, b, Set_Monad(xs)) => fold[A, B](comp_fun_idem_apply[A, B](f), xs, b)
  case (f, b, Collect_set(p)) =>
    { sys.error("set_fold_cfi not supported on Collect_set");
      (((_: Unit) => set_fold_cfi[A, B](f, b, Collect_set[A](p)))).apply(()) }
  case (f, b, Complement(a)) =>
    { sys.error("set_fold_cfi not supported on Complement");
      (((_: Unit) => set_fold_cfi[A, B](f, b, Complement[A](a)))).apply(()) }
}

def map_formula[A, B](f: A => B, x1: formula[A]): formula[B] = (f, x1) match {
  case (f, Atom(x1)) => Atom[B](f(x1))
  case (f, Bot()) => Bot[B]()
  case (f, Not(x3)) => Not[B](map_formula[A, B](f, x3))
  case (f, And(x41, x42)) =>
    And[B](map_formula[A, B](f, x41), map_formula[A, B](f, x42))
  case (f, Or(x51, x52)) =>
    Or[B](map_formula[A, B](f, x51), map_formula[A, B](f, x52))
  case (f, Imp(x61, x62)) =>
    Imp[B](map_formula[A, B](f, x61), map_formula[A, B](f, x62))
}

def map_num_fluent[A, B](f: A => B, x1: num_fluent[A]): num_fluent[B] = (f, x1)
  match {
  case (f, NFun(x11, x12)) => NFun[B](x11, map[A, B](f, x12))
  case (f, Num(x2)) => Num[B](x2)
  case (f, Add(x31, x32)) =>
    Add[B](map_num_fluent[A, B](f, x31), map_num_fluent[A, B](f, x32))
  case (f, Sub(x41, x42)) =>
    Sub[B](map_num_fluent[A, B](f, x41), map_num_fluent[A, B](f, x42))
  case (f, Mult(x51, x52)) =>
    Mult[B](map_num_fluent[A, B](f, x51), map_num_fluent[A, B](f, x52))
  case (f, Div(x61, x62)) =>
    Div[B](map_num_fluent[A, B](f, x61), map_num_fluent[A, B](f, x62))
}

def map_num_comp[A, B](f: A => B, x1: num_comp[A]): num_comp[B] = (f, x1) match
  {
  case (f, Num_Eq(x11, x12)) =>
    Num_Eq[B](map_num_fluent[A, B](f, x11), map_num_fluent[A, B](f, x12))
  case (f, Le(x21, x22)) =>
    Le[B](map_num_fluent[A, B](f, x21), map_num_fluent[A, B](f, x22))
  case (f, Lta(x31, x32)) =>
    Lta[B](map_num_fluent[A, B](f, x31), map_num_fluent[A, B](f, x32))
}

def map_pred[A, B](f: A => B, x1: pred[A]): pred[B] = (f, x1) match {
  case (f, Pred(x11, x12)) => Pred[B](x11, map[A, B](f, x12))
  case (f, Eqa(x21, x22)) => Eqa[B](f(x21), f(x22))
}

def map_atom[A, B](f: A => B, x1: atom[A]): atom[B] = (f, x1) match {
  case (f, PredAtom(x1)) => PredAtom[B](map_pred[A, B](f, x1))
  case (f, NumComp(x2)) => NumComp[B](map_num_comp[A, B](f, x2))
}

def map_term[A, B](f: A => B, x1: term[A]): term[B] = (f, x1) match {
  case (f, Fun(x11, x12)) =>
    Fun[B](x11, map[term[A],
                     term[B]](((a: term[A]) => map_term[A, B](f, a)), x12))
  case (f, Ent(x2)) => Ent[B](f(x2))
}

def equal_variable(x0: variable, x1: variable): Boolean = (x0, x1) match {
  case (Vara(x), Vara(ya)) => equal_lista[char](x, ya)
}

def sym_subst(v: variable, obj: objecta, x2: symbol): symbol = (v, obj, x2)
  match {
  case (v, obj, Var(x)) => (if (equal_variable(x, v)) Const(obj) else Var(x))
  case (uu, uv, Const(obj)) => Const(obj)
}

def term_subst(v: variable, obj: objecta): (term[symbol]) => term[symbol] =
  ((a: term[symbol]) =>
    map_term[symbol, symbol](((aa: symbol) => sym_subst(v, obj, aa)), a))

def atom_subst(v: variable, c: objecta):
      (atom[term[symbol]]) => atom[term[symbol]]
  =
  ((a: atom[term[symbol]]) =>
    map_atom[term[symbol], term[symbol]](term_subst(v, c), a))

def f_subst(v: variable, c: objecta):
      (formula[atom[term[symbol]]]) => formula[atom[term[symbol]]]
  =
  ((a: formula[atom[term[symbol]]]) =>
    map_formula[atom[term[symbol]], atom[term[symbol]]](atom_subst(v, c), a))

def bit_cut_integer(k: BigInt): (BigInt, Boolean) =
  (if (k == BigInt(0)) (BigInt(0), false)
    else {
           val (r, s) =
             ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
               (k.abs /% l.abs)).apply(k).apply(BigInt(2)):
               ((BigInt, BigInt));
           ((if (BigInt(0) < k) r else (- r) - s), s == BigInt(1))
         })

def char_of_integer(k: BigInt): char =
  {
    val (q0, b0) = bit_cut_integer(k): ((BigInt, Boolean))
    val (q1, b1) = bit_cut_integer(q0): ((BigInt, Boolean))
    val (q2, b2) = bit_cut_integer(q1): ((BigInt, Boolean))
    val (q3, b3) = bit_cut_integer(q2): ((BigInt, Boolean))
    val (q4, b4) = bit_cut_integer(q3): ((BigInt, Boolean))
    val (q5, b5) = bit_cut_integer(q4): ((BigInt, Boolean))
    val (q6, b6) = bit_cut_integer(q5): ((BigInt, Boolean))
    val (_, a) = bit_cut_integer(q6): ((BigInt, Boolean));
    Char(b0, b1, b2, b3, b4, b5, b6, a)
  }

def explode(s: String): List[char] =
  map[BigInt,
       char](((a: BigInt) => char_of_integer(a)),
              (s.toList.map(c => { val k: Int = c.toInt; if (k < 128) BigInt(k) else sys.error("Non-ASCII character in literal") })))

def preds(x0: world_model): set[pred[objecta]] = x0 match {
  case World_Model(x1, x2, x3) => x1
}

def pred_inst(m: world_model, x1: pred[term[objecta]]): Option[pred[objecta]] =
  (m, x1) match {
  case (m, Pred(p, as)) =>
    {
      val arg_vals =
        map[term[objecta],
             Option[objecta]](((a: term[objecta]) => term_val(m, a)), as):
          (List[Option[objecta]]);
      (if (list_all[Option[objecta]](((x: Option[objecta]) =>
                                       ! (is_none[objecta](x))),
                                      arg_vals))
        Some[pred[objecta]](Pred[objecta](p,
   map[Option[objecta],
        objecta](((a: Option[objecta]) => the[objecta](a)), arg_vals)))
        else None)
    }
  case (m, Eqa(t1, t2)) =>
    ((term_val(m, t1), term_val(m, t2)) match {
       case (None, _) => None
       case (Some(_), None) => None
       case (Some(x), Some(y)) => Some[pred[objecta]](Eqa[objecta](x, y))
     })
}

def pred_val(m: world_model, p: pred[term[objecta]]): Boolean =
  (pred_inst(m, p) match {
     case None => false
     case Some(Pred(pa, as)) =>
       member[pred[objecta]](Pred[objecta](pa, as), preds(m))
     case Some(Eqa(a, b)) => equal_objecta(a, b)
   })

def set_impl_variable: phantom[variable, set_impla] =
  phantoma[set_impla, variable](set_RBT())

def sym_vars(x0: symbol): set[variable] = x0 match {
  case Var(x) =>
    insert[variable](x, set_empty[variable](of_phantom[variable,
                set_impla](set_impl_variable)))
  case Const(c) =>
    set_empty[variable](of_phantom[variable, set_impla](set_impl_variable))
}

def Sup_set[A : finite_UNIV : cenum : ceq : cproper_interval : set_impl](a:
                                   set[set[A]]):
      set[A]
  =
  (if (finite[set[A]](a))
    set_fold_cfi[set[A], set[A]](sup_cfi[set[A]], bot_set[A], a)
    else { sys.error("Sup: infinite"); (((_: Unit) => Sup_set[A](a))).apply(())
           })

def ent[A : finite_UNIV : cenum : ceq : cproper_interval : equal : set_impl](x0:
                                       term[A]):
      set[A]
  =
  x0 match {
  case Fun(x11, x12) =>
    Sup_set[A](image[term[A],
                      set[A]](((a: term[A]) => ent[A](a)), set[term[A]](x12)))
  case Ent(x2) => insert[A](x2, bot_set[A])
}

def valuation(m: world_model, x1: atom[term[objecta]]): Boolean = (m, x1) match
  {
  case (m, PredAtom(p)) => pred_val(m, p)
  case (m, NumComp(c)) => nc_val(m, c)
}

def predicate[A](x0: pred[A]): predicate = x0 match {
  case Pred(x11, x12) => x11
}

def subtype_edge[A, B](x0: (A, B)): (B, A) = x0 match {
  case (ty, superty) => (superty, ty)
}

def types(x0: ast_domain_decs): List[(List[char], List[char])] = x0 match {
  case DomainDecls(x1, x2, x3, x4, x5) => x1
}

def STG(dd: ast_domain_decs): (List[char]) => List[List[char]] =
  tab_succ[List[char],
            List[char]](map[(List[char], List[char]),
                             (List[char],
                               List[char])](((a: (List[char], List[char])) =>
      subtype_edge[List[char], List[char]](a)),
     types(dd)))

def consts(x0: ast_domain_decs): List[(objecta, typea)] = x0 match {
  case DomainDecls(x1, x2, x3, x4, x5) => x5
}

def term_vars_impl(x0: term[symbol]): set[variable] = x0 match {
  case Fun(f, as) =>
    fold[term[symbol],
          set[variable]](comp[set[variable], (set[variable]) => set[variable],
                               term[symbol]](((a: set[variable]) =>
       (b: set[variable]) => sup_seta[variable](a, b)),
      ((a: term[symbol]) => term_vars_impl(a))),
                          as, set_empty[variable](of_phantom[variable,
                      set_impla](set_impl_variable)))
  case Ent(x) => sym_vars(x)
}

def pred_vars_impl(x0: pred[term[symbol]]): set[variable] = x0 match {
  case Eqa(a, b) => sup_seta[variable](term_vars_impl(a), term_vars_impl(b))
  case Pred(p, as) =>
    fold[term[symbol],
          set[variable]](comp[set[variable], (set[variable]) => set[variable],
                               term[symbol]](((a: set[variable]) =>
       (b: set[variable]) => sup_seta[variable](a, b)),
      ((a: term[symbol]) => term_vars_impl(a))),
                          as, set_empty[variable](of_phantom[variable,
                      set_impla](set_impl_variable)))
}

def nf_vars_impl(x0: num_fluent[term[symbol]]): set[variable] = x0 match {
  case Div(a, b) => sup_seta[variable](nf_vars_impl(a), nf_vars_impl(b))
  case Mult(a, b) => sup_seta[variable](nf_vars_impl(a), nf_vars_impl(b))
  case Sub(a, b) => sup_seta[variable](nf_vars_impl(a), nf_vars_impl(b))
  case Add(a, b) => sup_seta[variable](nf_vars_impl(a), nf_vars_impl(b))
  case Num(n) =>
    set_empty[variable](of_phantom[variable, set_impla](set_impl_variable))
  case NFun(f, as) =>
    fold[term[symbol],
          set[variable]](comp[set[variable], (set[variable]) => set[variable],
                               term[symbol]](((a: set[variable]) =>
       (b: set[variable]) => sup_seta[variable](a, b)),
      ((a: term[symbol]) => term_vars_impl(a))),
                          as, set_empty[variable](of_phantom[variable,
                      set_impla](set_impl_variable)))
}

def nc_vars_impl(x0: num_comp[term[symbol]]): set[variable] = x0 match {
  case Lta(a, b) => sup_seta[variable](nf_vars_impl(a), nf_vars_impl(b))
  case Le(a, b) => sup_seta[variable](nf_vars_impl(a), nf_vars_impl(b))
  case Num_Eq(a, b) => sup_seta[variable](nf_vars_impl(a), nf_vars_impl(b))
}

def atom_vars_impl(x0: atom[term[symbol]]): set[variable] = x0 match {
  case NumComp(nc) => nc_vars_impl(nc)
  case PredAtom(p) => pred_vars_impl(p)
}

def f_vars_impl(x0: formula[atom[term[symbol]]]): set[variable] = x0 match {
  case Imp(phi_1, phi_2) =>
    sup_seta[variable](f_vars_impl(phi_1), f_vars_impl(phi_2))
  case Or(phi_1, phi_2) =>
    sup_seta[variable](f_vars_impl(phi_1), f_vars_impl(phi_2))
  case And(phi_1, phi_2) =>
    sup_seta[variable](f_vars_impl(phi_1), f_vars_impl(phi_2))
  case Not(phi_1) => f_vars_impl(phi_1)
  case Bot() =>
    set_empty[variable](of_phantom[variable, set_impla](set_impl_variable))
  case Atom(p) => atom_vars_impl(p)
}

def domain_decs(x0: ast_problem_decs): ast_domain_decs = x0 match {
  case ProbDecls(x1, x2) => x1
}

def of_type_impl(dd: ast_domain_decs): typea => typea => Boolean =
  ((a: typea) => (b: typea) => of_type(STG(dd), a, b))

def objects(x0: ast_problem_decs): List[(objecta, typea)] = x0 match {
  case ProbDecls(x1, x2) => x2
}

def t_dom_impl(pd: ast_problem_decs, typ: typea): List[objecta] =
  map_filter[(objecta, typea),
              objecta](((x: (objecta, typea)) =>
                         (if ({
                                val (_, t) = x: ((objecta, typea));
                                (of_type_impl(domain_decs(pd))).apply(t).apply(typ)
                              })
                           Some[objecta](fst[objecta, typea](x)) else None)),
                        consts(domain_decs(pd)) ++ objects(pd))

def all_impl(pd: ast_problem_decs, v: variable, t: typea,
              phi: formula[atom[term[symbol]]]):
      formula[atom[term[symbol]]]
  =
  (if (! (member[variable](v, f_vars_impl(phi))) &&
         ! (nulla[objecta](t_dom_impl(pd, t))))
    phi else BigAnd[atom[term[symbol]]](map[objecta,
     formula[atom[term[symbol]]]](((c: objecta) => (f_subst(v, c)).apply(phi)),
                                   t_dom_impl(pd, t))))

def exists_impl(pd: ast_problem_decs, v: variable, t: typea,
                 phi: formula[atom[term[symbol]]]):
      formula[atom[term[symbol]]]
  =
  (if (! (member[variable](v, f_vars_impl(phi))) &&
         ! (nulla[objecta](t_dom_impl(pd, t))))
    phi else BigOr[atom[term[symbol]]](map[objecta,
    formula[atom[term[symbol]]]](((c: objecta) => (f_subst(v, c)).apply(phi)),
                                  t_dom_impl(pd, t))))

def pddl_all_impl(pd: ast_problem_decs, vts: List[(variable, typea)],
                   phi: formula[atom[term[symbol]]]):
      formula[atom[term[symbol]]]
  =
  (foldr[(variable, typea),
          formula[atom[term[symbol]]]](((a: (variable, typea)) =>
 {
   val (aa, b) = a: ((variable, typea));
   ((c: formula[atom[term[symbol]]]) => all_impl(pd, aa, b, c))
 }),
vts)).apply(phi)

def pddl_exists_impl(pd: ast_problem_decs, vts: List[(variable, typea)],
                      phi: formula[atom[term[symbol]]]):
      formula[atom[term[symbol]]]
  =
  (foldr[(variable, typea),
          formula[atom[term[symbol]]]](((a: (variable, typea)) =>
 {
   val (aa, b) = a: ((variable, typea));
   ((c: formula[atom[term[symbol]]]) => exists_impl(pd, aa, b, c))
 }),
vts)).apply(phi)

} /* object PDDL_Checker_Exported */
