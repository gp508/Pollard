structure Product_Type : sig
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

fun apsnd f (x, y) = (x, f y);

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

end; (*struct Product_Type*)

structure Orderings : sig
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val max : 'a ord -> 'a -> 'a -> 'a
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

end; (*struct Orderings*)

structure HOL : sig
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

end; (*struct HOL*)

structure Arith : sig
  type nat
  val equal_nata : nat -> nat -> bool
  val equal_nat : nat HOL.equal
  val times_nata : nat -> nat -> nat
  type 'a times
  datatype num = One | Bit0 of num | Bit1 of num
  val one_nata : nat
  type 'a one
  val plus_nata : nat -> nat -> nat
  val zero_nata : nat
  type 'a power
  val power_nat : nat power
  val minus_nata : nat -> nat -> nat
  val divide_nata : nat -> nat -> nat
  val modulo_nata : nat -> nat -> nat
  type 'a semiring_modulo_trivial
  type 'a algebraic_semidom
  type 'a semidom_modulo
  val semidom_modulo_nat : nat semidom_modulo
  val suc : nat -> nat
  val dvd : 'a HOL.equal * 'a semidom_modulo -> 'a -> 'a -> bool
  val power : 'a power -> 'a -> nat -> 'a
  val less_nat : nat -> nat -> bool
  val nat_of_integer : IntInf.int -> nat
  val less_eq_nat : nat -> nat -> bool
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat HOL.equal;

fun times_nata m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

datatype num = One | Bit0 of num | Bit1 of num;

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int Orderings.ord;

fun minus_nata m n =
  Nat (Orderings.max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_nat = {minus = minus_nata} : nat minus;

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else Product_Type.apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun divide_integer k l = Product_Type.fst (divmod_integer k l);

fun divide_nata m n =
  Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

val divide_nat = {divide = divide_nata} : nat divide;

fun modulo_integer k l = Product_Type.snd (divmod_integer k l);

fun modulo_nata m n =
  Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

type 'a modulo =
  {divide_modulo : 'a divide, dvd_modulo : 'a dvd, modulo : 'a -> 'a -> 'a};
val divide_modulo = #divide_modulo : 'a modulo -> 'a divide;
val dvd_modulo = #dvd_modulo : 'a modulo -> 'a dvd;
val modulo = #modulo : 'a modulo -> 'a -> 'a -> 'a;

val modulo_nat =
  {divide_modulo = divide_nat, dvd_modulo = dvd_nat, modulo = modulo_nata} :
  nat modulo;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};
val semiring_0_semiring_no_zero_divisors = #semiring_0_semiring_no_zero_divisors
  : 'a semiring_no_zero_divisors -> 'a semiring_0;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};
val semiring_1_semiring_1_no_zero_divisors =
  #semiring_1_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_1;
val semiring_no_zero_divisors_semiring_1_no_zero_divisors =
  #semiring_no_zero_divisors_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_no_zero_divisors;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add,
    semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel =
  #cancel_comm_monoid_add_semiring_0_cancel :
  'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel :
  'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel,
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1,
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel =
  #comm_semiring_0_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel =
  #comm_semiring_1_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel =
  #semiring_1_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel,
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom :
  'a semidom -> 'a comm_semiring_1_cancel;
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom :
  'a semidom -> 'a semiring_1_no_zero_divisors;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

val comm_monoid_add_nat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat,
    monoid_add_comm_monoid_add = monoid_add_nat}
  : nat comm_monoid_add;

val mult_zero_nat = {times_mult_zero = times_nat, zero_mult_zero = zero_nat} :
  nat mult_zero;

val semigroup_mult_nat = {times_semigroup_mult = times_nat} :
  nat semigroup_mult;

val semiring_nat =
  {ab_semigroup_add_semiring = ab_semigroup_add_nat,
    semigroup_mult_semiring = semigroup_mult_nat}
  : nat semiring;

val semiring_0_nat =
  {comm_monoid_add_semiring_0 = comm_monoid_add_nat,
    mult_zero_semiring_0 = mult_zero_nat, semiring_semiring_0 = semiring_nat}
  : nat semiring_0;

val semiring_no_zero_divisors_nat =
  {semiring_0_semiring_no_zero_divisors = semiring_0_nat} :
  nat semiring_no_zero_divisors;

val monoid_mult_nat =
  {semigroup_mult_monoid_mult = semigroup_mult_nat,
    power_monoid_mult = power_nat}
  : nat monoid_mult;

val semiring_numeral_nat =
  {monoid_mult_semiring_numeral = monoid_mult_nat,
    numeral_semiring_numeral = numeral_nat,
    semiring_semiring_numeral = semiring_nat}
  : nat semiring_numeral;

val zero_neq_one_nat =
  {one_zero_neq_one = one_nat, zero_zero_neq_one = zero_nat} : nat zero_neq_one;

val semiring_1_nat =
  {semiring_numeral_semiring_1 = semiring_numeral_nat,
    semiring_0_semiring_1 = semiring_0_nat,
    zero_neq_one_semiring_1 = zero_neq_one_nat}
  : nat semiring_1;

val semiring_1_no_zero_divisors_nat =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_nat,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_nat}
  : nat semiring_1_no_zero_divisors;

val cancel_semigroup_add_nat =
  {semigroup_add_cancel_semigroup_add = semigroup_add_nat} :
  nat cancel_semigroup_add;

val cancel_ab_semigroup_add_nat =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_nat,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_nat,
    minus_cancel_ab_semigroup_add = minus_nat}
  : nat cancel_ab_semigroup_add;

val cancel_comm_monoid_add_nat =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_nat,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_nat}
  : nat cancel_comm_monoid_add;

val semiring_0_cancel_nat =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_nat,
    semiring_0_semiring_0_cancel = semiring_0_nat}
  : nat semiring_0_cancel;

val ab_semigroup_mult_nat =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
  nat ab_semigroup_mult;

val comm_semiring_nat =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat,
    semiring_comm_semiring = semiring_nat}
  : nat comm_semiring;

val comm_semiring_0_nat =
  {comm_semiring_comm_semiring_0 = comm_semiring_nat,
    semiring_0_comm_semiring_0 = semiring_0_nat}
  : nat comm_semiring_0;

val comm_semiring_0_cancel_nat =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_nat,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_nat}
  : nat comm_semiring_0_cancel;

val semiring_1_cancel_nat =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_nat,
    semiring_1_semiring_1_cancel = semiring_1_nat}
  : nat semiring_1_cancel;

val comm_monoid_mult_nat =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat,
    monoid_mult_comm_monoid_mult = monoid_mult_nat,
    dvd_comm_monoid_mult = dvd_nat}
  : nat comm_monoid_mult;

val comm_semiring_1_nat =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat,
    semiring_1_comm_semiring_1 = semiring_1_nat}
  : nat comm_semiring_1;

val comm_semiring_1_cancel_nat =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_nat,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_nat,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_nat}
  : nat comm_semiring_1_cancel;

val semidom_nat =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_nat,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_nat}
  : nat semidom;

type 'a divide_trivial =
  {one_divide_trivial : 'a one, zero_divide_trivial : 'a zero,
    divide_divide_trivial : 'a divide};
val one_divide_trivial = #one_divide_trivial : 'a divide_trivial -> 'a one;
val zero_divide_trivial = #zero_divide_trivial : 'a divide_trivial -> 'a zero;
val divide_divide_trivial = #divide_divide_trivial :
  'a divide_trivial -> 'a divide;

val divide_trivial_nat =
  {one_divide_trivial = one_nat, zero_divide_trivial = zero_nat,
    divide_divide_trivial = divide_nat}
  : nat divide_trivial;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};
val semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
  #semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
  'a semiring_no_zero_divisors_cancel -> 'a semiring_no_zero_divisors;

type 'a semidom_divide =
  {divide_trivial_semidom_divide : 'a divide_trivial,
    semidom_semidom_divide : 'a semidom,
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};
val divide_trivial_semidom_divide = #divide_trivial_semidom_divide :
  'a semidom_divide -> 'a divide_trivial;
val semidom_semidom_divide = #semidom_semidom_divide :
  'a semidom_divide -> 'a semidom;
val semiring_no_zero_divisors_cancel_semidom_divide =
  #semiring_no_zero_divisors_cancel_semidom_divide :
  'a semidom_divide -> 'a semiring_no_zero_divisors_cancel;

val semiring_no_zero_divisors_cancel_nat =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_nat}
  : nat semiring_no_zero_divisors_cancel;

val semidom_divide_nat =
  {divide_trivial_semidom_divide = divide_trivial_nat,
    semidom_semidom_divide = semidom_nat,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_nat}
  : nat semidom_divide;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel,
    modulo_semiring_modulo : 'a modulo};
val comm_semiring_1_cancel_semiring_modulo =
  #comm_semiring_1_cancel_semiring_modulo :
  'a semiring_modulo -> 'a comm_semiring_1_cancel;
val modulo_semiring_modulo = #modulo_semiring_modulo :
  'a semiring_modulo -> 'a modulo;

type 'a semiring_modulo_trivial =
  {divide_trivial_semiring_modulo_trivial : 'a divide_trivial,
    semiring_modulo_semiring_modulo_trivial : 'a semiring_modulo};
val divide_trivial_semiring_modulo_trivial =
  #divide_trivial_semiring_modulo_trivial :
  'a semiring_modulo_trivial -> 'a divide_trivial;
val semiring_modulo_semiring_modulo_trivial =
  #semiring_modulo_semiring_modulo_trivial :
  'a semiring_modulo_trivial -> 'a semiring_modulo;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};
val semidom_divide_algebraic_semidom = #semidom_divide_algebraic_semidom :
  'a algebraic_semidom -> 'a semidom_divide;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom,
    semiring_modulo_trivial_semidom_modulo : 'a semiring_modulo_trivial};
val algebraic_semidom_semidom_modulo = #algebraic_semidom_semidom_modulo :
  'a semidom_modulo -> 'a algebraic_semidom;
val semiring_modulo_trivial_semidom_modulo =
  #semiring_modulo_trivial_semidom_modulo :
  'a semidom_modulo -> 'a semiring_modulo_trivial;

val semiring_modulo_nat =
  {comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_nat,
    modulo_semiring_modulo = modulo_nat}
  : nat semiring_modulo;

val semiring_modulo_trivial_nat =
  {divide_trivial_semiring_modulo_trivial = divide_trivial_nat,
    semiring_modulo_semiring_modulo_trivial = semiring_modulo_nat}
  : nat semiring_modulo_trivial;

val algebraic_semidom_nat =
  {semidom_divide_algebraic_semidom = semidom_divide_nat} :
  nat algebraic_semidom;

val semidom_modulo_nat =
  {algebraic_semidom_semidom_modulo = algebraic_semidom_nat,
    semiring_modulo_trivial_semidom_modulo = semiring_modulo_trivial_nat}
  : nat semidom_modulo;

fun suc n = plus_nata n one_nata;

fun dvd (A1_, A2_) a b =
  HOL.eq A1_
    (modulo
      ((modulo_semiring_modulo o semiring_modulo_semiring_modulo_trivial o
         semiring_modulo_trivial_semidom_modulo)
        A2_)
      b a)
    (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_semidom o semidom_semidom_divide o
             semidom_divide_algebraic_semidom o
             algebraic_semidom_semidom_modulo)
            A2_));

fun power A_ a n =
  (if equal_nata n zero_nata then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nata n one_nata)));

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun nat_of_integer k = Nat (Orderings.max ord_integer (0 : IntInf.int) k);

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

end; (*struct Arith*)

structure GCD : sig
  val gcd_nat : Arith.nat -> Arith.nat -> Arith.nat
end = struct

fun gcd_nat x y =
  (if Arith.equal_nata y Arith.zero_nata then x
    else gcd_nat y (Arith.modulo_nata x y));

end; (*struct GCD*)

structure List : sig
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val insert : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val removeAll : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val all_interval_nat : (Arith.nat -> bool) -> Arith.nat -> Arith.nat -> bool
end = struct

fun member A_ [] y = false
  | member A_ (x :: xs) y = HOL.eq A_ x y orelse member A_ xs y;

fun insert A_ x xs = (if member A_ xs x then xs else x :: xs);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if HOL.eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun all_interval_nat p i j =
  Arith.less_eq_nat j i orelse p i andalso all_interval_nat p (Arith.suc i) j;

end; (*struct List*)

structure Set : sig
  type 'a set
  val insert : 'a HOL.equal -> 'a -> 'a set -> 'a set
  val member : 'a HOL.equal -> 'a -> 'a set -> bool
  val bot_set : 'a set
end = struct

datatype 'a set = Set of 'a list | Coset of 'a list;

fun insert A_ x (Coset xs) = Coset (List.removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (List.insert A_ x xs);

fun member A_ x (Coset xs) = not (List.member A_ xs x)
  | member A_ x (Set xs) = List.member A_ xs x;

val bot_set : 'a set = Set [];

end; (*struct Set*)

structure Primes : sig
  val prime_nat : Arith.nat -> bool
end = struct

fun prime_nat p =
  Arith.less_nat Arith.one_nata p andalso
    List.all_interval_nat
      (fn n => not (Arith.dvd (Arith.equal_nat, Arith.semidom_modulo_nat) n p))
      (Arith.suc Arith.one_nata) p;

end; (*struct Primes*)

structure Pollard : sig
  val g : Arith.nat -> Arith.nat -> Arith.nat
  val getQ : Arith.nat list -> Arith.nat
  val getd : Arith.nat -> Arith.nat list -> Arith.nat
  val cycle : Arith.nat -> Arith.nat -> Arith.nat list -> Arith.nat list
  val factorise : Arith.nat list -> Arith.nat list
  val rho : Arith.nat -> Arith.nat list
end = struct

fun g n x =
  Arith.modulo_nata
    (Arith.plus_nata
      (Arith.power Arith.power_nat x (Arith.nat_of_integer (2 : IntInf.int)))
      Arith.one_nata)
    n;

val primeset : Arith.nat Set.set =
  Set.insert Arith.equal_nat (Arith.nat_of_integer (2 : IntInf.int))
    (Set.insert Arith.equal_nat (Arith.nat_of_integer (3 : IntInf.int))
      (Set.insert Arith.equal_nat (Arith.nat_of_integer (5 : IntInf.int))
        (Set.insert Arith.equal_nat (Arith.nat_of_integer (7 : IntInf.int))
          (Set.insert Arith.equal_nat (Arith.nat_of_integer (11 : IntInf.int))
            (Set.insert Arith.equal_nat (Arith.nat_of_integer (13 : IntInf.int))
              (Set.insert Arith.equal_nat
                (Arith.nat_of_integer (17 : IntInf.int))
                (Set.insert Arith.equal_nat
                  (Arith.nat_of_integer (19 : IntInf.int))
                  (Set.insert Arith.equal_nat
                    (Arith.nat_of_integer (23 : IntInf.int))
                    (Set.insert Arith.equal_nat
                      (Arith.nat_of_integer (29 : IntInf.int))
                      (Set.insert Arith.equal_nat
                        (Arith.nat_of_integer (31 : IntInf.int))
                        (Set.insert Arith.equal_nat
                          (Arith.nat_of_integer (37 : IntInf.int))
                          (Set.insert Arith.equal_nat
                            (Arith.nat_of_integer (41 : IntInf.int))
                            (Set.insert Arith.equal_nat
                              (Arith.nat_of_integer (43 : IntInf.int))
                              (Set.insert Arith.equal_nat
                                (Arith.nat_of_integer (47 : IntInf.int))
                                (Set.insert Arith.equal_nat
                                  (Arith.nat_of_integer (53 : IntInf.int))
                                  (Set.insert Arith.equal_nat
                                    (Arith.nat_of_integer (59 : IntInf.int))
                                    (Set.insert Arith.equal_nat
                                      (Arith.nat_of_integer (61 : IntInf.int))
                                      (Set.insert Arith.equal_nat
(Arith.nat_of_integer (67 : IntInf.int))
(Set.insert Arith.equal_nat (Arith.nat_of_integer (71 : IntInf.int))
  (Set.insert Arith.equal_nat (Arith.nat_of_integer (73 : IntInf.int))
    (Set.insert Arith.equal_nat (Arith.nat_of_integer (79 : IntInf.int))
      (Set.insert Arith.equal_nat (Arith.nat_of_integer (83 : IntInf.int))
        (Set.insert Arith.equal_nat (Arith.nat_of_integer (89 : IntInf.int))
          (Set.insert Arith.equal_nat (Arith.nat_of_integer (97 : IntInf.int))
            (Set.insert Arith.equal_nat
              (Arith.nat_of_integer (101 : IntInf.int))
              (Set.insert Arith.equal_nat
                (Arith.nat_of_integer (103 : IntInf.int))
                (Set.insert Arith.equal_nat
                  (Arith.nat_of_integer (107 : IntInf.int))
                  (Set.insert Arith.equal_nat
                    (Arith.nat_of_integer (109 : IntInf.int))
                    (Set.insert Arith.equal_nat
                      (Arith.nat_of_integer (113 : IntInf.int))
                      (Set.insert Arith.equal_nat
                        (Arith.nat_of_integer (127 : IntInf.int))
                        (Set.insert Arith.equal_nat
                          (Arith.nat_of_integer (131 : IntInf.int))
                          (Set.insert Arith.equal_nat
                            (Arith.nat_of_integer (137 : IntInf.int))
                            (Set.insert Arith.equal_nat
                              (Arith.nat_of_integer (139 : IntInf.int))
                              (Set.insert Arith.equal_nat
                                (Arith.nat_of_integer (149 : IntInf.int))
                                (Set.insert Arith.equal_nat
                                  (Arith.nat_of_integer (151 : IntInf.int))
                                  (Set.insert Arith.equal_nat
                                    (Arith.nat_of_integer (157 : IntInf.int))
                                    (Set.insert Arith.equal_nat
                                      (Arith.nat_of_integer (163 : IntInf.int))
                                      (Set.insert Arith.equal_nat
(Arith.nat_of_integer (167 : IntInf.int))
(Set.insert Arith.equal_nat (Arith.nat_of_integer (173 : IntInf.int))
  (Set.insert Arith.equal_nat (Arith.nat_of_integer (179 : IntInf.int))
    (Set.insert Arith.equal_nat (Arith.nat_of_integer (181 : IntInf.int))
      (Set.insert Arith.equal_nat (Arith.nat_of_integer (191 : IntInf.int))
        (Set.insert Arith.equal_nat (Arith.nat_of_integer (193 : IntInf.int))
          (Set.insert Arith.equal_nat (Arith.nat_of_integer (197 : IntInf.int))
            (Set.insert Arith.equal_nat
              (Arith.nat_of_integer (199 : IntInf.int))
              (Set.insert Arith.equal_nat
                (Arith.nat_of_integer (211 : IntInf.int))
                (Set.insert Arith.equal_nat
                  (Arith.nat_of_integer (223 : IntInf.int))
                  (Set.insert Arith.equal_nat
                    (Arith.nat_of_integer (227 : IntInf.int))
                    (Set.insert Arith.equal_nat
                      (Arith.nat_of_integer (229 : IntInf.int))
                      (Set.insert Arith.equal_nat
                        (Arith.nat_of_integer (233 : IntInf.int))
                        (Set.insert Arith.equal_nat
                          (Arith.nat_of_integer (239 : IntInf.int))
                          (Set.insert Arith.equal_nat
                            (Arith.nat_of_integer (241 : IntInf.int))
                            (Set.insert Arith.equal_nat
                              (Arith.nat_of_integer (251 : IntInf.int))
                              (Set.insert Arith.equal_nat
                                (Arith.nat_of_integer (257 : IntInf.int))
                                (Set.insert Arith.equal_nat
                                  (Arith.nat_of_integer (263 : IntInf.int))
                                  (Set.insert Arith.equal_nat
                                    (Arith.nat_of_integer (269 : IntInf.int))
                                    (Set.insert Arith.equal_nat
                                      (Arith.nat_of_integer (271 : IntInf.int))
                                      (Set.insert Arith.equal_nat
(Arith.nat_of_integer (277 : IntInf.int))
(Set.insert Arith.equal_nat (Arith.nat_of_integer (281 : IntInf.int))
  (Set.insert Arith.equal_nat (Arith.nat_of_integer (283 : IntInf.int))
    (Set.insert Arith.equal_nat (Arith.nat_of_integer (293 : IntInf.int))
      Set.bot_set)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));

fun prime x = (if Set.member Arith.equal_nat x primeset then true else false);

fun getQ [] = Arith.one_nata
  | getQ [x] = Arith.one_nata
  | getQ (x :: y :: xs) = Arith.times_nata (Arith.minus_nata y x) (getQ xs);

fun getd n xs = let
                  val q = Arith.modulo_nata (getQ xs) n;
                in
                  GCD.gcd_nat q n
                end;

fun cycle i n (x :: y :: xs) =
  let
    val d = Arith.modulo_nata (getd n (x :: y :: xs)) n;
    val p = Arith.divide_nata n d;
  in
    (if Arith.less_nat (Arith.nat_of_integer (1000 : IntInf.int)) i then xs
      else (if Arith.less_nat Arith.one_nata d andalso Arith.less_nat d n
             then (if prime p andalso Primes.prime_nat d
                    then [d, Arith.divide_nata n d]
                    else (if prime p
                           then p :: cycle (Arith.plus_nata i Arith.one_nata) d
                                       [Arith.nat_of_integer (2 : IntInf.int),
 g d (Arith.nat_of_integer (2 : IntInf.int))]
                           else (if prime d
                                  then d ::
 cycle (Arith.plus_nata i Arith.one_nata) p
   [Arith.nat_of_integer (2 : IntInf.int),
     g p (Arith.nat_of_integer (2 : IntInf.int))]
                                  else cycle (Arith.plus_nata i Arith.one_nata)
 d [Arith.nat_of_integer (2 : IntInf.int),
     g d (Arith.nat_of_integer (2 : IntInf.int))] @
 cycle (Arith.plus_nata i Arith.one_nata) p
   [Arith.nat_of_integer (2 : IntInf.int),
     g p (Arith.nat_of_integer (2 : IntInf.int))])))
             else cycle (Arith.plus_nata i Arith.one_nata) n
                    [g n x, g n (g n y)]))
  end
  | cycle i n [] = []
  | cycle i n [uu] = [];

fun factorise (x :: xs) =
  (if prime x then x :: factorise xs
    else cycle Arith.one_nata x
           [Arith.nat_of_integer (2 : IntInf.int),
             g x (Arith.nat_of_integer (2 : IntInf.int))]) @
    factorise xs
  | factorise [] = [];

fun rho x = (if prime x then [x] else factorise [x]);

end; (*struct Pollard*)
