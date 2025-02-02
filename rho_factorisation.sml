structure Product_Type : sig
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

end; (*struct Product_Type*)

structure Arith : sig
  datatype nat = Zero_nat | Suc of nat
  val one_nata : nat
  type 'a one
  val plus_nat : nat -> nat -> nat
  val times_nata : nat -> nat -> nat
  type 'a times
  type 'a power
  val power_nat : nat power
  datatype num = One | Bit0 of num | Bit1 of num
  val nat_of_num : num -> nat
  val power : 'a power -> 'a -> nat -> 'a
  val less_nat : nat -> nat -> bool
  val minus_nat : nat -> nat -> nat
  val equal_nat : nat -> nat -> bool
  val divide_nat : nat -> nat -> nat
  val modulo_nat : nat -> nat -> nat
end = struct

datatype nat = Zero_nat | Suc of nat;

val one_nata : nat = Suc Zero_nat;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat n = n;

fun times_nata Zero_nat n = Zero_nat
  | times_nata (Suc m) n = plus_nat n (times_nata m n);

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_nat = {times = times_nata} : nat times;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

datatype num = One | Bit0 of num | Bit1 of num;

fun nat_of_num (Bit1 n) = let
                            val m = nat_of_num n;
                          in
                            Suc (plus_nat m m)
                          end
  | nat_of_num (Bit0 n) = let
                            val m = nat_of_num n;
                          in
                            plus_nat m m
                          end
  | nat_of_num One = one_nata;

fun power A_ a Zero_nat = one (one_power A_)
  | power A_ a (Suc n) = times (times_power A_) a (power A_ a n);

fun less_nat m (Suc n) = less_eq_nat m n
  | less_nat n Zero_nat = false
and less_eq_nat (Suc m) n = less_nat m n
  | less_eq_nat Zero_nat n = true;

fun minus_nat (Suc m) (Suc n) = minus_nat m n
  | minus_nat Zero_nat n = Zero_nat
  | minus_nat m Zero_nat = m;

fun equal_nat Zero_nat (Suc x2) = false
  | equal_nat (Suc x2) Zero_nat = false
  | equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2
  | equal_nat Zero_nat Zero_nat = true;

fun divmod_nat m n =
  (if equal_nat n Zero_nat orelse less_nat m n then (Zero_nat, m)
    else let
           val (q, a) = divmod_nat (minus_nat m n) n;
         in
           (Suc q, a)
         end);

fun divide_nat m n = Product_Type.fst (divmod_nat m n);

fun modulo_nat m n = Product_Type.snd (divmod_nat m n);

end; (*struct Arith*)

structure GCD : sig
  val gcd_nat : Arith.nat -> Arith.nat -> Arith.nat
end = struct

fun gcd_nat x y =
  (if Arith.equal_nat y Arith.Zero_nat then x
    else gcd_nat y (Arith.modulo_nat x y));

end; (*struct GCD*)

structure Pollard : sig
  val rho : Arith.nat -> Arith.nat list
end = struct

fun g x =
  Arith.plus_nat
    (Arith.power Arith.power_nat x (Arith.nat_of_num (Arith.Bit0 Arith.One)))
    Arith.one_nata;

fun prime x =
  (if Arith.equal_nat x (Arith.nat_of_num (Arith.Bit0 Arith.One)) then true
    else (if Arith.equal_nat x (Arith.nat_of_num (Arith.Bit1 Arith.One))
           then true else false));

fun getQ [] = Arith.one_nata
  | getQ [x] = Arith.one_nata
  | getQ (x :: y :: xs) =
    Arith.times_nata (Arith.minus_nat y x) (getQ (y :: xs));

fun getd n xs = let
                  val q = getQ xs;
                in
                  GCD.gcd_nat q n
                end;

fun cycle i n (x :: y :: xs) =
  let
    val d = Arith.modulo_nat (getd n xs) n;
  in
    (if Arith.less_nat
          (Arith.nat_of_num
            (Arith.Bit0
              (Arith.Bit0
                (Arith.Bit0
                  (Arith.Bit1
                    (Arith.Bit0
                      (Arith.Bit1
                        (Arith.Bit1 (Arith.Bit1 (Arith.Bit1 Arith.One))))))))))
          i
      then xs
      else (if Arith.less_nat i d andalso Arith.less_nat d n
             then [d, Arith.divide_nat n d]
             else cycle (Arith.plus_nat i Arith.one_nata) n
                    [g x, g (g x), x, y]))
  end
  | cycle i n [] = []
  | cycle i n [uu] = [];

fun factorise (x :: xs) =
  (if prime x then x :: factorise xs
    else cycle Arith.one_nata x
           [Arith.nat_of_num (Arith.Bit0 Arith.One),
             Arith.nat_of_num (Arith.Bit0 Arith.One)])
  | factorise [] = [];

fun rho x = (if prime x then [x] else factorise [x]);

end; (*struct Pollard*)
