{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Arith(Nat, equal_nat, times_nat, Times, Num(..), one_nat, One, plus_nat,
         zero_nat, Power, minus_nat, modulo_nat, Semiring_modulo_trivial,
         Algebraic_semidom, Semidom_modulo, suc, dvd, power, less_nat,
         nat_of_integer, less_eq_nat)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Product_Type;
import qualified Orderings;

newtype Nat = Nat Integer;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

times_nat :: Nat -> Nat -> Nat;
times_nat m n = Nat (integer_of_nat m * integer_of_nat n);

class Times a where {
  times :: a -> a -> a;
};

class (Times a) => Dvd a where {
};

instance Times Nat where {
  times = times_nat;
};

instance Dvd Nat where {
};

data Num = One | Bit0 Num | Bit1 Num;

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

class One a where {
  one :: a;
};

instance One Nat where {
  one = one_nat;
};

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Nat where {
  plus = plus_nat;
};

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

class Zero a where {
  zero :: a;
};

instance Zero Nat where {
  zero = zero_nat;
};

class (Plus a) => Semigroup_add a where {
};

class (One a, Semigroup_add a) => Numeral a where {
};

instance Semigroup_add Nat where {
};

instance Numeral Nat where {
};

class (One a, Times a) => Power a where {
};

instance Power Nat where {
};

instance Orderings.Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n =
  Nat (Orderings.max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

class Minus a where {
  minus :: a -> a -> a;
};

instance Minus Nat where {
  minus = minus_nat;
};

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else Product_Type.apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

class Divide a where {
  divide :: a -> a -> a;
};

instance Divide Nat where {
  divide = divide_nat;
};

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

class (Divide a, Dvd a) => Modulo a where {
  modulo :: a -> a -> a;
};

instance Modulo Nat where {
  modulo = modulo_nat;
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Times a, Zero a) => Mult_zero a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

class (Semiring_0 a) => Semiring_no_zero_divisors a where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

class (Semiring_1 a,
        Semiring_no_zero_divisors a) => Semiring_1_no_zero_divisors a where {
};

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class (Ab_semigroup_add a, Cancel_semigroup_add a,
        Minus a) => Cancel_ab_semigroup_add a where {
};

class (Cancel_ab_semigroup_add a,
        Comm_monoid_add a) => Cancel_comm_monoid_add a where {
};

class (Cancel_comm_monoid_add a, Semiring_0 a) => Semiring_0_cancel a where {
};

class (Semigroup_mult a) => Ab_semigroup_mult a where {
};

class (Ab_semigroup_mult a, Semiring a) => Comm_semiring a where {
};

class (Comm_semiring a, Semiring_0 a) => Comm_semiring_0 a where {
};

class (Comm_semiring_0 a,
        Semiring_0_cancel a) => Comm_semiring_0_cancel a where {
};

class (Semiring_0_cancel a, Semiring_1 a) => Semiring_1_cancel a where {
};

class (Ab_semigroup_mult a, Monoid_mult a, Dvd a) => Comm_monoid_mult a where {
};

class (Comm_monoid_mult a, Comm_semiring_0 a,
        Semiring_1 a) => Comm_semiring_1 a where {
};

class (Comm_semiring_0_cancel a, Comm_semiring_1 a,
        Semiring_1_cancel a) => Comm_semiring_1_cancel a where {
};

class (Comm_semiring_1_cancel a,
        Semiring_1_no_zero_divisors a) => Semidom a where {
};

instance Ab_semigroup_add Nat where {
};

instance Monoid_add Nat where {
};

instance Comm_monoid_add Nat where {
};

instance Mult_zero Nat where {
};

instance Semigroup_mult Nat where {
};

instance Semiring Nat where {
};

instance Semiring_0 Nat where {
};

instance Semiring_no_zero_divisors Nat where {
};

instance Monoid_mult Nat where {
};

instance Semiring_numeral Nat where {
};

instance Zero_neq_one Nat where {
};

instance Semiring_1 Nat where {
};

instance Semiring_1_no_zero_divisors Nat where {
};

instance Cancel_semigroup_add Nat where {
};

instance Cancel_ab_semigroup_add Nat where {
};

instance Cancel_comm_monoid_add Nat where {
};

instance Semiring_0_cancel Nat where {
};

instance Ab_semigroup_mult Nat where {
};

instance Comm_semiring Nat where {
};

instance Comm_semiring_0 Nat where {
};

instance Comm_semiring_0_cancel Nat where {
};

instance Semiring_1_cancel Nat where {
};

instance Comm_monoid_mult Nat where {
};

instance Comm_semiring_1 Nat where {
};

instance Comm_semiring_1_cancel Nat where {
};

instance Semidom Nat where {
};

class (One a, Zero a, Divide a) => Divide_trivial a where {
};

instance Divide_trivial Nat where {
};

class (Semiring_no_zero_divisors a) => Semiring_no_zero_divisors_cancel a where {
};

class (Divide_trivial a, Semidom a,
        Semiring_no_zero_divisors_cancel a) => Semidom_divide a where {
};

instance Semiring_no_zero_divisors_cancel Nat where {
};

instance Semidom_divide Nat where {
};

class (Comm_semiring_1_cancel a, Modulo a) => Semiring_modulo a where {
};

class (Divide_trivial a, Semiring_modulo a) => Semiring_modulo_trivial a where {
};

class (Semidom_divide a) => Algebraic_semidom a where {
};

class (Algebraic_semidom a,
        Semiring_modulo_trivial a) => Semidom_modulo a where {
};

instance Semiring_modulo Nat where {
};

instance Semiring_modulo_trivial Nat where {
};

instance Algebraic_semidom Nat where {
};

instance Semidom_modulo Nat where {
};

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

dvd :: forall a. (Eq a, Semidom_modulo a) => a -> a -> Bool;
dvd a b = modulo b a == zero;

power :: forall a. (Power a) => a -> Nat -> a;
power a n =
  (if equal_nat n zero_nat then one
    else times a (power a (minus_nat n one_nat)));

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (Orderings.max (0 :: Integer) k);

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

}
