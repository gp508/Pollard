{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module GCD(gcd_nat) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Arith;

gcd_nat :: Arith.Nat -> Arith.Nat -> Arith.Nat;
gcd_nat x y =
  (if Arith.equal_nat y Arith.zero_nat then x
    else gcd_nat y (Arith.modulo_nat x y));

}
