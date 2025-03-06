{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Primes(prime_nat) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified List;
import qualified Arith;

prime_nat :: Arith.Nat -> Bool;
prime_nat p =
  Arith.less_nat Arith.one_nat p &&
    List.all_interval_nat (\ n -> not (Arith.dvd n p)) (Arith.suc Arith.one_nat)
      p;

}
