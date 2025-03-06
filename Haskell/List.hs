{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module List(all_interval_nat) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Arith;

all_interval_nat :: (Arith.Nat -> Bool) -> Arith.Nat -> Arith.Nat -> Bool;
all_interval_nat p i j =
  Arith.less_eq_nat j i || p i && all_interval_nat p (Arith.suc i) j;

}
