{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Str(Char, integer_of_char) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Arith;

data Char = Char Bool Bool Bool Bool Bool Bool Bool Bool;

integer_of_char :: Char -> Integer;
integer_of_char (Char b0 b1 b2 b3 b4 b5 b6 b7) =
  ((((((Arith.of_bool b7 * (2 :: Integer) + Arith.of_bool b6) * (2 :: Integer) +
        Arith.of_bool b5) *
        (2 :: Integer) +
       Arith.of_bool b4) *
       (2 :: Integer) +
      Arith.of_bool b3) *
      (2 :: Integer) +
     Arith.of_bool b2) *
     (2 :: Integer) +
    Arith.of_bool b1) *
    (2 :: Integer) +
    Arith.of_bool b0;

}
