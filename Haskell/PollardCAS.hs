{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module PollardCAS(rho) where

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified GCD;
import qualified HOL;
import qualified Primes;
import qualified Arith;
import Sage;

g :: Arith.Nat -> Arith.Nat -> Arith.Nat;
g n x =
  Arith.modulo_nat
    (Arith.plus_nat (Arith.power x (Arith.nat_of_integer (2 :: Integer)))
      Arith.one_nat)
    n;

getQ :: [Arith.Nat] -> Arith.Nat;
getQ [] = Arith.one_nat;
getQ [x] = Arith.one_nat;
getQ (x : y : xs) = Arith.times_nat (Arith.minus_nat y x) (getQ xs);

getd :: Arith.Nat -> [Arith.Nat] -> Prelude.IO Arith.Nat;
getd n xs = let {
              q = Arith.modulo_nat (getQ xs) n;
            } in gcdSage q n;

cycle :: Arith.Nat -> Arith.Nat -> Arith.Nat -> Arith.Nat -> Prelude.IO Arith.Nat
cycle i n x y = do
    d <- getd n [x, y]  -- Extract `d` from IO
    let dMod = Arith.modulo_nat d n  -- Apply modulo
    if Arith.equal_nat i Arith.zero_nat
        then return Arith.one_nat
        else if Arith.less_nat Arith.one_nat dMod && Arith.less_nat dMod n
            then return dMod
            else cycle (Arith.minus_nat i Arith.one_nat) n (g n x) (g n (g n y))



rho :: Arith.Nat -> Prelude.IO Arith.Nat;
rho n =
  (if Primes.prime_nat n then return n
    else cycle (Arith.nat_of_integer (1000 :: Integer)) n (Arith.nat_of_integer (2 :: Integer))
           (Arith.nat_of_integer (2 :: Integer)));


--gcd :: Arith.Nat -> Arith.Nat -> Arith.Nat
--gcd x y =
--    hGetContents ((_, Just hout, _, _) <- createProcess (shell "sage -c 'print(gcd(x,y))'") { std_out = CreatePipe })

