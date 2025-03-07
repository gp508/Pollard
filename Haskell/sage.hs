module Sage (gcdSage) where

import System.Process
import System.IO
import qualified Arith 

lala :: Integer -> Arith.Nat
lala x = Arith.nat_of_integer x

gcdSage :: Arith.Nat -> Arith.Nat -> IO Arith.Nat
gcdSage x y = do
    let command = "sage -c 'print(gcd(" ++ show (Arith.integer_of_nat x) ++ "," ++ show (Arith.integer_of_nat y) ++ "))'"
    (_, Just hout, _, _) <- createProcess (shell command) { std_out = CreatePipe }
    output <- hGetContents hout
    return (Arith.nat_of_integer(read(init output)))