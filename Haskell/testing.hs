import Pollard
import Arith

main :: IO ()
main = sequence_ (test [45,135,3383976097])

test :: [Integer] -> [IO()]
test [] = []
test (x:xs) = 
    putStrLn (show (Arith.integer_of_nat(rho (Arith.nat_of_integer x)))) : test xs

