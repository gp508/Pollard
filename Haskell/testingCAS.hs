import PollardCAS
import Arith

main :: IO ()
main = test [21]

test :: [Integer] -> IO ()
test [] = putStrLn("")
test (x:xs) = do
    result <- rho (Arith.nat_of_integer x) 
    let integerResult = Arith.integer_of_nat result
    putStrLn (show integerResult)
    test xs 
