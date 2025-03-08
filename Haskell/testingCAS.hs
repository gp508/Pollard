import PollardCAS
import Arith

main :: IO ()
main = test 10

test :: Integer -> IO()
test x = do
    result <- rho (Arith.nat_of_integer x)
    let integerResult = Arith.integer_of_nat result  
    putStrLn (show integerResult) 
