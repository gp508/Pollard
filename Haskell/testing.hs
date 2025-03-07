import PollardCAS
import Arith

main :: IO ()
main = do
    result <- rho (Arith.nat_of_integer 3558539)
    let integerResult = Arith.integer_of_nat result  
    putStrLn (show integerResult) 
