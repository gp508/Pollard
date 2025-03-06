import System.Process
import System.IO

main :: IO ()
main = do
    (_, Just hout, _, _) <- createProcess (shell "sage -c 'print(is_prime(68543))'") { std_out = CreatePipe }
    output <- hGetContents hout
    putStrLn output
