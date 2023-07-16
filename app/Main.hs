import System.Environment (getArgs)
import System.IO (IOMode(ReadMode), openFile)

main :: IO ()
main = do
    args <- getArgs
    fp   <- openFile (head args) ReadMode
    putStrLn "Hello, Haskell!"