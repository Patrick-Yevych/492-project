{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
import System.Environment (getArgs)
import System.IO (IOMode (ReadMode), openFile)
import Lang
import Parse
import Eval

evalTop :: Expr -> Value
evalTop e = eval (Env []) initDlt e id

-- Reference: https://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours/Evaluation,_Part_1
main :: IO ()
main = getArgs >>= print . evalTop . readExpr . head