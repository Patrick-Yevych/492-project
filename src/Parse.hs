-- Reference: https://en.wikibooks.org/wiki Write_Yourself_a_Scheme_in_48_Hours/Parsing
-- For spaces, printExpr, readExpr
module Parse where
import Text.ParserCombinators.Parsec hiding (spaces)
import System.Environment
import Control.Monad
import Top
import Lang

spaces :: Parser ()
spaces = skipMany1 space

parseName :: Parser Name
parseName = do
    f <- letter
    r  <- many (letter <|> digit)
    return $ Name (f:r)

parseVar :: Parser Expr
parseVar = do
    nm <- parseName
    return $ Var nm

parseAtom :: Parser Expr
parseAtom = do
    char '\''
    f <- letter
    r  <- many (letter <|> digit)
    return $ Tick (f:r)

desugarNat :: Integer -> Expr
desugarNat 0 = Zero
desugarNat n = Add1 $ desugarNat (n-1)

parseNum :: Parser Expr
parseNum = liftM (desugarNat . read) $ many1 digit

desugarLambda :: [Name] -> Expr -> Expr
desugarLambda [] body = body
desugarLambda (x:xs) body = Lambda x (desugarLambda xs body)

parseLambda :: Parser Expr
parseLambda = do
    char '('
    string "lambda"
    spaces
    char '('
    args <- sepBy parseName spaces
    char ')'
    spaces
    body <- parseExpr
    char ')'
    return $ desugarLambda args body

parseBind :: Parser (Name, Expr)
parseBind = do
    char '('
    x <- parseName
    spaces
    xT <- parseExpr
    char ')'
    return $ (x, xT)

desugarPi :: [(Name, Expr)] -> Expr -> Expr
desugarPi [] body = body
desugarPi (x:xs) body = Pi (fst x) (snd x) (desugarPi xs body)

parsePi :: Parser Expr
parsePi = do
    char '('
    string "Pi"
    spaces
    string "("
    binds <- sepBy parseBind spaces
    string ")"
    spaces
    body <- parseExpr
    char ')'
    return $ desugarPi binds body

desugarSigma :: [(Name, Expr)] -> Expr -> Expr
desugarSigma [] body = body
desugarSigma (x : xs) body = Sigma (fst x) (snd x) (desugarSigma xs body)

parseSigma :: Parser Expr
parseSigma = do
    char '('
    string "Sigma"
    spaces
    string "("
    binds <- sepBy parseBind spaces
    string ")"
    spaces
    body <- parseExpr
    char ')'
    return $ desugarSigma binds body

parseApp :: Parser Expr
parseApp = do
    char '('
    rator <- parseExpr
    spaces
    rand <- parseExpr
    char ')'
    return $ App rator rand

parseCons :: Parser Expr
parseCons = do
    char '('
    string "cons"
    spaces
    a <- parseExpr
    spaces
    d <- parseExpr
    char ')'
    return $ Cons a d

parseCar :: Parser Expr
parseCar = do
    char '('
    string "car"
    spaces
    a <- parseExpr
    char ')'
    return $ Car a

parseCdr :: Parser Expr
parseCdr = do
    char '('
    string "cdr"
    spaces
    d <- parseExpr
    char ')'
    return $ Cdr d

parseAdd :: Parser Expr
parseAdd = do
    char '('
    string "add1"
    spaces
    n <- parseExpr
    char ')'
    return $ Add1 n

parseIndNat :: Parser Expr
parseIndNat = do
    char '('
    string "ind-Nat"
    spaces
    tar <- parseExpr
    spaces
    mot <- parseExpr
    spaces
    base <- parseExpr
    spaces
    step <- parseExpr
    char ')'
    return $ IndNat tar mot base step

parseEq :: Parser Expr
parseEq = do
    char '('
    char '='
    spaces
    x <- parseExpr
    spaces
    from <- parseExpr
    spaces
    to <- parseExpr
    char ')'
    return $ Equal x from to

parseReplace :: Parser Expr
parseReplace = do
    char '('
    string "replace"
    spaces
    tar <- parseExpr
    spaces
    mot <- parseExpr
    spaces
    base <- parseExpr
    char ')'
    return $ Replace tar mot base

parseIndAbsurd :: Parser Expr
parseIndAbsurd = do
    char '('
    string "ind-Absurd"
    spaces
    tar <- parseExpr
    spaces
    mot <- parseExpr
    char ')'
    return $ IndAbsurd tar mot

parseThe :: Parser Expr
parseThe = do
    char '('
    string "the"
    spaces
    ty <- parseExpr
    spaces
    expr <- parseExpr
    char ')'
    return $ The ty expr

parseClr :: Parser Expr
parseClr = do
    char '('
    string "clr"
    spaces
    body <- parseExpr
    char ')'
    return $ Clr body

parseShf :: Parser Expr
parseShf = do
    char '('
    string "shf"
    spaces
    mu <- parseName
    spaces
    body <- parseExpr
    char ')'
    return $ Shf mu body

-- parseCnt :: Parser Expr
-- parseCnt = do
--     char '('
--     string "cnt"
--     spaces
--     mu <- parseName
--     spaces
--     app <- parseExpr
--     char ')'
--     return $ Cnt mu app

parseJmp :: Parser Expr
parseJmp = do
    char '('
    string "jmp"
    spaces
    mu <- parseName
    spaces
    app <- parseExpr
    char ')'
    return $ Jmp mu app

parseExpr :: Parser Expr
parseExpr = try parseAtom
    <|> try parseNum
    <|> try parsePi
    <|> try parseLambda
    <|> try parseSigma
    <|> try parseCons
    <|> try parseCar
    <|> try parseCdr
    <|> do string "Nat" 
           return Nat
    <|> do string "zero"
           return Zero
    <|> try parseAdd
    <|> try parseIndNat
    <|> try parseEq
    <|> do string "same"
           return Same
    <|> try parseReplace
    <|> do string "Trivial"
           return Trivial
    <|> do string "Sole"
           return Sole
    <|> do string "Absurd"
           return Absurd
    <|> try parseIndAbsurd
    <|> do string "Atom"
           return Atom
    <|> do string "U"
           return U
    <|> try parseThe
    <|> try parseClr
    <|> try parseShf
    <|> try parseJmp
    <|> try parseApp
    <|> try parseVar
    -- <|> try parseCnt


printExpr :: String -> String
printExpr input = case parse parseExpr "lisp" input of
  Left err -> "No match: " ++ show err
  Right val -> "Found: " ++ show val

readExpr :: String -> Expr
readExpr input = case parse parseExpr "lisp" input of
  Left err -> error $ "No match: " ++ show err
  Right val -> val