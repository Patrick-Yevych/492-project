main :: IO ()    -- This says that main is an IO action.
main = return () -- This tells main to do nothing.

data Expr
    = Var Name
    | Pi Name Expr Expr
    | Lambda Name Expr
    | App Expr Expr
    | Sigma Name Expr Expr
    | Cons Expr Expr
    | Car Expr
    | Cdr Expr
    | Nat
    | Zero
    | Add1 Expr
    | IndNat Expr Expr Expr Expr
    | Equal Expr Expr Expr
    | Same
    | Replace Expr Expr Expr
    | Trivial
    | Sole
    | Absurd
    | IndAbsurd Expr Expr
    | Atom
    | Tick String
    | U
    | The Expr Expr
    deriving (Eq, Show)

data Value
    = VClosure (Env Value) Name Expr
    deriving Show

newtype Name = Name String
    deriving (Show, Eq)

newtype Env val = Env [(Name, val)]
    deriving Show

newtype Message = Message String
    deriving Show

initEnv :: Env val
initEnv = Env [ ]

failure :: String -> Either Message a
failure msg = Left (Message msg)

lookupVar :: Env val -> Name -> Either Message val
lookupVar (Env [ ]) (Name x) =
    failure ("Not found: " ++ x)
lookupVar (Env ((y, v) : env0)) x
    | y == x = Right v
    | otherwise = lookupVar (Env env0) x

extend :: Env val -> Name -> val -> Env val
extend (Env env) x v = Env ((x, v) : env)

eval :: Env Value -> Expr -> Either Message Value
eval env (Var x) = lookupVar env x
eval env (Lambda x body) = Right (VClosure env x body)
eval env (App rator rand) = 
    do fun <- eval env rator
       arg <- eval env rand
       doApply fun arg

doApply :: Value -> Value -> Either Message Value
doApply (VClosure env x body) arg = eval (extend env x arg) body

instance Functor Env where
    fmap f (Env xs) = Env (map (\x -> ((fst x), f (snd x))) xs)  -- Note: check this out later 

runProgram :: [(Name, Expr)] -> Expr -> Either Message Value
runProgram defs expr = do 
    env <- addDefs initEnv defs
    eval env expr

addDefs :: Env Value -> [(Name, Expr)] -> Either Message (Env Value)
addDefs env [ ] = Right env
addDefs env ((x, e) : defs) = do 
    v <- eval env e
    addDefs (extend env x v) defs



-- Church Numerals testing begin


test :: Either Message Value
test =
    runProgram churchDefs
        (App (App (Var (Name "+"))
                (toChurch 2))
            (toChurch 3))

churchDefs :: [(Name, Expr)]
churchDefs =
    [ (Name "zero",
        Lambda (Name "f")
            (Lambda (Name "x")
                (Var (Name "x"))))
    , (Name "add1",
    Lambda (Name "n")
        (Lambda (Name "f")
            (Lambda (Name "x")
                (App (Var (Name "f"))
                    (App (App (Var (Name "n"))
                        (Var (Name "f")))
                            (Var (Name "x")))))))
    , (Name "+",
        Lambda (Name "j")
            (Lambda (Name "k")
                (Lambda (Name "f")
                    (Lambda (Name "x")
                        (App (App (Var (Name "j")) (Var (Name "f")))
                            (App (App (Var (Name "k")) (Var (Name "f")))
                                (Var (Name "x"))))))))
    ]
toChurch :: Integer -> Expr
toChurch n
    | n <= 0 = Var (Name "zero")
    | otherwise = App (Var (Name "add1")) (toChurch (n - 1))

-- Church Numerals testing end



freshen :: [Name] -> Name -> Name
freshen used x
    | elem x used = freshen used (nextName x)
    | otherwise = x
    
nextName :: Name -> Name
nextName (Name x) = Name (x ++ "'")
