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
    | Rec Ty Expr Expr Expr -- TODO Delete this later
    | Ann Expr Ty  -- TODO Delete this later
    deriving (Eq, Show)

data Value
    = VClosure (Env Value) Name Expr
    | VNeutral Neutral
    deriving Show

data Neutral
    = NVar Name
    | NApp Neutral Value
    deriving (Show)

-- type stuff

data Ty
    = TNat
    | TArr Ty Ty
    deriving (Eq, Show)

type Context = Env Ty
initCtx :: Context
initCtx = initEnv

synth :: Context -> Expr -> Either Message Ty
synth ctx (Var x) = lookupVar ctx x     -- variables
synth ctx (App rator rand) = do         -- function application
    ty <- synth ctx rator
    case ty of
        TArr argT retT -> do 
            check ctx rand argT
            Right retT
        other -> failure ("Not a function type: " ++ show other)
synth ctx (Rec ty tgt base step) = do   -- recursion
    tgtT <- synth ctx tgt
    case tgtT of
        TNat -> do 
            check ctx base tgtT
            check ctx step (TArr TNat (TArr ty ty))
            Right ty
        other -> failure ("Not the type Nat: " ++ show other)
synth ctx (Ann e t) = do                -- function annotation 
    check ctx e t
    Right t
synth _ other =                         -- failure
    failure ("Can't find a type for " ++ show other ++ ". " ++
        "Try adding a type annotation.")

check :: Context -> Expr -> Ty -> Either Message ()
check ctx (Lambda x body) t =           -- lambda
    case t of
        TArr arg ret -> check (extend ctx x arg) body ret
        other -> failure ("Lambda requires a function type, but got " ++ show other)
check ctx Zero t =                      -- zero
    case t of
        TNat -> Right ()
        other -> failure ("Zero should be a Nat, but was used where a " ++ show other ++ " was expected")
check ctx (Add1 n) t =                  -- successor
    case t of
        TNat -> check ctx n TNat
        other -> failure ("Add1 should be a Nat, but was used where a " ++ show other ++ " was expected")
check ctx other t = do                  -- mode change
    t' <- synth ctx other
    if t' == t
        then Right ()
        else failure ("Expected " ++ show t ++ " but got " ++ show t')

-- end stuff

newtype Name = Name String
    deriving (Show, Eq)

newtype Env val = Env [(Name, val)]
    deriving Show

newtype Message = Message String
    deriving Show

instance Functor Env where
    fmap f (Env xs) = Env (map (\x -> ((fst x), f (snd x))) xs)  -- Note: check this out later 

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
eval env (App rator rand) = do
        fun <- eval env rator
        arg <- eval env rand
        doApply fun arg


doApply :: Value -> Value -> Either Message Value
doApply (VClosure env x body) arg = eval (extend env x arg) body
doApply (VNeutral neu) arg = Right (VNeutral (NApp neu arg))

readBack :: [Name] -> Value -> Either Message Expr
readBack used (VNeutral (NVar x)) = Right (Var x)
readBack used (VNeutral (NApp fun arg)) = do 
    rator <- readBack used (VNeutral fun)
    rand <- readBack used arg
    Right (App rator rand)
readBack used fun@(VClosure _ x _) = 
    let x' = freshen used x
    in do
        bodyVal <- doApply fun (VNeutral (NVar x'))
        bodyExpr <- readBack (x' : used) bodyVal
        Right (Lambda x' bodyExpr)

normalize :: Expr -> Either Message Expr
normalize expr = do 
    val <- eval initEnv expr
    readBack [ ] val

-- runProgram :: [(Name, Expr)] -> Expr -> Either Message Expr
-- runProgram defs expr = do 
--     env <- addDefs initEnv defs
--     val <- eval env expr
--     readBack (map fst defs) val

addDefs :: Context -> [(Name, Expr)] -> Either Message Context
addDefs ctx [ ] = Right ctx
addDefs ctx ((x, e) : defs) = do 
    t <- synth ctx e
    addDefs (extend ctx x t) defs


-- Church Numerals testing begin


test :: Either Message (Ty, Ty)
test = do 
    ctx <- addDefs initCtx
                [(Name "two",
                    (Ann (Add1 (Add1 Zero))
                        TNat)),
                 (Name "three",
                    (Ann (Add1 (Add1 (Add1 Zero)))
                        TNat)),
                 (Name "+",
                    (Ann (Lambda (Name "n")
                            (Lambda (Name "k")
                                (Rec TNat (Var (Name "n"))
                                    (Var (Name "k"))
                                    (Lambda (Name "pred")
                                        (Lambda (Name "almostSum")
                                            (Add1 (Var (Name "almostSum"))))))))
                        (TArr TNat (TArr TNat TNat))))]
    t1 <- synth ctx (App (Var (Name "+")) (Var (Name "three")))
    t2 <- synth ctx (App (App (Var (Name "+")) (Var (Name "three")))
                        (Var (Name "two")))
    Right (t1, t2)

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



