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
    = VZero
    | VAdd1 Value
    | VClosure (Env Value) Name Expr
    | VNeutral Ty Neutral
    deriving (Show)

data Neutral
    = NVar Name
    | NApp Neutral Normal
    | NRec Ty Neutral Normal Normal
    deriving (Show)

data Normal
    = Normal {normalType :: Ty, normalValue :: Value}
    deriving (Show)

type Defs = Env Normal

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

eval :: Env Value -> Expr -> Value
eval env (Var x) =
    case lookupVar env x of
        Left msg -> error ("Internal error: " ++ show msg)
        Right v -> v
eval env (Lambda x body) = VClosure env x body
eval env (App rator rand) = doApply (eval env rator) (eval env rand)
eval env Zero = VZero
eval env (Add1 n) = VAdd1 (eval env n)
eval env (Rec t tgt base step) = doRec t (eval env tgt) (eval env base) (eval env step)
eval env (Ann e t) = eval env e


-- doApply :: Value -> Value -> Either Message Value
-- doApply (VClosure env x body) arg = eval (extend env x arg) body
-- doApply (VNeutral neu) arg = Right (VNeutral (NApp neu arg))

doApply :: Value -> Value -> Value
doApply (VClosure env x body) arg =
    eval (extend env x arg) body
doApply (VNeutral (TArr t1 t2) neu) arg =
    VNeutral t2 (NApp neu (Normal t1 arg))

doRec :: Ty -> Value -> Value -> Value -> Value
doRec t VZero base step = base
doRec t (VAdd1 n) base step =
    doApply (doApply step n)
        (doRec t n base step)
doRec t (VNeutral TNat neu) base step =
    VNeutral t
        (NRec t neu
            (Normal t base)
            (Normal (TArr TNat (TArr t t)) step))

readBackNormal :: [Name] -> Normal -> Expr
readBackNormal used (Normal t v) = readBack used t v

readBack :: [Name] -> Ty -> Value -> Expr
readBack used TNat VZero = Zero
readBack used TNat (VAdd1 pred) = Add1 (readBack used TNat pred)
readBack used (TArr t1 t2) fun =
    let x = freshen used (argName fun)
        xVal = VNeutral t1 (NVar x)
    in Lambda x
        (readBack used t2
         (doApply fun xVal))
    where
        argName (VClosure _ x _) = x
        argName _ = Name "x"
readBack used t1 (VNeutral t2 neu) =
-- Note: checking t1 and t2 for equality here is a good way to find bugs,
-- but is not strictly necessary.
    if t1 == t2
        then readBackNeutral used neu
        else error "Internal error: mismatched types at readBackNeutral"

readBackNeutral :: [Name] -> Neutral -> Expr
readBackNeutral used (NVar x) = Var x
readBackNeutral used (NApp rator arg) =
    App (readBackNeutral used rator) (readBackNormal used arg)
readBackNeutral used (NRec t neu base step) =
    Rec t (readBackNeutral used neu)
        (readBackNormal used base)
        (readBackNormal used step)

noDefs :: Defs
noDefs = initEnv

defsToContext :: Defs -> Context
defsToContext defs = fmap normalType defs

defsToEnv :: Defs -> Env Value
defsToEnv defs = fmap normalValue defs

normWithDefs :: Defs -> Expr -> Either Message Normal
normWithDefs defs e = do 
    t <- synth (defsToContext defs) e
    let v = eval (defsToEnv defs) e
    Right (Normal t v)

addDefs :: Defs -> [(Name, Expr)] -> Either Message Defs
addDefs defs [ ] = Right defs
addDefs defs ((x, e) : more) = do 
    norm <- normWithDefs defs e
    addDefs (extend defs x norm) more

definedNames :: Defs -> [Name]
definedNames (Env defs) = map fst defs


-- Church Numerals testing begin

normWithTestDefs :: Expr -> Either Message Expr
normWithTestDefs e = do 
    defs <- addDefs noDefs
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
    norm <- normWithDefs defs e
    Right (readBackNormal (definedNames defs) norm)

test1, test2, test3 :: Either Message Expr
test1 = normWithTestDefs (Var (Name "+"))
test2 = normWithTestDefs (App (Var (Name "+"))
                            (Var (Name "three")))
test3 = normWithTestDefs (App (App (Var (Name "+"))
                            (Var (Name "three")))
                        (Var (Name "two")))

-- Church Numerals testing end

freshen :: [Name] -> Name -> Name
freshen used x
    | elem x used = freshen used (nextName x)
    | otherwise = x
    
nextName :: Name -> Name
nextName (Name x) = Name (x ++ "'")



