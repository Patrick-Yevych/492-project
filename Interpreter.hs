module Interpreter where
import Header

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

freshen :: [Name] -> Name -> Name
freshen used x
    | elem x used = freshen used (nextName x)
    | otherwise = x
    
nextName :: Name -> Name
nextName (Name x) = Name (x ++ "'")