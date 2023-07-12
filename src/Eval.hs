module Eval where
import Lang

----- ERROR MESSAGES -----

failure :: String -> Either Message a
failure msg = Left (Message msg)

----- ENV -----

extendEnv :: Env -> Name -> Value -> Env
extendEnv (Env env) x v = Env ((x, v) : env)

mkEnv :: Ctx -> Env
mkEnv (Ctx []) = Env []
mkEnv (Ctx ((x, e) : ctx)) = Env ((x, v) : env)
  where
    Env env = mkEnv (Ctx ctx)
    v = case e of
      Def _ v -> v
      IsA t -> VNeutral t (NVar x)

----- CTX -----

initCtx :: Ctx
initCtx = Ctx []

ctxNames :: Ctx -> [Name]
ctxNames (Ctx ctx) = map fst ctx

extendCtx :: Ctx -> Name -> Ty -> Ctx
extendCtx (Ctx ctx) x t = Ctx ((x, IsA t) : ctx)

define :: Ctx -> Name -> Ty -> Value -> Ctx
define (Ctx ctx) x t v = Ctx ((x, Def t v) : ctx)

lookupType :: Ctx -> Name -> Either Message Ty
lookupType (Ctx []) x = failure ("Unbound variable: " ++ show x)
lookupType (Ctx ((y, e) : ctx)) x
  | x == y =
    case e of
      Def t _ -> return t
      IsA t -> return t
  | otherwise =
    lookupType (Ctx ctx) x

----- EVAL -----

evalVar :: Env -> Name -> Value
evalVar (Env []) x = error ("Missing value for " ++ show x)
evalVar (Env ((y, v) : env)) x
  | x == y = v
  | otherwise = evalVar (Env env) x

evalClosure :: Closure -> Value -> Value
evalClosure (Closure env x e) v = eval (extendEnv env x v) e

doCar :: Value -> Value
doCar (VPair v1 v2) = v1
doCar (VNeutral (VSigma aT dT) neu) = VNeutral aT (NCar neu)

doCdr :: Value -> Value
doCdr (VPair v1 v2) = v2
doCdr v@(VNeutral (VSigma aT dT) neu) = VNeutral (evalClosure dT (doCar v)) (NCdr neu)

doApply :: Value -> Value -> Value
doApply (VLambda closure) arg = evalClosure closure arg
doApply (VNeutral (VPi dom ran) neu) arg = VNeutral (evalClosure ran arg) (NApp neu (Normal dom arg))

doIndAbsurd :: Value -> Value -> Value
doIndAbsurd (VNeutral VAbsurd neu) mot = VNeutral mot (NIndAbsurd neu (Normal VU mot))

doReplace :: Value -> Value -> Value -> Value
doReplace VSame mot base = base
doReplace (VNeutral (VEq ty from to) neu) mot base =
  VNeutral
    (doApply mot to)
    (NReplace neu (Normal motT mot) (Normal baseT base))
  where
    motT = VPi ty (Closure (Env []) (Name "x") U)
    baseT = doApply mot from

indNatStepType :: Value -> Value
indNatStepType mot =
  eval
    (Env [(Name "mot", mot)])
    ( Pi
        (Name "n-1")
        Nat
        ( Pi
            (Name "almost")
            ( App
                (Var (Name "mot"))
                (Var (Name "n-1"))
            )
            ( App
                (Var (Name "mot"))
                (Add1 (Var (Name "n-1")))
            )
        )
    )

doIndNat :: Value -> Value -> Value -> Value -> Value
doIndNat VZero mot base step = base
doIndNat (VAdd1 v) mot base step =
  doApply (doApply step v) (doIndNat v mot base step)
doIndNat tgt@(VNeutral VNat neu) mot base step =
  VNeutral
    (doApply mot tgt)
    ( NIndNat
        neu
        (Normal (VPi VNat (Closure (Env []) (Name "k") U)) mot)
        (Normal (doApply mot VZero) base)
        (Normal (indNatStepType mot) step)
    )

eval :: Env -> Expr -> Value
eval env (Var x) = evalVar env x
eval env (Pi x dom ran) = VPi (eval env dom) (Closure env x ran)
eval env (Lambda x body) = VLambda (Closure env x body)
eval env (App rator rand) = doApply (eval env rator) (eval env rand)
eval env (Sigma x carType cdrType) = VSigma (eval env carType) (Closure env x cdrType)
eval env (Cons a d) = VPair (eval env a) (eval env d)
eval env (Car e) = doCar (eval env e)
eval env (Cdr e) = doCdr (eval env e)
eval env Nat = VNat
eval env Zero = VZero
eval env (Add1 e) = VAdd1 (eval env e)
eval env (IndNat tgt mot base step) = doIndNat (eval env tgt) (eval env mot) (eval env base) (eval env step)
eval env (Equal ty from to) = VEq (eval env ty) (eval env from) (eval env to)
eval env Same = VSame
eval env (Replace tgt mot base) = doReplace (eval env tgt) (eval env mot) (eval env base)
eval env Trivial = VTrivial
eval env Sole = VSole
eval env Absurd = VAbsurd
eval env (IndAbsurd tgt mot) = doIndAbsurd (eval env tgt) (eval env mot)
eval env Atom = VAtom
eval env (Tick x) = VTick x
eval env U = VU
eval env (The ty e) = eval env e