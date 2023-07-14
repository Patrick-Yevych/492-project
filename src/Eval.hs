module Eval where
import Lang
import qualified Data.Map (Map, lookup, insert, empty, fromList)

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

-- TODO: pass dlt, k here; then eval (extendEnv env x v) dlt e (\res-> k res)
-- this will break doCar, doApply, etc. will need to fix
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
    emptyDlt
    (Pi
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
    id

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

eval :: Env -> Dlt -> Expr -> IR -> Value
eval env dlt (Var x) k = k $ evalVar env x

eval env dlt (Pi x dom ran) k = eval env dlt dom (\dres ->
    k (VPi dres (Closure env x ran)))

-- TODO: need to add dlt to Closure as it is "part" of the env
-- see 324a3 shift
eval env dlt (Lambda x body) k = k (VLambda (Closure env x body))

eval env dlt (App rator rand) k = eval env dlt rator (\fres ->
    eval env dlt rand (\pres ->
        k $ doApply fres pres))

eval env dlt (Sigma x carType cdrType) k = eval env dlt carType (\cres->
    k (VSigma cres (Closure env x cdrType)))
eval env dlt (Cons a d) k = eval env dlt a (\ares ->
    eval env dlt d (\dres ->
        k (VPair ares dres)))
eval env dlt (Car e) k = eval env dlt e (\eres ->
    k $ doCar eres)
eval env dlt (Cdr e) k = eval env dlt e (\eres ->
    k $ doCdr eres)
eval env dlt Nat k = k VNat
eval env dlt Zero k = k VZero
eval env dlt (Add1 e) k = eval env dlt e (\eres ->
    k (VAdd1 eres))
eval env dlt (IndNat tgt mot base step) k = eval env dlt tgt (\tres ->
    eval env dlt mot (\mres ->
        eval env dlt base (\bres ->
            eval env dlt step (\sres ->
                k $ doIndNat tres mres bres sres))))
eval env dlt (Equal ty from to) k = eval env dlt ty (\tyres ->
    eval env dlt from (\fres ->
        eval env dlt to (\tores ->
            k (VEq tyres fres tores))))
eval env dlt Same k = k VSame
eval env dlt (Replace tgt mot base) k = eval env dlt tgt (\tres ->
    eval env dlt mot (\mres ->
        eval env dlt base (\bres ->
            k $ doReplace tres mres bres)))
eval env dlt Trivial k = k VTrivial
eval env dlt Sole k = k VSole
eval env dlt Absurd k = k VAbsurd
eval env dlt (IndAbsurd tgt mot) k = eval env dlt tgt (\tres ->
    eval env dlt mot (\mres ->
        k $ doIndAbsurd tres mres))
eval env dlt Atom k = k VAtom
eval env dlt (Tick x) k = k (VTick x)
eval env dlt U k = k VU
eval env dlt (The ty e) k = eval env dlt e k
-- continuation
eval env dlt (Reset body) k = eval env dlt body id
eval env dlt (Shift mu body) k = eval env (Data.Map.insert mu k dlt) body id
eval env dlt (Mu mu rand) k = case (Data.Map.lookup mu dlt) of
    Just k'  -> eval env dlt rand (k.k')
    Nothing -> error ("Missing value for " ++ show mu)