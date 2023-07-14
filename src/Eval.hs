{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
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

-- TODO: redefine env to be a map. This will make evalVar order O(1).
evalVar :: Env -> Name -> Value
evalVar (Env []) x = error ("Missing value for " ++ show x)
evalVar (Env ((y, v) : env)) x
  | x == y = v
  | otherwise = evalVar (Env env) x

-- TODO: pass dlt, k here; then eval (extendEnv env x v) dlt e (\res-> k res)
-- this will break doCar, doApply, etc. will need to fix
evalClosure :: Closure -> Value -> IR -> Value
evalClosure (Closure env dlt x e) v k = eval (extendEnv env x v) dlt e k

doCar :: Value -> IR -> Value
doCar (VPair v1 v2) k = k v1
doCar (VNeutral (VSigma aT dT) neu) k = k (VNeutral aT (NCar neu))

doCdr :: Value -> IR -> Value
doCdr (VPair v1 v2) k = k v2
doCdr v@(VNeutral (VSigma aT dT) neu) k = doCar v (\r1 ->
    evalClosure dT r1 (\r2 ->
        k (VNeutral r2 (NCdr neu))))

doApply :: Value -> Value -> IR -> Value
doApply (VLambda closure) arg k = evalClosure closure arg k
doApply (VNeutral (VPi dom ran) neu) arg k = evalClosure ran arg (\r1 ->
    k (VNeutral r1 (NApp neu (Normal dom arg))))

doIndAbsurd :: Value -> Value -> IR -> Value
doIndAbsurd (VNeutral VAbsurd neu) mot k = k (VNeutral mot (NIndAbsurd neu (Normal VU mot)))

doReplace :: Value -> Value -> Value -> IR -> Value
doReplace VSame mot base k = k base
doReplace (VNeutral (VEq ty from to) neu) mot base k = doApply mot to (\r1 ->
    doApply mot from (\r2 ->
        k (VNeutral r1 
            (NReplace neu 
                (Normal 
                    (VPi ty (Closure (Env []) emptyDlt (Name "x") U)) 
                    mot) 
                (Normal r2 base)))))

-- TODO: may need to fix
indNatStepType :: Value -> IR -> Value
indNatStepType mot k =
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
    k

doIndNat :: Value -> Value -> Value -> Value -> IR -> Value
doIndNat VZero mot base step k = k base
doIndNat (VAdd1 v) mot base step k = doApply step v (\r1 ->
    doIndNat v mot base step (\r2 ->
        doApply r1 r2 k))
doIndNat tgt@(VNeutral VNat neu) mot base step k = doApply mot tgt (\r1 ->
    doApply mot VZero (\r2 ->
        indNatStepType mot (\r3 ->
            k (VNeutral r1
                    (NIndNat neu
                        (Normal (VPi VNat (Closure (Env []) emptyDlt (Name "k") U)) mot)
                        (Normal r2 base)
                        (Normal r3 step))))))

eval :: Env -> Dlt -> Expr -> IR -> Value
eval env dlt (Var x) k = k $ evalVar env x

eval env dlt (Pi x dom ran) k = eval env dlt dom (\r1 ->
    k (VPi r1 (Closure env dlt x ran)))

-- TODO: need to add dlt to Closure as it is "part" of the env
-- see 324a3 shift
eval env dlt (Lambda x body) k = k (VLambda (Closure env dlt x body))

eval env dlt (App rator rand) k = eval env dlt rator (\r1 ->
    eval env dlt rand (\r2 ->
        doApply r1 r2 k))

eval env dlt (Sigma x carType cdrType) k = eval env dlt carType (\r1->
    k (VSigma r1 (Closure env dlt x cdrType)))
eval env dlt (Cons a d) k = eval env dlt a (\r1 ->
    eval env dlt d (\r2 ->
        k (VPair r1 r2)))
eval env dlt (Car e) k = eval env dlt e (\r1 ->
    doCar r1 k)
eval env dlt (Cdr e) k = eval env dlt e (\r1 ->
    doCdr r1 k)
eval env dlt Nat k = k VNat
eval env dlt Zero k = k VZero
eval env dlt (Add1 e) k = eval env dlt e (\r1 ->
    k (VAdd1 r1))
eval env dlt (IndNat tgt mot base step) k = eval env dlt tgt (\r1 ->
    eval env dlt mot (\r2 ->
        eval env dlt base (\r3 ->
            eval env dlt step (\r4 ->
                doIndNat r1 r2 r3 r4 k))))
eval env dlt (Equal ty from to) k = eval env dlt ty (\r1 ->
    eval env dlt from (\r2 ->
        eval env dlt to (\r3 ->
            k (VEq r1 r2 r3))))
eval env dlt Same k = k VSame
eval env dlt (Replace tgt mot base) k = eval env dlt tgt (\r1 ->
    eval env dlt mot (\r2 ->
        eval env dlt base (\r3 ->
            doReplace r1 r2 r3 k)))
eval env dlt Trivial k = k VTrivial
eval env dlt Sole k = k VSole
eval env dlt Absurd k = k VAbsurd
eval env dlt (IndAbsurd tgt mot) k = eval env dlt tgt (\r1 ->
    eval env dlt mot (\r2 ->
        doIndAbsurd r1 r2 k))
eval env dlt Atom k = k VAtom
eval env dlt (Tick x) k = k (VTick x)
eval env dlt U k = k VU
eval env dlt (The ty e) k = eval env dlt e k
-- continuation
eval env dlt (Reset body) k = eval env dlt body id
eval env dlt (Shift mu body) k = eval env (Data.Map.insert mu k dlt) body id
eval env dlt (Mu mu rand) k = case Data.Map.lookup mu dlt of
    Just k'  -> eval env dlt rand (k.k')
    Nothing -> error ("Missing value for " ++ show mu)