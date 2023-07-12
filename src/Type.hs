module Type where
import Lang
import Eval
import Norm

----- TYPE CHECK HELPERS -----

unexpected :: Ctx -> String -> Value -> Either Message a
unexpected ctx msg t = failure (msg ++ ": " ++ show e)
    where
        e = readBackTyped ctx VU t

isPi :: Ctx -> Value -> Either Message (Ty, Closure)
isPi _ (VPi a b) = return (a, b)
isPi ctx other = unexpected ctx "Not a Pi type" other

isSigma :: Ctx -> Value -> Either Message (Ty, Closure)
isSigma _ (VSigma a b) = return (a, b)
isSigma ctx other = unexpected ctx "Not a Sigma type" other

isNat :: Ctx -> Value -> Either Message ()
isNat _ VNat = return ()
isNat ctx other = unexpected ctx "Not Nat" other

isEqual :: Ctx -> Value -> Either Message (Ty, Value, Value)
isEqual _ (VEq ty from to) = return (ty, from, to)
isEqual ctx other = unexpected ctx "Not an equality type" other

isAbsurd :: Ctx -> Value -> Either Message ()
isAbsurd _ VAbsurd = return ()
isAbsurd ctx other = unexpected ctx "Not Absurd: " other

isTrivial :: Ctx -> Value -> Either Message ()
isTrivial _ VTrivial = return ()
isTrivial ctx other = unexpected ctx "Not Trivial" other

isAtom :: Ctx -> Value -> Either Message ()
isAtom _ VAtom = return ()
isAtom ctx other = unexpected ctx "Not Atom" other

----- TYPE SYNTHESIS -----

synth :: Ctx -> Expr -> Either Message Ty
synth ctx (Var x) = do 
    t <- lookupType ctx x
    return t
synth ctx (Pi x a b) = do 
    check ctx a VU
    check (extendCtx ctx x (eval (mkEnv ctx) a)) b VU
    return VU
synth ctx (App rator rand) = do 
    funTy <- synth ctx rator
    (a, b) <- isPi ctx funTy
    check ctx rand a
    return (evalClosure b (eval (mkEnv ctx) rand))
synth ctx (Sigma x a b) = do 
    check ctx a VU
    check (extendCtx ctx x (eval (mkEnv ctx) a)) b VU
    return VU
synth ctx (Car e) = do 
    t <- synth ctx e
    (aT, dT) <- isSigma ctx t
    return aT
synth ctx (Cdr e) = do 
    t <- synth ctx e
    (aT, dT) <- isSigma ctx t
    return (evalClosure dT (doCar (eval (mkEnv ctx) e)))
synth ctx Nat = return VU
synth ctx (IndNat tgt mot base step) = do 
    t <- synth ctx tgt
    isNat ctx t
    let tgtV = eval (mkEnv ctx) tgt
        motTy = eval (Env [ ]) (Pi (Name "x") Nat U)
    check ctx mot motTy
    let motV = eval (mkEnv ctx) mot
    check ctx base (doApply motV VZero)
    check ctx step (indNatStepType motV)
    return (doApply motV tgtV)
synth ctx (Equal ty from to) = do 
    check ctx ty VU
    let tyV = eval (mkEnv ctx) ty
    check ctx from tyV
    check ctx to tyV
    return VU
synth ctx (Replace tgt mot base) = do 
    t <- synth ctx tgt
    (ty, from, to) <- isEqual ctx t
    let motTy = eval (Env [(Name "ty", ty)]) (Pi (Name "x") (Var (Name "ty")) U)
    check ctx mot motTy
    let motV = eval (mkEnv ctx) mot
    check ctx base (doApply motV from)
    return (doApply motV to)
synth ctx Trivial = return VU
synth ctx Absurd = return VU
synth ctx (IndAbsurd tgt mot) = do 
    t <- synth ctx tgt
    isAbsurd ctx t
    check ctx mot VU
    return (eval (mkEnv ctx) mot)
synth ctx Atom = return VU
synth ctx U = return VU
synth ctx (The ty expr) = do 
    check ctx ty VU
    let tyV = eval (mkEnv ctx) ty
    check ctx expr tyV
    return tyV
synth ctx other =
    failure ("Unable to synthesize a type for " ++ show other)

----- TYPE CHECK -----

check :: Ctx -> Expr -> Ty -> Either Message ()
check ctx (Lambda x body) t = do 
    (a, b) <- isPi ctx t
    let xV = evalClosure b (VNeutral a (NVar x))
    check (extendCtx ctx x a) body xV
check ctx (Cons a d) t = do 
    (aT, dT) <- isSigma ctx t
    check ctx a aT
    let aV = eval (mkEnv ctx) a
    check ctx d (evalClosure dT aV)
check ctx Zero t = isNat ctx t
check ctx (Add1 n) t = do 
    isNat ctx t
    check ctx n VNat
check ctx Same t = do 
    (t, from, to) <- isEqual ctx t
    convert ctx t from to
check ctx Sole t = isTrivial ctx t
check ctx (Tick a) t = isAtom ctx t
check ctx other t = do 
    t' <- synth ctx other
    convert ctx VU t' t
