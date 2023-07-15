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
    check (extendCtx ctx x (eval (mkEnv ctx) initDlt a id)) b VU
    return VU
synth ctx (App rator rand) = do 
    funTy <- synth ctx rator
    (a, b) <- isPi ctx funTy
    check ctx rand a
    return (evalClosure b (eval (mkEnv ctx) initDlt rand id) id)
synth ctx (Sigma x a b) = do 
    check ctx a VU
    check (extendCtx ctx x (eval (mkEnv ctx) initDlt a id)) b VU
    return VU
synth ctx (Car e) = do 
    t <- synth ctx e
    (aT, dT) <- isSigma ctx t
    return aT
synth ctx (Cdr e) = do 
    t <- synth ctx e
    (aT, dT) <- isSigma ctx t
    return (evalClosure dT (doCar (eval (mkEnv ctx) initDlt e id) id) id)
synth ctx Nat = return VU
synth ctx (IndNat tgt mot base step) = do 
    t <- synth ctx tgt
    isNat ctx t
    let tgtV = eval (mkEnv ctx) initDlt tgt id
        motTy = eval (Env [ ]) initDlt (Pi (Name "x") Nat U) id
    check ctx mot motTy
    let motV = eval (mkEnv ctx) initDlt mot id
    check ctx base (doApply motV VZero id)
    check ctx step (indNatStepType motV id)
    return (doApply motV tgtV id)
synth ctx (Equal ty from to) = do 
    check ctx ty VU
    let tyV = eval (mkEnv ctx) initDlt ty id
    check ctx from tyV
    check ctx to tyV
    return VU
synth ctx (Replace tgt mot base) = do 
    t <- synth ctx tgt
    (ty, from, to) <- isEqual ctx t
    let motTy = eval (Env [(Name "ty", ty)]) initDlt (Pi (Name "x") (Var (Name "ty")) U) id
    check ctx mot motTy
    let motV = eval (mkEnv ctx) initDlt mot id
    check ctx base (doApply motV from id)
    return (doApply motV to id)
synth ctx Trivial = return VU
synth ctx Absurd = return VU
synth ctx (IndAbsurd tgt mot) = do 
    t <- synth ctx tgt
    isAbsurd ctx t
    check ctx mot VU
    return (eval (mkEnv ctx) initDlt mot id)
synth ctx Atom = return VU
synth ctx U = return VU
synth ctx (The ty expr) = do 
    check ctx ty VU
    let tyV = eval (mkEnv ctx) initDlt ty id
    check ctx expr tyV
    return tyV
synth ctx other =
    failure ("Unable to synthesize a type for " ++ show other)

----- TYPE CHECK -----

check :: Ctx -> Expr -> Ty -> Either Message ()
check ctx (Lambda x body) t = do 
    (a, b) <- isPi ctx t
    let xV = evalClosure b (VNeutral a (NVar x)) id
    check (extendCtx ctx x a) body xV
check ctx (Cons a d) t = do 
    (aT, dT) <- isSigma ctx t
    check ctx a aT
    let aV = eval (mkEnv ctx) initDlt a id
    check ctx d (evalClosure dT aV id)
check ctx Zero t = isNat ctx t
check ctx (Add1 n) t = do 
    isNat ctx t
    check ctx n VNat
check ctx Same t = do 
    (t, from, to) <- isEqual ctx t
    convert ctx t from to
check ctx Sole t = isTrivial ctx t
check ctx (Tick a) t = isAtom ctx t
check ctx (Clr body) t = do
    let v = eval (mkEnv ctx) initDlt body id
    let e = readBackTyped ctx t v
    check ctx e t
check ctx other t = do 
    t' <- synth ctx other
    convert ctx VU t' t
