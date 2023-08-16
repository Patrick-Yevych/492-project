module Type where
import Lang
import Eval
import Norm

----- TYPE CHECK HELPERS -----

unexpected :: Ctx -> String -> Value -> Either Message a
unexpected ctx msg t = failure (msg ++ ": " ++ show e)
    where
        e = readBackTyped ctx VU t

-- (X -> Y) where input x has type a and b is a closure whose body never uses x
-- (Pi (x X) Y)
isPi :: Ctx -> Value -> Either Message (Ty, Closure)
isPi _ (VPi a b) = return (a, b)
isPi ctx other = unexpected ctx "Not a Pi type" other

-- ((X3 -> Y1) -> X2) -> X1  where X3=X2=X1
isClr :: Ctx -> Value -> Either Message (Ty, Closure)
isClr ctx (VPi (VPi (VPi x3 y1) x2) x1) = do
    let x1Ty = evalClosureBody x1 id -- closure x1 must not reference Ty arg. if it does, then construction of clr type fails by missing key error.
    let x2Ty = evalClosureBody x2 id

    let t1 = readBackTyped ctx VU x1Ty
    let t2 = readBackTyped ctx VU x2Ty
    let t3 = readBackTyped ctx VU x3
    
    if aEquiv t1 t2 && aEquiv t2 t3
        then return (x3, y1)
--        else return (Message "Improper Clr type construction")
        else unexpected ctx "Mismatching types: Error" VU
         

isClr ctx other = unexpected ctx "Not a Clr type" other

-- gc takes an expression (expr) its type (texpr) and a name (tname).
-- gc then gets the continuation of the expression and binds it to 
-- the name. gc utilizes its helper function _gc.


gc :: Name -> Expr -> Expr -> Expr
gc tname texpr expr = Lambda tname (_gc tname texpr expr)

-- _gc is a helper for gc.

_gc :: Name -> Expr -> Expr -> Expr
_gc tname texpr (Var name) = Var name
_gc tname texpr (Pi name a b) = Pi name (_gc tname texpr a) (_gc tname texpr b)
_gc tname texpr (Lambda name expr) = Lambda name (_gc tname texpr expr)
_gc tname texpr (App rator rand) = App (_gc tname texpr rator) (_gc tname texpr rand)
_gc tname texpr (Sigma name a b) = Sigma name (_gc tname texpr a) (_gc tname texpr b)
_gc tname texpr (Cons a d) = Cons (_gc tname texpr a) (_gc tname texpr d)
_gc tname texpr (Car a) = Car (_gc tname texpr a)
_gc tname texpr (Cdr d) = Cdr (_gc tname texpr d)
_gc tname texpr Nat = Nat
_gc tname texpr Zero = Zero
_gc tname texpr (Add1 expr) = Add1 (_gc tname texpr expr)
_gc tname texpr (IndNat a b c d) = IndNat (_gc tname texpr a) (_gc tname texpr b) (_gc tname texpr c) (_gc tname texpr d)
_gc tname texpr (Equal a b c) = Equal (_gc tname texpr a) (_gc tname texpr b) (_gc tname texpr c)
_gc tname texpr Same = Same
_gc tname texpr (Replace a b c) = Replace (_gc tname texpr a) (_gc tname texpr b) (_gc tname texpr c)
_gc tname texpr Trivial = Trivial
_gc tname texpr Sole = Sole
_gc tname texpr Absurd = Absurd
_gc tname texpr (IndAbsurd a b) = IndAbsurd (_gc tname texpr a) (_gc tname texpr b)
_gc tname texpr Atom = Atom
_gc tname texpr (Tick s) = Tick s
_gc tname texpr U = U
_gc tname texpr (The a b) = The (_gc tname texpr a) (_gc tname texpr b)
_gc tname texpr (Clr expr) = Clr (_gc tname texpr expr)
_gc tname texpr (Shf name expr) =
    if tname == name && texpr == expr
        then Var tname
        else Shf name expr
_gc tname texpr (Jmp name expr) = Jmp name (_gc tname texpr expr)
-- _gc tname texpr (Cnt name expr) = Cnt name (_gc tname texpr expr)

-- gs takes an expression (expr) as input and finds the the first shift sub-expression
-- within expr with respect to the order of evaluation of eval. If there is no shift 
-- subsexpression, an appropriate message is displayed. gs utilizes _gs as a helper.

gs :: Expr -> Either Message (Name, Expr)
gs expr = case _gs expr of
    (Shf tname texpr) -> Right (tname, texpr)
    _ -> failure "Shf not found"

-- _gs is a helper function for gs.

_gs :: Expr -> Expr
_gs (Pi name a b) = case _gs a of
    (Shf mu expr) -> (Shf mu expr)
    _ -> _gs b
_gs (Lambda name body) = _gs body 
_gs (App rator rand) = case _gs rator of
    (Shf mu expr) -> (Shf mu expr)
    _ -> _gs rand
_gs (Sigma name a b) = case _gs a of
    (Shf mu expr) -> (Shf mu expr)
    _ -> _gs b
_gs (Cons a d) = case _gs a of
    (Shf mu expr) -> (Shf mu expr)
    _ -> _gs d
_gs (Car a) = _gs a
_gs (Cdr d) = _gs d
_gs (Add1 expr) = _gs expr
_gs (IndNat a b c d) = case _gs a of
    (Shf mu expr) -> (Shf mu expr)
    _ -> case _gs b of
        (Shf mu expr) -> (Shf mu expr)
        _ -> case _gs c of
            (Shf mu expr) -> (Shf mu expr)
            _ -> _gs d
_gs (Equal a b c) = case _gs a of
    (Shf mu expr) -> (Shf mu expr)
    _ -> case _gs b of
        (Shf mu expr) -> (Shf mu expr)
        _ -> _gs c
_gs (Replace a b c) = case _gs a of
    (Shf mu expr) -> (Shf mu expr)
    _ -> case _gs b of
        (Shf mu expr) -> (Shf mu expr)
        _ -> _gs c
_gs (IndAbsurd a b) = case _gs a of
    (Shf mu expr) -> (Shf mu expr)
    _ -> _gs b
_gs (The a b) = case _gs a of
    (Shf mu expr) -> (Shf mu expr)
    _ -> _gs b
_gs (Clr expr) = _gs expr
_gs (Shf mu expr) = (Shf mu expr)

-- _gs (Jmp name expr) = _gs expr
-- _gs (Cnt name expr) = _gs expr
    
_gs _ = Absurd


-- gj takes an expression (expr) as input and finds the the first jump sub-expression
-- within expr with respect to the order of evaluation of eval. If there is no jump 
-- subsexpression, an appropriate message is displayed. gj utilizes _gj as a helper.

gj :: Expr -> Either Expr (Name, Expr)
gj expr = case _gj expr of
    (Jmp name expr) -> Right (name, expr)
    _ -> Left Absurd

-- _gj is a helper function for gj.

_gj :: Expr -> Expr
_gj (Pi name a b) = case _gs a of
    (Jmp name expr)-> (Jmp name expr)
    _ -> _gs b
_gj (Lambda name body) = _gs body 
_gj (App rator rand) = case _gs rator of
    (Jmp name expr) -> (Jmp name expr)
    _ -> _gs rand
_gj (Sigma name a b) = case _gs a of
    (Jmp name expr) -> (Jmp name expr)
    _ -> _gs b
_gj (Cons a d) = case _gs a of
    (Jmp name expr) -> (Jmp name expr)
    _ -> _gs d
_gj (Car a) = _gs a
_gj (Cdr d) = _gs d
_gj (Add1 expr) = _gs expr
_gj (IndNat a b c d) = case _gs a of
    (Jmp name expr) -> (Jmp name expr)
    _ -> case _gs b of
        (Jmp name expr) -> (Jmp name expr)
        _ -> case _gs c of
            (Jmp name expr) -> (Jmp name expr)
            _ -> _gs d
_gj (Equal a b c) = case _gs a of
    (Jmp name expr) -> (Jmp name expr)
    _ -> case _gs b of
        (Jmp name expr) -> (Jmp name expr)
        _ -> _gs c
_gj (Replace a b c) = case _gs a of
    (Jmp name expr) -> (Jmp name expr)
    _ -> case _gs b of
        (Jmp name expr) -> (Jmp name expr)
        _ -> _gs c
_gj (IndAbsurd a b) = case _gs a of
    (Jmp name expr) -> (Jmp name expr)
    _ -> _gs b
_gj (The a b) = case _gs a of
    (Jmp name expr) -> (Jmp name expr)
    _ -> _gs b
_gj (Clr expr) = _gs expr

_gj (Shf mu expr) = _gs expr
_gj (Jmp name expr) = (Jmp name expr)
_gj _ = Absurd





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
-- we need to understand this
-- the closure b is not the closure of the lambda function,
-- but rather the closure for B in the type of (Pi ((a A) B)
-- this is important because the type B may reference a as at is a dependent type
check ctx (Lambda x body) t = do 
    (a, b) <- isPi ctx t
    let xV = evalClosure b (VNeutral a (NVar x)) id
    check (extendCtx ctx x a) body xV -- x is of type a, and body **should** be of type xV
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

-- (Clr (+ 2 (Shf k (* 3 (Jmp k 3)))))
-- \x -> x + 2
-- (lambda (Name "x") (+ (Var (Name "x")) 2))
-- (The Nat (Jmp k Body))
-- (+ 2 (call/cc (lambda (k) (* 3 (k 3)))))
-- the type of Clr and call/cc is ((X -> Y) -> X) -> X  OR (-> (-> (-> X Y) X) X) OR
-- (Pi (c (Pi (b (Pi (a X) Y)) X)) X)
-- the exact type of B is irrelevant and may be considered as ⊥ for the purposed of type checking.
check ctx (Clr body) t = do
    (x, y) <- isClr ctx t
    let contTy = VPi x y
    (tname, texpr) <- gs body
    let cont = gc tname texpr body
    check ctx cont contTy
    check ctx (Shf tname texpr) x

    -- we need to use evaluator to extract the continuation, then check that it is type (xTy -> yTy)
    -- The top most constructor gives us the type yTy. e.g. if the first thing we see in body is Add1,
    -- we know that yTy is of type Nat.
    -- the type the continuation is expecting will most likely need to be found by the type of expression rand
    -- passed into (Jmp mu rand)
    -- for (Jmp mu rand), rand must be type xTy

-- the type of the continuation bound to mu is (X -> Y).
-- this continuation is the expression between Clr and Shf.
-- in call/cc, the lambda function passed in is of type (X -> Y) -> X
-- because body is simply any expr rather than the lambda function, its type is
-- A, with the continuation (X -> Y) bound to mu in Dlt.
check ctx (Shf mu body) t = case gj body of
    Right (mu, rand) -> check ctx (Jmp mu rand) t
    _ -> check ctx body t

-- the type of mu is (X -> Y), and we are applying rand to mu.
-- therefore, rand must be of type X.
check ctx (Jmp mu rand) t = check ctx rand t

check ctx other t = do 
    t' <- synth ctx other
    convert ctx VU t' t
