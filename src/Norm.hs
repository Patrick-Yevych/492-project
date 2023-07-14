module Norm where
import Lang
import Eval

----- SAMENESS -----

convert :: Ctx -> Ty -> Value -> Value -> Either Message ()
convert ctx t v1 v2 =
  if aEquiv e1 e2
    then return ()
    else failure (show e1 ++ " is not the same type as " ++ show e2)
  where
    e1 = readBackTyped ctx t v1
    e2 = readBackTyped ctx t v2

----- READBACK HELPERS -----

nextName :: Name -> Name
nextName (Name x) = Name (x ++ "'")

freshen :: [Name] -> Name -> Name
freshen used x
  | elem x used = freshen used (nextName x)
  | otherwise = x

----- READBACK -----

readBackNormal :: Ctx -> Normal -> Expr
readBackNormal ctx (Normal t v) = readBackTyped ctx t v

readBackTyped :: Ctx -> Ty -> Value -> Expr
readBackTyped ctx VNat VZero = Zero
readBackTyped ctx VNat (VAdd1 v) = Add1 (readBackTyped ctx VNat v)
readBackTyped ctx (VPi dom ran) fun =
  Lambda
    x
    ( readBackTyped
        (extendCtx ctx x dom)
        (evalClosure ran xVal id)
        (doApply fun xVal id)
    )
  where
    x = freshen (ctxNames ctx) (closureName ran)
    xVal = VNeutral dom (NVar x)
readBackTyped ctx (VSigma aT dT) pair =
  Cons
    (readBackTyped ctx aT carVal)
    (readBackTyped ctx (evalClosure dT carVal id) cdrVal)
  where
    carVal = doCar pair id
    cdrVal = doCdr pair id
readBackTyped ctx VTrivial val = Sole
readBackTyped ctx VAbsurd (VNeutral VAbsurd neu) = The Absurd (readBackNeutral ctx neu)
readBackTyped ctx (VEq _ _ _) VSame = Same
readBackTyped ctx VAtom (VTick x) = Tick x
readBackTyped ctx VU VNat = Nat
readBackTyped ctx VU VAtom = Atom
readBackTyped ctx VU VTrivial = Trivial
readBackTyped ctx VU VAbsurd = Absurd
readBackTyped ctx VU (VEq t from to) =
  Equal
    (readBackTyped ctx VU t)
    (readBackTyped ctx t from)
    (readBackTyped ctx t to)
readBackTyped ctx VU (VSigma aT dT) = Sigma x a d
  where
    x = freshen (ctxNames ctx) (closureName dT)
    a = readBackTyped ctx VU aT
    d =
      readBackTyped
        (extendCtx ctx x aT)
        VU
        (evalClosure dT (VNeutral aT (NVar x)) id)
readBackTyped ctx VU (VPi aT bT) = Pi x a b
  where
    x = freshen (ctxNames ctx) (closureName bT)
    a = readBackTyped ctx VU aT
    b =
      readBackTyped
        (extendCtx ctx x aT)
        VU
        (evalClosure bT (VNeutral aT (NVar x)) id)
readBackTyped ctx VU VU = U
readBackTyped ctx t (VNeutral t' neu) = readBackNeutral ctx neu
readBackTyped _ otherT otherE = error $ (show otherT) ++ show otherE

readBackNeutral :: Ctx -> Neutral -> Expr
readBackNeutral ctx (NVar x) = Var x
readBackNeutral ctx (NApp neu arg) = App (readBackNeutral ctx neu) (readBackNormal ctx arg)
readBackNeutral ctx (NCar neu) = Car (readBackNeutral ctx neu)
readBackNeutral ctx (NCdr neu) = Cdr (readBackNeutral ctx neu)
readBackNeutral ctx (NIndNat neu mot base step) =
  IndNat
    (readBackNeutral ctx neu)
    (readBackNormal ctx mot)
    (readBackNormal ctx base)
    (readBackNormal ctx step)
readBackNeutral ctx (NReplace neu mot base) =
  Replace
    (readBackNeutral ctx neu)
    (readBackNormal ctx mot)
    (readBackNormal ctx base)
readBackNeutral ctx (NIndAbsurd neu mot) =
  IndAbsurd
    (The Absurd (readBackNeutral ctx neu))
    (readBackNormal ctx mot)

----- ALPHA EQUIVALENCE -----

aEquiv :: Expr -> Expr -> Bool
aEquiv e1 e2 = aEquivHelper 0 [] e1 [] e2

aEquivHelper :: Integer -> [(Name, Integer)] -> Expr -> [(Name, Integer)] -> Expr -> Bool
aEquivHelper i ns1 (Var x) ns2 (Var y) =
  case (lookup x ns1, lookup y ns2) of
    (Nothing, Nothing) -> x == y
    (Just i, Just j) -> i == j
    _ -> False
aEquivHelper i ns1 (Pi x a1 r1) ns2 (Pi y a2 r2) =
  aEquivHelper i ns1 a1 ns2 a2
    && aEquivHelper (i + 1) ((x, i) : ns1) r1 ((y, i) : ns2) r2
aEquivHelper i ns1 (Lambda x body1) ns2 (Lambda y body2) =
  aEquivHelper (i + 1) ((x, i) : ns1) body1 ((y, i) : ns2) body2
aEquivHelper i ns1 (App rator1 rand1) ns2 (App rator2 rand2) =
  aEquivHelper i ns1 rator1 ns2 rator2
    && aEquivHelper i ns1 rand1 ns2 rand2
aEquivHelper i ns1 (Sigma x a1 d1) ns2 (Sigma y a2 d2) =
  aEquivHelper i ns1 a1 ns2 a2
    && aEquivHelper (i + 1) ((x, i) : ns1) d1 ((y, i) : ns2) d2
aEquivHelper i ns1 (Cons car1 cdr1) ns2 (Cons car2 cdr2) =
  aEquivHelper i ns1 car1 ns2 car2
    && aEquivHelper i ns1 cdr1 ns2 cdr2
aEquivHelper i ns1 (Car pair1) ns2 (Car pair2) =
  aEquivHelper i ns1 pair1 ns2 pair2
aEquivHelper i ns1 (Cdr pair1) ns2 (Cdr pair2) =
  aEquivHelper i ns1 pair1 ns2 pair2
aEquivHelper _ _ Nat _ Nat = True
aEquivHelper _ _ Zero _ Zero = True
aEquivHelper i ns1 (Add1 e1) ns2 (Add1 e2) = aEquivHelper i ns1 e1 ns2 e2
aEquivHelper i ns1 (IndNat tgt1 mot1 base1 step1) ns2 (IndNat tgt2 mot2 base2 step2) =
  aEquivHelper i ns1 tgt1 ns2 tgt2
    && aEquivHelper i ns1 mot1 ns2 mot2
    && aEquivHelper i ns1 base1 ns2 base2
    && aEquivHelper i ns1 step1 ns2 step2
aEquivHelper i ns1 (Equal ty1 from1 to1) ns2 (Equal ty2 from2 to2) =
  aEquivHelper i ns1 ty1 ns2 ty2
    && aEquivHelper i ns1 from1 ns2 from2
    && aEquivHelper i ns1 to1 ns2 to2
aEquivHelper _ _ Same _ Same = True
aEquivHelper i ns1 (Replace tgt1 mot1 base1) ns2 (Replace tgt2 mot2 base2) =
  aEquivHelper i ns1 tgt1 ns2 tgt2
    && aEquivHelper i ns1 mot1 ns2 mot2
    && aEquivHelper i ns1 base1 ns2 base2
aEquivHelper _ _ Trivial _ Trivial = True
aEquivHelper _ _ Sole _ Sole = True
aEquivHelper _ _ Absurd _ Absurd = True
aEquivHelper i ns1 (IndAbsurd tgt1 mot1) ns2 (IndAbsurd tgt2 mot2) =
  aEquivHelper i ns1 tgt1 ns2 tgt2
    && aEquivHelper i ns1 mot1 ns2 mot2
aEquivHelper _ _ Atom _ Atom = True
aEquivHelper _ _ U _ U = True
aEquivHelper _ _ (Tick a1) _ (Tick a2) = a1 == a2
aEquivHelper _ _ (The Absurd _) _ (The Absurd _) = True
aEquivHelper i ns1 (The t1 e1) ns2 (The t2 e2) =
  aEquivHelper i ns1 t1 ns2 t2
    && aEquivHelper i ns1 e1 ns2 e2
aEquivHelper _ _ _ _ _ = False