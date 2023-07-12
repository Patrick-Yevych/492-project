module Test where

-- normWithTestDefs :: Expr -> Either Message Expr
-- normWithTestDefs e = do 
--     defs <- addDefs noDefs
--             [(Name "two",
--               (Ann (Add1 (Add1 Zero))
--                     TNat)),
--              (Name "three",
--               (Ann (Add1 (Add1 (Add1 Zero)))
--                     TNat)),
--              (Name "+",
--               (Ann (Lambda (Name "n")
--                         (Lambda (Name "k")
--                             (Rec TNat (Var (Name "n"))
--                                 (Var (Name "k"))
--                                 (Lambda (Name "pred")
--                                     (Lambda (Name "almostSum")
--                                         (Add1 (Var (Name "almostSum"))))))))
--                     (TArr TNat (TArr TNat TNat))))]
--     norm <- normWithDefs defs e
--     Right (readBackNormal (definedNames defs) norm)

-- test1, test2, test3 :: Either Message Expr
-- test1 = normWithTestDefs (Var (Name "+"))
-- test2 = normWithTestDefs (App (Var (Name "+"))
--                             (Var (Name "three")))
-- test3 = normWithTestDefs (App (App (Var (Name "+"))
--                             (Var (Name "three")))
--                         (Var (Name "two")))