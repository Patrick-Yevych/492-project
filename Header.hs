module Header where

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

data Ty
    = TNat
    | TArr Ty Ty
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

type Context = Env Ty
initCtx :: Context
initCtx = initEnv

initEnv :: Env val
initEnv = Env [ ]

newtype Name = Name String
    deriving (Show, Eq)

newtype Env val = Env [(Name, val)]
    deriving Show

instance Functor Env where
    fmap f (Env xs) = Env (map (\x -> ((fst x), f (snd x))) xs)  -- Note: check this out later 

newtype Message = Message String
    deriving Show