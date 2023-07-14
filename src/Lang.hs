module Lang where
import qualified Data.Map as Map

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
    | Reset Expr
    | Shift Name Expr
    | Mu Name Expr
    deriving (Eq, Show)

type Ty = Value

data Value
    = VPi Ty Closure
    | VLambda Closure
    | VSigma Ty Closure
    | VPair Value Value
    | VNat
    | VZero
    | VAdd1 Value
    | VEq Ty Value Value
    | VSame
    | VTrivial
    | VSole
    | VAbsurd
    | VAtom
    | VTick String
    | VU
    | VNeutral Ty Neutral
    deriving (Show)

data Closure = Closure {closureEnv :: Env, closureDlt :: Dlt, closureName :: Name, closureBody :: Expr}
    deriving Show

data Neutral
    = NVar Name
    | NApp Neutral Normal
    | NCar Neutral
    | NCdr Neutral
    | NIndNat Neutral Normal Normal Normal
    | NReplace Neutral Normal Normal
    | NIndAbsurd Neutral Normal
    deriving Show

data Normal = Normal Ty Value
    deriving Show

data CtxEntry = Def Ty Value | IsA Ty

newtype Ctx = Ctx [(Name, CtxEntry)]

newtype Name = Name String
    deriving (Show, Eq, Ord)

newtype Env = Env [(Name, Value)]
    deriving Show

type IR = (Value -> Value)

type Dlt = Map.Map Name IR
emptyDlt = Map.empty

instance Show (a -> b) where
    show _ = "k"

newtype Message = Message String
    deriving Show

data Toplevel = Define Name Expr | Example Expr

data Output = ExampleOutput Expr
    deriving (Eq, Show)