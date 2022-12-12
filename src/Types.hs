module Types where

import           Latte.Abs

type Pos = BNFC'Position

data CType
  = CInt
  | CStr
  | CBool
  | CVoid
  | CFun CType [CType]
  | CClass Ident [(CType,Ident)]
  deriving (Eq)

getCType :: Type -> CType
getCType (Int  _            ) = CInt
getCType (Str  _            ) = CStr
getCType (Bool _            ) = CBool
getCType (Void _            ) = CVoid
getCType (Fun _ retType args) = CFun (getCType retType) (map getCType args)
getCType (Class _ ident     ) = CClass ident []

instance Show CType where
  show CInt                         = "i32"
  show CStr                         = "i8*"
  show CBool                        = "i1"
  show CVoid                        = "void"
  show (CFun   _            _     ) = "function"
  show (CClass (Ident name) fields) = "%" ++ name ++ "*"

printType :: CType -> String
printType (CClass (Ident name) fields) = "%" ++ name ++ "*" ++ show fields
printType ctype                        = show ctype

newtype Register
  = Reg Int
  deriving Eq

instance Show Register where
  show (Reg num) = "%r" ++ show num

nextReg :: Register -> Register
nextReg (Reg num) = Reg $ num + 1

newtype Var
  = Var Int
  deriving Eq

instance Show Var where
  show (Var num) = "%var" ++ show num

nextVar :: Var -> Var
nextVar (Var num) = Var $ num + 1

newtype Label
  = Lab Int
  deriving Eq

instance Show Label where
  show (Lab num) = "L_" ++ show num

nextLabel :: Label -> Label
nextLabel (Lab num) = Lab $ num + 1

data Val
  = IntV Integer
  | RegV Register
  | VarV Var
  | BoolV Bool
  | VoidV
  | NullV CType
  deriving (Eq)

instance Show Val where
  show (IntV  i    ) = show i
  show (RegV  reg  ) = show reg
  show (VarV  v    ) = show v
  show (BoolV False) = "0"
  show (BoolV True ) = "1"
  show VoidV         = ""
  show (NullV _) = "null"

data LogicalOperator
  = LOr
  | LAnd
  deriving (Eq)

instance Show LogicalOperator where
  show LOr  = "or"
  show LAnd = "and"
