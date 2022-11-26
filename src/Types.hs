module Types where

import           Latte.Abs

type Pos = BNFC'Position

data CType
  = CInt
  | CStr
  | CBool
  | CVoid
  | CFun CType [CType]
  | CArray CType
  deriving (Eq)

getCType :: Type -> CType
getCType (Int _)              = CInt
getCType (Str _)              = CStr
getCType (Bool _)             = CBool
getCType (Void _)             = CVoid
getCType (Fun _ retType args) = CFun (getCType retType) (map getCType args)
getCType (Array _ vtype)      = CArray (getCType vtype)

instance Show CType where
  show CInt       = "i32"
  show CStr       = "i8*"
  show CBool      = "i1"
  show CVoid      = "void"
  show (CFun _ _) = "function"
  show (CArray vtype) = show vtype ++ "[]"

typeToLLVM :: Type -> String
typeToLLVM (Int _)              = "i32"
typeToLLVM (Str _)              = "i8*"
typeToLLVM (Bool _)             = "i1"
typeToLLVM (Void _)             = "void"
typeToLLVM (Fun _ retType args) = "todo"

data Register =
  Reg Int
  deriving (Eq)

instance Show Register where
  show (Reg num) = "%r" ++ show num

nextReg :: Register -> Register
nextReg (Reg num) = Reg $ num + 1

data Var =
  Var Int
  deriving (Eq)

instance Show Var where
  show (Var num) = "%var" ++ show num

nextVar :: Var -> Var
nextVar (Var num) = Var $ num + 1

data Label =
  Lab Int
  deriving (Eq)

instance Show Label where
  show (Lab num) = "L_" ++ show num

nextLabel :: Label -> Label
nextLabel (Lab num) = Lab $ num + 1

data Val
  = IntV Integer
  | RegV Register
  | BoolV Bool
  | VoidV
  deriving (Eq)

instance Show Val where
  show (IntV i)      = show i
  show (RegV reg)    = show reg
  show (BoolV False) = "0"
  show (BoolV True)  = "1"
