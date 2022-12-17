{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE InstanceSigs #-}

module Instructions where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map                      as Map
import           Distribution.Simple            ( VersionInterval )
import           Latte.Abs
import           Types
import           Utils

data Instruction
  = ArtI Register ArtOp Val Val
  | CompareInstruction Register RelOp CType Val Val
  | BrI Val Label Label
  | JmpI Label
  | IfElseI Val Label Label Label String String
  | WhileI Val String Label Label Label String
  | AddV Var CType
  | AddClassI String Var CType
  | AddNullI Var CType
  | InitI Var CType
  | GetV Var CType Register
  | SetV Var CType Val
  | SetFieldI Register Ident Val Integer Val CType
  | BoolI Register BoolOp Val Val
  | RetI CType Val
  | CastStrI Register Int Int
  | ConstI Int Int String
  | VRetI
  | CallI Register CType String String
  | RetVoidI
  | RetDummyStrI
  | RetDummyI CType
  deriving (Eq)

-- reg = getelementptr %name, %name* val, i32 num
-- store ctype val, ctype* reg

instance Show Instruction where
  show :: Instruction -> String
  show (AddNullI v (CClass (Ident name) _)) =
    "\n;--- Struct ["
      ++ name
      ++ "] declaration ---\n"
      ++ show v ++ " = alloca %"
      ++ name
      ++ "*\n"
      ++ "store %"
      ++ name
      ++ "* null, %"
      ++ name
      ++ "** "
      ++ show v
      ++ "\n;--- End of struct declaration ---\n\n"
  show (AddNullI v _) = ""
  show (AddClassI tmp v (CClass (Ident name) _)) =
    "\n;--- Struct ["
      ++ name
      ++ "] declaration ---\n"
      ++ "%"
      ++ tmp
      ++ " = alloca %"
      ++ name
      ++ "\n"
      ++ show v
      ++ " = alloca %"
      ++ name
      ++ "*\n"
      ++ "store %"
      ++ name
      ++ "* %"
      ++ tmp
      ++ ", %"
      ++ name
      ++ "** "
      ++ show v
      ++ "\n;--- End of struct declaration ---\n\n"
  show (AddClassI tmp v _) = ""
  show (SetFieldI reg (Ident name) objVal num aVal aType) =
    show reg
      ++ "= getelementptr %"
      ++ name
      ++ ", %"
      ++ name
      ++ "* "
      ++ show objVal
      ++ ",  i32 0, i32 "
      ++ show num
      ++ "\nstore "
      ++ show aType
      ++ " "
      ++ show aVal
      ++ ", "
      ++ show aType
      ++ "* "
      ++ show reg
  show RetVoidI          = "ret void\n"
  show RetDummyStrI      = "%_ = inttoptr i32 0 to i8*\n ret i8* %_\n"
  show (RetDummyI ctype) = "ret " ++ show ctype ++ " 0\n"
  show (CallI reg ctype name args) =
    show reg ++ " = call " ++ show ctype ++ " @" ++ name ++ "(" ++ args ++ ")\n"
  show (ConstI n len str) =
    "@s"
      ++ show n
      ++ " = private constant ["
      ++ show len
      ++ " x i8] c\""
      ++ prepString str
      ++ "\\00\"\n"
  show (CastStrI reg len n) =
    show reg
      ++ " = bitcast ["
      ++ show len
      ++ " x i8]* @s"
      ++ show n
      ++ " to i8*\n"
  show (ArtI register operator value1 value2) =
    show register
      ++ " = "
      ++ show operator
      ++ " i32 "
      ++ show value1
      ++ ", "
      ++ show value2
      ++ "\n"
  show (CompareInstruction resultRegister operator ctype value1 value2) =
    show resultRegister
      ++ " = icmp "
      ++ relOpToLLVM operator
      ++ " "
      ++ show ctype
      ++ " "
      ++ show value1
      ++ ", "
      ++ show value2
      ++ "\n"
  show (BrI reg label1 label2) =
    "br i1 "
      ++ show reg
      ++ ", label "
      ++ "%"
      ++ show label1
      ++ ", label "
      ++ "%"
      ++ show label2
      ++ "\n"
  show (JmpI label) = "br label %" ++ show label ++ "\n"
  show (IfElseI exprReg lTrue lFalse lEnd trueCode falseCode) =
    show (BrI exprReg lTrue lFalse)
      ++ show lTrue
      ++ ": \n"
      ++ trueCode
      ++ show (JmpI lEnd)
      ++ show lFalse
      ++ ":\n"
      ++ falseCode
      ++ show (JmpI lEnd)
      ++ show lEnd
      ++ ":\n"
  show (AddV var (CClass (Ident name) _)) =
    show var ++ " = alloca %" ++ name ++ "\n"
  show (AddV var ctype) = show var ++ " = alloca " ++ show ctype ++ "\n"

  show (InitI var ctype) =
    "store " ++ show ctype ++ " 0, " ++ show ctype ++ "* " ++ show var ++ "\n"
  -- show (GetV reg (CClass (Ident name) _) resultReg) =
  --   show resultReg
  --     ++ " = load %"
  --     ++ name
  --     ++ ", %"
  --     ++ name
  --     ++ "* "
  --     ++ show reg
  --     ++ "\n"
  show (GetV reg ctype resultReg) =
    show resultReg
      ++ " = load "
      ++ show ctype
      ++ ", "
      ++ show ctype
      ++ "* "
      ++ show reg
      ++ "\n"
  -- show (SetC reg var (CClass (Ident name) fields) reg) =
  --   show reg ++ " = load %"++name++"*,%"++name++"** "++show var++
  --   "\nstore %"++name++"* %r10, %"++name++"** %var1"
  show (SetV var ctype reg) =
    "store "
      ++ show ctype
      ++ " "
      ++ show reg
      ++ ", "
      ++ show ctype
      ++ "* "
      ++ show var
      ++ "\n"
  show (BoolI reg op v1 v2) =
    show reg ++ " = " ++ show op ++ " i1 " ++ show v1 ++ ", " ++ show v2 ++ "\n"
  show (RetI ctype v) = "ret " ++ show ctype ++ " " ++ show v ++ "\n"
  show VRetI          = "ret void\n"
  show (WhileI exprReg exprCode lStart lTrue lEnd code) =
    show (JmpI lStart)
      ++ show lStart
      ++ ": \n"
      ++ exprCode
      ++ show (BrI exprReg lTrue lEnd)
      ++ show lTrue
      ++ ":\n"
      ++ code
      ++ show (JmpI lStart)
      ++ show lEnd
      ++ ": \n"


data BoolOp
  = AndOp
  | OrOp
  | XorOp
  deriving (Eq)

instance Show BoolOp where
  show AndOp = "and"
  show OrOp  = "or"
  show XorOp = "xor"

data ArtOp
  = AddOp
  | SubOp
  | DivOp
  | MulOp
  | ModOp
  deriving (Eq)

instance Show ArtOp where
  show AddOp = "add"
  show SubOp = "sub"
  show DivOp = "sdiv"
  show MulOp = "mul"
  show ModOp = "srem"

relOpToLLVM :: RelOp -> String
relOpToLLVM (LTH _) = "slt"
relOpToLLVM (LE  _) = "sle"
relOpToLLVM (GTH _) = "sgt"
relOpToLLVM (GE  _) = "sge"
relOpToLLVM (EQU _) = "eq"
relOpToLLVM (NE  _) = "ne"
