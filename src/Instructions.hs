{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Instructions where

import Control.Monad.Except
import Control.Monad.State
import Data.Map as Map
import Latte.Abs
import Types

data Instruction
  = ArtI Register ArtOp Val Val
  | CompareInstruction Register RelOp CType Val Val 
  | BrI Val Label Label
  | JmpI Label
  | IfElseI Val Label Label Label Label String String Label Label
  | WhileI Val String Label Label Label String
  | AddV Var CType
  | InitI Var CType
  | GetV Register CType Register
  | SetV Var CType Register
  | SetRegister Register CType Register
  | BoolI Register BoolOp Val Val
  | RetI CType Register
  | VRetI
  deriving (Eq)

instance Show Instruction where
  show (ArtI register operator value1 value2) = show register ++ " = " ++ show operator ++ " i32 " ++ show value1 ++ ", " ++ show value2 ++ "\n"
  show (CompareInstruction resultRegister operator ctype value1 value2) = 
    show resultRegister ++ " = icmp " ++ relOpToLLVM operator ++ " " ++ show ctype ++ " " ++ show value1 ++ ", " ++ show value2 ++ "\n"
  show (BrI reg label1 label2) = "br i1 " ++ show reg ++ ", label " ++ "%" ++ show label1 ++ ", label " ++ "%" ++ show label2 ++ "\n"
  show (JmpI label) = "br label %" ++ show label ++ "\n"
  show (IfElseI exprReg lBase lTrue lFalse lEnd trueCode falseCode endTrue endFalse) = show (JmpI lBase) ++ show  lBase ++ ":\n" ++ show (BrI exprReg lTrue lFalse) ++ show lTrue ++ ": \n" ++ trueCode ++ show (JmpI endTrue) ++ show  endTrue ++ ":\n" ++ show (JmpI lEnd) ++ show lFalse ++ ":\n" ++ falseCode ++ show (JmpI endFalse) ++ show  endFalse ++ ":\n"   ++ show (JmpI lEnd) ++ show lEnd ++ ":\n"
  show (WhileI exprReg exprCode lStart lTrue lEnd code) = show (JmpI lStart) ++ show lStart ++ ": \n" ++ exprCode ++ show (BrI exprReg lTrue lEnd) ++ show lTrue ++ ":\n" ++ code ++ show (JmpI lStart) ++ show lEnd ++ ": \n"
  show (AddV var ctype) = show var ++ " = alloca " ++ show ctype ++ "\n"
  show (InitI var ctype) = "store " ++ show ctype ++ " 0, " ++ show ctype ++ "* " ++ show var ++ "\n"
  show (GetV reg ctype resultReg) = show resultReg ++ " = load " ++ show ctype ++ ", " ++ show ctype ++ "* " ++ show reg ++ "\n"
  show (SetV var ctype reg) = "store " ++ show ctype ++ " " ++ show reg ++ ", " ++ show ctype ++ "* " ++ show var ++ "\n"
  show (SetRegister resultReg ctype exprReg) = show resultReg ++ " = " ++ show ctype ++ " " ++ show exprReg ++ "\n"
  show (BoolI reg op v1 v2) = show reg ++ " = " ++ show op ++ " i1 " ++ show v1 ++ ", " ++ show v2 ++ "\n"
  show (RetI ctype reg) = "ret " ++ show ctype ++ " " ++ show reg ++ "\n"
  show VRetI = "ret void\n"

data BoolOp
  = AndOp
  | OrOp
  | XorOp
  deriving (Eq)

instance Show BoolOp where
  show AndOp = "and"
  show OrOp = "or"
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
relOpToLLVM (LE _) = "sle"
relOpToLLVM (GTH _) = "sgt"
relOpToLLVM (GE _) = "sge"
relOpToLLVM (EQU _) = "eq"
relOpToLLVM (NE _) = "ne"
