-- File generated by the BNF Converter (bnfc 2.9.4).

-- Templates for pattern matching on abstract syntax

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Latte.Skel where

import Prelude (($), Either(..), String, (++), Show, show)
import qualified Latte.Abs

type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transIdent :: Latte.Abs.Ident -> Result
transIdent x = case x of
  Latte.Abs.Ident string -> failure x

transProgram :: Show a => Latte.Abs.Program' a -> Result
transProgram x = case x of
  Latte.Abs.Program _ topdefs -> failure x

transTopDef :: Show a => Latte.Abs.TopDef' a -> Result
transTopDef x = case x of
  Latte.Abs.FnDef _ type_ ident args block -> failure x

transArg :: Show a => Latte.Abs.Arg' a -> Result
transArg x = case x of
  Latte.Abs.Arg _ type_ ident -> failure x

transBlock :: Show a => Latte.Abs.Block' a -> Result
transBlock x = case x of
  Latte.Abs.Block _ stmts -> failure x

transStmt :: Show a => Latte.Abs.Stmt' a -> Result
transStmt x = case x of
  Latte.Abs.Empty _ -> failure x
  Latte.Abs.BStmt _ block -> failure x
  Latte.Abs.Decl _ type_ items -> failure x
  Latte.Abs.Ass _ lvalue expr -> failure x
  Latte.Abs.Incr _ lvalue -> failure x
  Latte.Abs.Decr _ lvalue -> failure x
  Latte.Abs.Ret _ expr -> failure x
  Latte.Abs.VRet _ -> failure x
  Latte.Abs.Cond _ expr stmt -> failure x
  Latte.Abs.CondElse _ expr stmt1 stmt2 -> failure x
  Latte.Abs.While _ expr stmt -> failure x
  Latte.Abs.ForEach _ type_ ident expr stmt -> failure x
  Latte.Abs.SExp _ expr -> failure x

transItem :: Show a => Latte.Abs.Item' a -> Result
transItem x = case x of
  Latte.Abs.NoInit _ ident -> failure x
  Latte.Abs.Init _ ident expr -> failure x

transLValue :: Show a => Latte.Abs.LValue' a -> Result
transLValue x = case x of
  Latte.Abs.LVar _ ident -> failure x
  Latte.Abs.LAt _ ident expr -> failure x

transType :: Show a => Latte.Abs.Type' a -> Result
transType x = case x of
  Latte.Abs.Int _ -> failure x
  Latte.Abs.Str _ -> failure x
  Latte.Abs.Bool _ -> failure x
  Latte.Abs.Void _ -> failure x
  Latte.Abs.Array _ type_ -> failure x
  Latte.Abs.Fun _ type_ types -> failure x

transExpr :: Show a => Latte.Abs.Expr' a -> Result
transExpr x = case x of
  Latte.Abs.ELValue _ lvalue -> failure x
  Latte.Abs.ELitInt _ integer -> failure x
  Latte.Abs.ELitTrue _ -> failure x
  Latte.Abs.ELitFalse _ -> failure x
  Latte.Abs.EApp _ ident exprs -> failure x
  Latte.Abs.EString _ string -> failure x
  Latte.Abs.ELength _ expr -> failure x
  Latte.Abs.Neg _ expr -> failure x
  Latte.Abs.Not _ expr -> failure x
  Latte.Abs.EMul _ expr1 mulop expr2 -> failure x
  Latte.Abs.EAdd _ expr1 addop expr2 -> failure x
  Latte.Abs.ERel _ expr1 relop expr2 -> failure x
  Latte.Abs.EAnd _ expr1 expr2 -> failure x
  Latte.Abs.EOr _ expr1 expr2 -> failure x
  Latte.Abs.ENew _ type_ expr -> failure x

transAddOp :: Show a => Latte.Abs.AddOp' a -> Result
transAddOp x = case x of
  Latte.Abs.Plus _ -> failure x
  Latte.Abs.Minus _ -> failure x

transMulOp :: Show a => Latte.Abs.MulOp' a -> Result
transMulOp x = case x of
  Latte.Abs.Times _ -> failure x
  Latte.Abs.Div _ -> failure x
  Latte.Abs.Mod _ -> failure x

transRelOp :: Show a => Latte.Abs.RelOp' a -> Result
transRelOp x = case x of
  Latte.Abs.LTH _ -> failure x
  Latte.Abs.LE _ -> failure x
  Latte.Abs.GTH _ -> failure x
  Latte.Abs.GE _ -> failure x
  Latte.Abs.EQU _ -> failure x
  Latte.Abs.NE _ -> failure x
