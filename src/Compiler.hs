module Compiler where

import Control.Monad.Except
import Control.Monad.State
import Data.Char (ord)
import Data.Map as Map
import Env
import GHC.RTS.Flags (TraceFlags (user))
import Instructions
import Latte.Abs
import Numeric
import Types

type LLVMCode = String

type StrDeclarations = String

type ArgsCode = String

type InitArgsCode = String

type ExpressionResult = (Val, LLVMCode, CType, StrDeclarations)

pref :: String -> String
pref str
  | length str > 1 = str
  | otherwise = "0" ++ str

prepString :: [Char] -> [Char]
prepString (c : str) = "\\" ++ pref (showHex (ord c) "") ++ prepString str
prepString [] = ""

funcDeclarations :: String
funcDeclarations =
  "declare i32 @puts(i8*)\n"
    ++ "declare i8* @readString()\n"
    ++ "declare i32 @readInt()\n"
    ++ "declare i8* @malloc(i32)\n"
    ++ "declare i8* @strcat(i8*,i8*)\n"
    ++ "declare i32 @strlen(i8*)\n"
    ++ "declare i8* @strcpy(i8*,i8*)\n"
    ++ "declare void @printInt(i32 %x)\n"
    ++ "declare void @printString(i8* %x)\n"
    ++ "declare i32 @printf(i8*, ...)\n"
    ++ "declare i32 @scanf(i8*, ...)\n"
    ++ "declare void @error()\n"
    ++ "declare i8* @concat(i8* %s1, i8* %s2)\n"

compile :: Program -> IO (Either Error String)
compile program = do
  result <- runStateT (runExceptT (compileProgram program)) initEnv
  case fst result of
    (Left error) -> return $ Left error
    (Right resultText) -> return $ Right (funcDeclarations ++ resultText)

compileProgram :: Program -> Compl LLVMCode
compileProgram (Program pos topDefs) = do
  addFuncDefinition topDefs
  compileFuncDefs topDefs

addFuncDefinition :: [TopDef] -> Compl ()
addFuncDefinition [] = return ()
addFuncDefinition ((FnDef pos retType (Ident name) args block) : defs) = do
  _ <- addProc (getCType retType) (Ident name) (Prelude.map getArgCType args)
  addFuncDefinition defs

compileFuncDefs :: [TopDef] -> Compl LLVMCode
compileFuncDefs [] = return ""
compileFuncDefs (def : defs) = do
  llvmCode1 <- compileFuncDef def
  llvmCode2 <- compileFuncDefs defs
  return $ llvmCode1 ++ llvmCode2

getArgCType :: Arg -> CType
getArgCType (Arg pos argType ident) = getCType argType

compileFuncDef :: TopDef -> Compl LLVMCode
compileFuncDef (FnDef pos retType (Ident name) args block) = do

  -- Funkcja ma osobny store i zmienne - nie ma dostepu do tych z main
  (prevEnv, prevVenv, prevStore, prevLoc, prevReg, prevLabel, prevVar) <- get

  (argsCode, initArgsCode) <- compileArgs args
  (blockCode, strDeclarations) <- compileBlock block

  (newEnv, newVenv, newStore, newLoc, newReg, newLabel, newVar) <- get
  put (prevEnv, prevVenv, prevStore, newLoc, newReg, newLabel, newVar)

  let blockCore = strDeclarations ++ "\ndefine " ++ typeToLLVM retType ++ " @" ++ name ++ "(" ++ argsCode ++ ") {\n" ++ initArgsCode ++"\n" ++ blockCode
  case retType of
    Void _ -> return $ blockCore ++ "ret void\n}\n"
    Str _ -> return $ blockCore ++ "%_ = call i8* @malloc(i32 1)\n ret i8* %_\n\n}\n" --TODO: Tu nie moze vyc zawsze tego samego %_
    _ -> return $ blockCore ++ "ret " ++ typeToLLVM retType ++ " 0\n}\n"

compileArgs :: [Arg] -> Compl (ArgsCode, InitArgsCode)
compileArgs [] = do return ("", "")
compileArgs [Arg pos argType ident] = do
  reg <- addVar (getCType argType) ident
  return (show (getCType argType) ++ " " ++ show reg,"")
compileArgs (arg : args) = do
  (argCode, initArgCode) <- compileArgs [arg]
  (argsCode, initArgsCode) <- compileArgs args
  return (argCode ++ "," ++ argsCode, initArgCode ++ initArgsCode)

compileBlock :: Block -> Compl (LLVMCode, StrDeclarations)
compileBlock (Block pos stmts) = compileStmts stmts

compileStmts :: [Stmt] -> Compl (LLVMCode, StrDeclarations)
compileStmts [] = do return ("", "")
compileStmts (stmt : stmts) = do
  (stmtCode, strDeclarations1) <- compileStmt stmt
  (stmtsCode, strDeclarations2) <- compileStmts stmts
  return (stmtCode ++ stmtsCode, strDeclarations1 ++ strDeclarations2)

compileStmt :: Stmt -> Compl (LLVMCode, StrDeclarations)
compileStmt (Empty pos) = do return ("", "")
compileStmt (BStmt _ (Block _ stmts)) = do
  (penv, venv, store, loc, reg, label, var) <- get
  (blockCode, strDeclarations) <- compileStmts stmts
  (postPenv, postVenv, postStore, postLoc, postReg, postLabel, postVar) <- get
  put (penv, venv, postStore, loc, postReg, postLabel, postVar)
  return ("\n " ++ blockCode ++ "\n", strDeclarations)
compileStmt (Decl pos varType items) = initVar (getCType varType) items
compileStmt (Ass pos ident expr) = do
  (exprResult, exprCode, _, strDeclarations) <- complieExpression expr  
  setVarVal ident exprResult
  return (exprCode,strDeclarations)
compileStmt (Incr pos ident) = compileStmt (Ass pos ident (EAdd pos (EVar pos ident) (Plus pos) (ELitInt pos 1)))
compileStmt (Decr pos ident) = compileStmt (Ass pos ident (EAdd pos (EVar pos ident) (Minus pos) (ELitInt pos 1)))
compileStmt (Ret pos expr) = do
  (exprResult, exprCode, exprType, strDeclarations) <- complieExpression expr
  case exprResult of
    (IntV exprVal) -> do return ("ret i32 "++ show exprVal ++ "\n" ,strDeclarations)
    (RegV exprReg) -> do
      return (exprCode ++ show (RetI exprType exprReg), strDeclarations)
compileStmt (VRet _) = return (show VRetI, "")
compileStmt (Cond _ (ELitTrue _) stmt) = compileStmt stmt
compileStmt (Cond _ (ELitFalse _) stmt) = return ("", "")
compileStmt (Cond pos expr stmt) = compileStmt (CondElse pos expr stmt (Empty pos)) --TODO: Optymalizacja
compileStmt (CondElse _ (ELitTrue _) stmt1 stmt2) = compileStmt stmt1
compileStmt (CondElse _ (ELitFalse _) stmt1 stmt2) = compileStmt stmt2
compileStmt (CondElse _ expr stmt1 stmt2) = do
  
  -- Wykonuje warunek
  (exprResult, exprCode, exprType, strDeclarations1) <- complieExpression expr

  -- zapisuje store przef ifem
  (prevEnv, prevVenv, prevStore, prevLoc, prevReg, prevLabel, prevVar) <- get

  -- Wykonuje blok true
  (stmt1Res, strDeclarations2) <- compileStmt stmt1

  -- zapisuje store po bloklu true
  (trueEnv, trueVenv, trueStore, trueLoc, trueReg, trueLabel, trueVar) <- get

  -- -- wrcam z stanem do pierwszego
  setStore prevStore
  -- put (prevEnv, prevVenv, prevStore, prevLoc, prevReg, prevLabel, prevVar)

  -- Wykonuje blok flase
  (stmt2Res, strDeclarations3) <- compileStmt stmt2
    
  -- zapisuje store po bloklu false
  (falseEnv, falseVenv, falseStore, falseLoc, falseReg, falseLabel, falseVar) <- get

   -- wrcam z stanem do pierwszego
  setStore prevStore
  -- put (prevEnv, prevVenv, prevStore, prevLoc, prevReg, prevLabel, prevVar)

  -- loop po prevStore jezeli jalas lokacja z prevStore ma inne Val w true, false -> do phi (Na poczatek mozna dla kazdej)

  labBase <- useLabel
  labTrue <- useLabel
  labFalse <- useLabel
  labEnd <- useLabel
  
  resultCode <- generatePhi prevStore trueStore falseStore labBase labTrue labFalse 
  
  return ( exprCode++ show (IfElseI exprResult labBase labTrue labFalse labEnd stmt1Res stmt2Res) ++  resultCode, strDeclarations1 ++ strDeclarations2 ++ strDeclarations3)

compileStmt (While pos expr stmt) = do return ("","")
  -- (exprResult, exprCode, exprType, strDeclarations1) <- complieExpression expr
  -- (stmtRes, strDeclarations2) <- compileStmt stmt
  -- labCheck <- useLabel
  -- labTrue <- useLabel
  -- labEnd <- useLabel
  -- case exprResult of
  --   IntV exprVal -> do return ("","")
  --   RegV exprReg -> do
  --     return (show (WhileI exprReg exprCode labCheck labTrue labEnd stmtRes), strDeclarations1 ++ strDeclarations2)
compileStmt (SExp pos expr) = do
  (_, code, _, strDeclarations) <- complieExpression expr
  return (code, strDeclarations)

initVar :: CType -> [Item] -> Compl (LLVMCode, StrDeclarations)
initVar varType [] = do return ("", "")
initVar CStr ((NoInit pos ident) : items) = initVar CStr ((Init pos ident (EString pos "")) : items)
initVar CInt ((NoInit pos ident) : items) = initVar CInt ((Init pos ident (ELitInt pos 0)) : items)
initVar CBool ((NoInit pos ident) : items) = initVar CBool ((Init pos ident (ELitFalse pos)) : items) 
initVar varType ((Init pos ident expr) : items) = do
  (exprResult, exprCode, _, strDeclarations1) <- complieExpression expr
  addVar varType ident
  setVarVal ident exprResult
  (varsCode, strDeclarations2) <- initVar varType items
  return (exprCode ++ varsCode  , strDeclarations1 ++ strDeclarations2)

complieExpression :: Expr -> Compl ExpressionResult
complieExpression (EAdd pos e1 (Plus posOp) e2) = compileBinaryExpression e1 e2 AddOp
complieExpression (EAdd pos e1 (Minus posOp) e2) = compileBinaryExpression e1 e2 SubOp
complieExpression (EMul pos e1 (Times posOp) e2) = compileBinaryExpression e1 e2 MulOp
complieExpression (EMul pos e1 (Div posOp) e2) = compileBinaryExpression e1 e2 DivOp
complieExpression (EMul pos e1 (Mod posOp) e2) = compileBinaryExpression e1 e2 ModOp
complieExpression (ERel pos e1 op e2) = complieCmpExpression e1 e2 op
complieExpression (ELitTrue pos) = return (BoolV True,"",CBool,"")
complieExpression (ELitFalse pos) = return (BoolV False,"",CBool,"")
complieExpression (ELitInt pos num) = return (IntV num,"", CInt, "")
complieExpression (EVar pos ident) = do
  (varType, varVal) <- getVar ident
  case varType of
    CVoid -> return (RegV $ Reg 0, "", CVoid, "")
    _ -> do return (varVal,"",varType,"")
complieExpression (EApp pos (Ident name) exprs) = do
  (argStr, compileStr, strDeclarations) <- compileArgsExpr exprs
  (retType, argsTypes) <- getProc $ Ident name
  reg <- useNewReg
  case retType of
    CVoid -> return (RegV reg, compileStr ++ "call void @" ++ name ++ "(" ++ argStr ++ ")\n", CVoid, strDeclarations)
    _ -> return (RegV reg, compileStr ++ show reg ++ " = call " ++ show retType ++ " @" ++ name ++ "(" ++ argStr ++ ")\n", retType, strDeclarations)
complieExpression (EString pos str) = do
  reg <- useNewReg
  let (Reg num) = reg
  let len = length str + 1
  let asignCode = show reg ++ " = bitcast [" ++ show len ++ " x i8]* @s" ++ show num ++ " to i8*\n"
  let strDeclarations = "@s" ++ show num ++ " = private constant [" ++ show len ++ " x i8] c\"" ++ prepString str ++ "\\00\"\n"
  return (RegV reg, asignCode, CStr, strDeclarations)
complieExpression (Neg pos expr) = complieExpression (EAdd pos (ELitInt pos 0) (Minus pos) expr)
complieExpression (EAnd pos e1 e2) = do return (IntV 0,"",CBool,"")
  -- (result1, text1, ctype1, _) <- complieExpression e1
  -- labE1True <- useLabel
  -- labE1False <- useLabel
  -- labEnd <- useLabel
  -- (Reg num) <- useNewReg
  -- let ident = Ident $ "and" ++ show num
  -- (varText, sd) <- initVar CBool [Init pos ident (ELitTrue pos)]
  -- (setTrueText, sd2) <- compileStmt (Ass pos ident e2)
  -- (setE2Text, sd3) <- compileStmt (Ass pos ident (ELitFalse pos))
  -- case result1 of
  --   IntV val1 -> do  return (IntV val1, "", CBool, sd ++ sd2 ++ sd3)
  --   RegV reg1 -> do
  --     let ifInstr = IfElseI reg1 labE1True labE1False labEnd setTrueText setE2Text
  --     (ctype, var) <- getVar ident
  --     res <- useNewReg
  --     return (RegV res, varText ++ text1 ++ show ifInstr ++ "", CBool, sd ++ sd2 ++ sd3)
complieExpression (EOr pos e1 e2) =  do return (IntV 0,"",CBool,"")
  -- (result1, text1, ctype1, _) <- complieExpression e1
  -- labE1True <- useLabel
  -- labE1False <- useLabel
  -- labEnd <- useLabel
  -- (Reg num) <- useNewReg
  -- let ident = Ident $ "or" ++ show num
  -- (varText, sd1) <- initVar CBool [Init pos ident (ELitFalse pos)]
  -- (setTrueText, sd2) <- compileStmt (Ass pos ident (ELitTrue pos))
  -- (setE2Text, sd3) <- compileStmt (Ass pos ident e2)
  -- case result1 of
  --   IntV val1 -> do  return (IntV val1, "", CBool, sd1 ++ sd2 ++ sd3)
  --   RegV reg1 -> do
  --     let ifInstr = IfElseI reg1 labE1True labE1False labEnd setTrueText setE2Text
  --     (ctype, var) <- getVar ident
  --     res <- useNewReg
  --     return (RegV res, varText ++ text1 ++ show ifInstr ++ "", CBool, sd1 ++ sd2 ++ sd3)

complieExpression (Not pos expr) = do
  (exprResult, code, ctype, strDeclarations) <- complieExpression expr
  reg <- useNewReg
  case exprResult of
    IntV exprVal -> do  return (IntV exprVal, "", CBool,"")
    RegV exprReg -> do
      return (RegV reg, code ++ show (BoolI reg XorOp (IntV 1) (RegV exprReg)), CBool, strDeclarations)

compileArgsExpr :: [Expr] -> Compl (String, String, String)
compileArgsExpr [] = return ("", "", "")
compileArgsExpr [expr] = do
  (exprRes, exprCode, ctype, strDeclarations) <- complieExpression expr
  return (show ctype ++ " " ++ show exprRes, exprCode, strDeclarations)
compileArgsExpr (expr : exprs) = do
  (exprRes, exprCode, ctype, strDeclarations1) <- complieExpression expr
  (argStr, argsCode, strDeclarations2) <- compileArgsExpr exprs
  return (show ctype ++ " " ++ show exprRes ++ "," ++ argStr, exprCode ++ argsCode, strDeclarations1 ++ strDeclarations2)

{- Returns specified function application expresion
    Params:
      ident - function identificator
      argumentExpresions 
-}
functionApplicationExpresion :: Ident -> [Expr] -> Expr
functionApplicationExpresion ident argumentExpresions = EApp (Just (0, 0)) ident argumentExpresions

{- Complie binary expression
    Params:
      expression1
      expression2
      comparision operator
-}
compileBinaryExpression :: Expr -> Expr -> ArtOp -> Compl ExpressionResult
compileBinaryExpression e1 e2 operator = do
  (result1, code1, type1, stringsDeclarations1) <- complieExpression e1
  (result2, code2, _, stringsDeclarations2) <- complieExpression e2
  case type1 of
    CStr -> do
      (result, code3, _, stringsDeclarations3) <- complieExpression $ functionApplicationExpresion (Ident "concat") [e1, e2]
      return (result, code1 ++ code2 ++ code3, CStr, stringsDeclarations1 ++ stringsDeclarations2 ++ stringsDeclarations3)
    _ -> do
      resultRegister <- useNewReg
      let instruction = show (ArtI resultRegister operator result1 result2)
      return (RegV resultRegister, code1 ++ code2 ++ instruction, type1, stringsDeclarations1 ++ stringsDeclarations2)

{- Complie comparision expresion
    Params:
      expression1 - compared expresion
      expression2 - compared expresion
 -} 
complieCmpExpression :: Expr -> Expr -> RelOp -> Compl ExpressionResult
complieCmpExpression e1 e2 operator = do
  (result1, code1, type1, stringsDeclarations1) <- complieExpression e1
  (result2, code2, type2, stringsDeclarations2) <- complieExpression e2
  resultRegister <- useNewReg
  return (RegV resultRegister, code1 ++ code2 ++ show (CompareInstruction resultRegister operator type1 result1 result2), CBool, stringsDeclarations1 ++ stringsDeclarations2)