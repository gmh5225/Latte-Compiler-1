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

type ExpressionResult = (VarState, LLVMCode, CType, StrDeclarations)

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
  (argsCode, initArgsCode) <- compileArgs args
  (blockCode, strDeclarations) <- compileBlock block
  let blockCore = strDeclarations ++ "\ndefine " ++ typeToLLVM retType ++ " @" ++ name ++ "(" ++ argsCode ++ ") {\n" ++ initArgsCode ++"\n" ++ blockCode
  case retType of
    Void _ -> return $ blockCore ++ "ret void\n}\n"
    Str _ -> return $ blockCore ++ "%_ = call i8* @malloc(i32 1)\n ret i8* %_\n\n}\n"
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
  (exprResult, exprCode, _, strDeclarations) <- compileExpr expr  
  case exprResult of
    Left exprVal -> do
      setVarVal ident exprVal
      return (exprCode,strDeclarations)
    Right exprReg -> do
      setVarReg ident exprReg
      return (exprCode,strDeclarations)
compileStmt (Incr pos ident) = compileStmt (Ass pos ident (EAdd pos (EVar pos ident) (Plus pos) (ELitInt pos 1)))
compileStmt (Decr pos ident) = compileStmt (Ass pos ident (EAdd pos (EVar pos ident) (Minus pos) (ELitInt pos 1)))
compileStmt (Ret pos expr) = do
  (exprResult, exprCode, exprType, strDeclarations) <- compileExpr expr
  case exprResult of
    Left exprVal -> do return ("ret i32 "++ show exprVal ++ "\n" ,strDeclarations)
    Right exprReg -> do
      return (exprCode ++ show (RetI exprType exprReg), strDeclarations)
compileStmt (VRet _) = return (show VRetI, "")
compileStmt (Cond _ (ELitTrue _) stmt) = compileStmt stmt
compileStmt (Cond _ (ELitFalse _) stmt) = return ("", "")
compileStmt (Cond _ expr stmt) = do
  (exprResult, exprCode, exprType, strDeclarations1) <- compileExpr expr
  (stmtCode, strDeclarations2) <- compileStmt stmt
  labTrue <- useLabel
  labFalse <- useLabel
  labEnd <- useLabel
  case exprResult of
    Left exprVal -> do
      return ("","")
    Right exprReg -> do
      return (exprCode ++ show (IfElseI exprReg labTrue labFalse labEnd stmtCode ""), strDeclarations1 ++ strDeclarations2)
compileStmt (CondElse _ (ELitTrue _) stmt1 stmt2) = compileStmt stmt1
compileStmt (CondElse _ (ELitFalse _) stmt1 stmt2) = compileStmt stmt2
compileStmt (CondElse _ expr stmt1 stmt2) = do
  (exprResult, exprCode, exprType, strDeclarations1) <- compileExpr expr
  (stmt1Res, strDeclarations2) <- compileStmt stmt1
  (stmt2Res, strDeclarations3) <- compileStmt stmt2
  labTrue <- useLabel
  labFalse <- useLabel
  labEnd <- useLabel
  case exprResult of
    Left exprVal -> do return ("","")
    Right exprReg -> do
      return (exprCode ++ show (IfElseI exprReg labTrue labFalse labEnd stmt1Res stmt2Res), strDeclarations1 ++ strDeclarations2 ++ strDeclarations3)
compileStmt (While pos expr stmt) = do
  (exprResult, exprCode, exprType, strDeclarations1) <- compileExpr expr
  (stmtRes, strDeclarations2) <- compileStmt stmt
  labCheck <- useLabel
  labTrue <- useLabel
  labEnd <- useLabel
  case exprResult of
    Left exprVal -> do return ("","")
    Right exprReg -> do
      return (show (WhileI exprReg exprCode labCheck labTrue labEnd stmtRes), strDeclarations1 ++ strDeclarations2)
compileStmt (SExp pos expr) = do
  (_, code, _, strDeclarations) <- compileExpr expr
  return (code, strDeclarations)

initVar :: CType -> [Item] -> Compl (LLVMCode, StrDeclarations)
initVar varType [] = do return ("", "")
initVar varType ((NoInit pos ident) : items) = do
  newVarReg <- addVar varType ident
  (varCode, strDeclarations) <- initVar varType items 
  case varType of
    CStr -> return (varCode , strDeclarations)
    _ -> return (varCode  , strDeclarations)

initVar varType ((Init pos ident expr) : items) = do
  (exprResult, exprCode, _, strDeclarations1) <- compileExpr expr
  case exprResult of
    Left val -> do
      addVar varType ident
      setVarVal ident val
      (varsCode, strDeclarations2) <- initVar varType items
      return (exprCode ++ varsCode  , strDeclarations1 ++ strDeclarations2)
    Right reg -> do
      addVar varType ident
      setVarReg ident reg

      (varsCode, strDeclarations2) <- initVar varType items
      return (exprCode++varsCode , strDeclarations1 ++ strDeclarations2)

compileExpr :: Expr -> Compl ExpressionResult
compileExpr (EAdd pos e1 (Plus posOp) e2) = compileBinExp e1 e2 AddOp
compileExpr (EAdd pos e1 (Minus posOp) e2) = compileBinExp e1 e2 SubOp
compileExpr (EMul pos e1 (Times posOp) e2) = compileBinExp e1 e2 MulOp
compileExpr (EMul pos e1 (Div posOp) e2) = compileBinExp e1 e2 DivOp
compileExpr (EMul pos e1 (Mod posOp) e2) = compileBinExp e1 e2 ModOp
compileExpr (ERel pos e1 op e2) = complieCmpExpresion e1 e2 op
compileExpr (ELitTrue pos) = do
  reg <- useNewReg
  return (Right reg, show reg ++ " = " ++ "or i1 1,1" ++ "\n", CBool, "")
compileExpr (ELitFalse pos) = do
  reg <- useNewReg
  return (Right reg, show reg ++ " = " ++ "or i1 0,0" ++ "\n", CBool, "")
compileExpr (ELitInt pos num) = do
  reg <- useNewReg
  return (Left $ IntVal num,"", CInt, "")
compileExpr (EVar pos ident) = do
  (varType, varVal) <- getVar ident
  newReg <- useNewReg
  case varType of
    CVoid -> return (Right $ Reg 0, "", CVoid, "")
    _ -> do return (varVal,"",varType,"")
compileExpr (EApp pos (Ident name) exprs) = do
  (argStr, compileStr, strDeclarations) <- compileArgsExpr exprs
  (retType, argsTypes) <- getProc $ Ident name
  reg <- useNewReg
  case retType of
    CVoid -> return (Right reg, compileStr ++ "call void @" ++ name ++ "(" ++ argStr ++ ")\n", CVoid, strDeclarations)
    _ -> return (Right reg, compileStr ++ show reg ++ " = call " ++ show retType ++ " @" ++ name ++ "(" ++ argStr ++ ")\n", retType, strDeclarations)
compileExpr (EString pos str) = do
  reg <- useNewReg
  let (Reg num) = reg
  let len = length str + 1
  let asignCode = show reg ++ " = bitcast [" ++ show len ++ " x i8]* @s" ++ show num ++ " to i8*\n"
  let strDeclarations = "@s" ++ show num ++ " = private constant [" ++ show len ++ " x i8] c\"" ++ prepString str ++ "\\00\"\n"
  return (Right reg, asignCode, CStr, strDeclarations)
compileExpr (Neg pos expr) = compileExpr (EAdd pos (ELitInt pos 0) (Minus pos) expr)
compileExpr (EAnd pos e1 e2) = do
  (result1, text1, ctype1, _) <- compileExpr e1
  labE1True <- useLabel
  labE1False <- useLabel
  labEnd <- useLabel
  (Reg num) <- useNewReg
  let ident = Ident $ "and" ++ show num
  (varText, sd) <- initVar CBool [Init pos ident (ELitTrue pos)]
  (setTrueText, sd2) <- compileStmt (Ass pos ident e2)
  (setE2Text, sd3) <- compileStmt (Ass pos ident (ELitFalse pos))
  case result1 of
    Left val1 -> do  return (Left val1, "", CBool, sd ++ sd2 ++ sd3)
    Right reg1 -> do
      let ifInstr = IfElseI reg1 labE1True labE1False labEnd setTrueText setE2Text
      (ctype, var) <- getVar ident
      res <- useNewReg
      return (Right res, varText ++ text1 ++ show ifInstr ++ "", CBool, sd ++ sd2 ++ sd3)
compileExpr (EOr pos e1 e2) = do
  (result1, text1, ctype1, _) <- compileExpr e1
  labE1True <- useLabel
  labE1False <- useLabel
  labEnd <- useLabel
  (Reg num) <- useNewReg
  let ident = Ident $ "or" ++ show num
  (varText, sd1) <- initVar CBool [Init pos ident (ELitFalse pos)]
  (setTrueText, sd2) <- compileStmt (Ass pos ident (ELitTrue pos))
  (setE2Text, sd3) <- compileStmt (Ass pos ident e2)
  case result1 of
    Left val1 -> do  return (Left val1, "", CBool, sd1 ++ sd2 ++ sd3)
    Right reg1 -> do
      let ifInstr = IfElseI reg1 labE1True labE1False labEnd setTrueText setE2Text
      (ctype, var) <- getVar ident
      res <- useNewReg
      return (Right res, varText ++ text1 ++ show ifInstr ++ "", CBool, sd1 ++ sd2 ++ sd3)

compileExpr (Not pos expr) = do
  (exprResult, code, ctype, strDeclarations) <- compileExpr expr
  reg <- useNewReg
  case exprResult of
    Left exprVal -> do  return (Left exprVal, "", CBool,"")
    Right exprReg -> do
      return (Right reg, code ++ show (BoolI reg XorOp (IntVal 1) (RegVal exprReg)), CBool, strDeclarations)

compileArgsExpr :: [Expr] -> Compl (String, String, String)
compileArgsExpr [] = return ("", "", "")
compileArgsExpr [expr] = do
  (exprRes, exprCode, ctype, strDeclarations) <- compileExpr expr
  return (show ctype ++ " " ++ showVarVal exprRes, exprCode, strDeclarations)
compileArgsExpr (expr : exprs) = do
  (exprRes, exprCode, ctype, strDeclarations1) <- compileExpr expr
  (argStr, argsCode, strDeclarations2) <- compileArgsExpr exprs
  return (show ctype ++ " " ++ showVarVal exprRes ++ "," ++ argStr, exprCode ++ argsCode, strDeclarations1 ++ strDeclarations2)


compileBinExp :: Expr -> Expr -> ArtOp -> Compl ExpressionResult
compileBinExp e1 e2 op = do
  (exprRes1, exprCode1, e1Type, strDeclarations1) <- compileExpr e1
  (exprRes2, exprCode2, e2Type, strDeclarations2) <- compileExpr e2
  case e1Type of
    CStr -> do
      (resultReg, resultCode, _, strDeclarations3) <- compileExpr (EApp (Just (0, 0)) (Ident "concat") [e1, e2])
      return (resultReg, resultCode, CStr, strDeclarations1 ++ strDeclarations2 ++ strDeclarations3)
    _ -> do
      reg <- useNewReg
      return (Right reg, exprCode1 ++ exprCode2 ++ show  (ArtI op exprRes1 exprRes2 reg), e1Type, strDeclarations1 ++ strDeclarations2)

complieCmpExpresion :: Expr -> Expr -> RelOp -> Compl ExpressionResult
complieCmpExpresion e1 e2 operator = do
  (result1, code1, type1, stringsDeclarations1) <- compileExpr e1
  (result2, code2, type2, stringsDeclarations2) <- compileExpr e2
  resultRegister <- useNewReg
  return (Right resultRegister, code1 ++ code2 ++ show (CompareInstruction resultRegister operator type1 result1 result2), CBool, stringsDeclarations1 ++ stringsDeclarations2)