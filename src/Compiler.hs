module Compiler where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Char            (ord)
import           Data.Map             as Map
import           Env
import           GHC.RTS.Flags        (TraceFlags (user))
import           Instructions
import           Latte.Abs
import           Numeric
import           Types

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
prepString (c:str) = "\\" ++ pref (showHex (ord c) "") ++ prepString str
prepString []      = ""

funcDeclarations :: String
funcDeclarations =
  "declare i32 @puts(i8*)\n" ++
  "declare i8* @readString()\n" ++
  "declare i32 @readInt()\n" ++
  "declare i8* @malloc(i32)\n" ++
  "declare i8* @strcat(i8*,i8*)\n" ++
  "declare i32 @strlen(i8*)\n" ++
  "declare i8* @strcpy(i8*,i8*)\n" ++
  "declare void @printInt(i32 %x)\n" ++
  "declare void @printString(i8* %x)\n" ++
  "declare i32 @printf(i8*, ...)\n" ++
  "declare i32 @scanf(i8*, ...)\n" ++
  "declare void @error()\n" ++ "declare i8* @concat(i8* %s1, i8* %s2)\n"

compileProgram :: Program -> IO (Either Error String)
compileProgram program = do
  result <- runStateT (runExceptT (complieTopDefs program)) initEnv
  case fst result of
    (Left error) -> return $ Left error
    (Right code) -> return $ Right (funcDeclarations ++ code)

complieTopDefs :: Program -> Compl LLVMCode
complieTopDefs (Program _ defs) = do
  addFuncDefinition defs
  compileFuncDefs defs

addFuncDefinition :: [TopDef] -> Compl ()
addFuncDefinition [] = return ()
addFuncDefinition (def:defs) = do
  addFunc def
  addFuncDefinition defs

compileFuncDefs :: [TopDef] -> Compl LLVMCode
compileFuncDefs [] = return ""
compileFuncDefs (def:defs) = do
  code1 <- compileFuncDef def
  code2 <- compileFuncDefs defs
  return (code1 ++ code2)

compileFuncDef :: TopDef -> Compl LLVMCode
compileFuncDef (FnDef _ retType (Ident name) args block) = do
  prevState <- get
  (argsCode, initArgsCode) <- compileArgs args
  (blockCode, strDeclarations) <- compileBlock block
  newState <- get
  -- TODO:
  put
    newState
      { sPenv = sPenv prevState
      , sVenv = sVenv prevState
      , sStore = sStore prevState
      }
  let blockCore =
        strDeclarations ++
        "\ndefine " ++
        typeToLLVM retType ++
        " @" ++
        name ++ "(" ++ argsCode ++ ") {\n" ++ initArgsCode ++ "\n" ++ blockCode
  case retType of
    Void _ -> return $ blockCore ++ "ret void\n}\n"
    Str _ ->
      return $ blockCore ++ "%_ = call i8* @malloc(i32 1)\n ret i8* %_\n\n}\n"
    _ -> return $ blockCore ++ "ret " ++ typeToLLVM retType ++ " 0\n}\n"

compileArgs :: [Arg] -> Compl (ArgsCode, InitArgsCode)
compileArgs [] = do
  return ("", "")
compileArgs [Arg pos argType ident] = do
  reg <- addVar (getCType argType) ident
  return (show (getCType argType) ++ " " ++ show reg, "")
compileArgs (arg:args) = do
  (argCode, initArgCode) <- compileArgs [arg]
  (argsCode, initArgsCode) <- compileArgs args
  return (argCode ++ "," ++ argsCode, initArgCode ++ initArgsCode)

compileBlock :: Block -> Compl (LLVMCode, StrDeclarations)
compileBlock (Block pos stmts) = compileStmts stmts

compileStmts :: [Stmt] -> Compl (LLVMCode, StrDeclarations)
compileStmts [] = do
  return ("", "")
compileStmts (stmt:stmts) = do
  (code1, strDeclarations1) <- compileStmt stmt
  (code2, strDeclarations2) <- compileStmts stmts
  return (code1 ++ code2, strDeclarations1 ++ strDeclarations2)

compileStmt :: Stmt -> Compl (LLVMCode, StrDeclarations)
compileStmt (Empty pos) = do
  return ("", "")
compileStmt (BStmt _ (Block _ stmts)) = do
  state <- get
  (code, strDeclarations) <- compileStmts stmts
  newState <- get
  put
    state
      { sStore = sStore newState
      , sRegister = sRegister newState
      , sLabel = sLabel newState
      }
  return (code, strDeclarations)
compileStmt (Decl pos varType items) = initVar (getCType varType) items
compileStmt (Ass pos ident expr) = do
  (val, code, _, strDeclarations) <- complieExpression expr
  setVarVal ident val
  return (code, strDeclarations)
compileStmt (Incr pos ident) =
  compileStmt
    (Ass pos ident (EAdd pos (EVar pos ident) (Plus pos) (ELitInt pos 1)))
compileStmt (Decr pos ident) =
  compileStmt
    (Ass pos ident (EAdd pos (EVar pos ident) (Minus pos) (ELitInt pos 1)))
compileStmt (Ret pos expr) = do
  (val, code, exprType, strDeclarations) <- complieExpression expr
  case val of
    (IntV exprVal) ->
      return (code ++ "ret i32 " ++ show exprVal ++ "\n", strDeclarations)
    (RegV exprReg) ->
      return (code ++ show (RetI exprType exprReg), strDeclarations)
    (BoolV boolVal) ->
      return
        (code ++ "ret i1 " ++ show (BoolV boolVal) ++ "\n", strDeclarations)
compileStmt (VRet _) = return (show VRetI, "")
compileStmt (Cond _ (ELitTrue _) stmt) = compileStmt stmt
compileStmt (Cond _ (ELitFalse _) stmt) = return ("", "")
compileStmt (Cond pos expr stmt) =
  compileStmt (CondElse pos expr stmt (Empty pos)) --TODO: Optymalizacja
compileStmt (CondElse _ (ELitTrue _) stmt1 stmt2) = compileStmt stmt1
compileStmt (CondElse _ (ELitFalse _) stmt1 stmt2) = compileStmt stmt2
compileStmt (CondElse _ expr stmt1 stmt2) = do
  (exprResult, exprCode, exprType, strDeclarations1) <- complieExpression expr
  prevState <- get
  (stmt1Res, strDeclarations2) <- compileStmt stmt1
  stateAfterTrueBlock <- get
  put stateAfterTrueBlock {sStore = sStore prevState}
  (stmt2Res, strDeclarations3) <- compileStmt stmt2
  stateAfterFalseBlock <- get
  put stateAfterFalseBlock {sStore = sStore prevState}
  labBase <- useLabel
  labTrue <- useLabel
  endTrue <- useLabel
  labFalse <- useLabel
  endFalse <- useLabel
  labEnd <- useLabel
  resultCode <-
    generatePhi
      (sStore prevState)
      (sStore stateAfterTrueBlock)
      (sStore stateAfterFalseBlock)
      endTrue
      endFalse
  return
    ( exprCode ++
      show
        (IfElseI
           exprResult
           labBase
           labTrue
           labFalse
           labEnd
           stmt1Res
           stmt2Res
           endTrue
           endFalse) ++
      resultCode
    , strDeclarations1 ++ strDeclarations2 ++ strDeclarations3)
compileStmt (While pos expr stmt) = do
  prevState <- get
  newRegisters
  updatedState <- get
  (exprResult, exprCode, exprType, strDeclarations1) <- complieExpression expr
  (stmt1Res, strDeclarations) <- compileStmt stmt
  stateAfterBodyCompl <- get
  labBase <- useLabel
  labCond <- useLabel
  labBody <- useLabel
  endBody <- useLabel
  labEnd <- useLabel
  condPhi <-
    generate3Phi
      (sStore updatedState)
      (sStore prevState)
      (sStore stateAfterBodyCompl)
      labBase
      endBody
  let result =
        show (JmpI labBase) ++
        show labBase ++
        ":\n" ++
        show (JmpI labCond) ++
        show labCond ++
        ":\n" ++
        condPhi ++
        exprCode ++
        show (BrI exprResult labBody labEnd) ++
        show labBody ++
        ":\n" ++
        stmt1Res ++
        show (JmpI endBody) ++
        show endBody ++
        ":\n" ++
        show (JmpI labCond) ++ show (JmpI labEnd) ++ show labEnd ++ ":\n"
  return (result, strDeclarations)
compileStmt (SExp pos expr) = do
  (_, code, _, strDeclarations) <- complieExpression expr
  return (code, strDeclarations)

initVar :: CType -> [Item] -> Compl (LLVMCode, StrDeclarations)
initVar varType [] = do
  return ("", "")
initVar CStr ((NoInit pos ident):items) =
  initVar CStr ((Init pos ident (EString pos "")) : items)
initVar CInt ((NoInit pos ident):items) =
  initVar CInt ((Init pos ident (ELitInt pos 0)) : items)
initVar CBool ((NoInit pos ident):items) =
  initVar CBool ((Init pos ident (ELitFalse pos)) : items)
initVar varType ((Init pos ident expr):items) = do
  (val, code, _, strDeclarations1) <- complieExpression expr
  addVar varType ident
  setVarVal ident val
  (codes, strDeclarations2) <- initVar varType items
  return (code ++ codes, strDeclarations1 ++ strDeclarations2)

complieExpression :: Expr -> Compl ExpressionResult
complieExpression (EAdd pos e1 (Plus posOp) e2) =
  compileBinaryExpression e1 e2 AddOp
complieExpression (EAdd pos e1 (Minus posOp) e2) =
  compileBinaryExpression e1 e2 SubOp
complieExpression (EMul pos e1 (Times posOp) e2) =
  compileBinaryExpression e1 e2 MulOp
complieExpression (EMul pos e1 (Div posOp) e2) =
  compileBinaryExpression e1 e2 DivOp
complieExpression (EMul pos e1 (Mod posOp) e2) =
  compileBinaryExpression e1 e2 ModOp
complieExpression (ERel pos e1 op e2) = complieCmpExpression e1 e2 op
complieExpression (ELitTrue pos) = return (BoolV True, "", CBool, "")
complieExpression (ELitFalse pos) = return (BoolV False, "", CBool, "")
complieExpression (ELitInt pos num) = return (IntV num, "", CInt, "")
complieExpression (EVar pos ident) = do
  (vtype, val) <- getVar ident
  return (val, "", vtype, "")
complieExpression (EApp pos (Ident name) exprs) = do
  (argStr, compileStr, strDeclarations) <- compileArgsExpr exprs
  (retType, argsTypes) <- getProc $ Ident name
  reg <- useNewReg
  case retType of
    CVoid ->
      return
        ( RegV reg
        , compileStr ++ "call void @" ++ name ++ "(" ++ argStr ++ ")\n"
        , CVoid
        , strDeclarations)
    _ ->
      return
        ( RegV reg
        , compileStr ++
          show reg ++
          " = call " ++ show retType ++ " @" ++ name ++ "(" ++ argStr ++ ")\n"
        , retType
        , strDeclarations)
complieExpression (EString pos str) = do
  reg <- useNewReg
  let (Reg num) = reg
  let len = length str + 1
  let asignCode =
        show reg ++
        " = bitcast [" ++ show len ++ " x i8]* @s" ++ show num ++ " to i8*\n"
  let strDeclarations =
        "@s" ++
        show num ++
        " = private constant [" ++
        show len ++ " x i8] c\"" ++ prepString str ++ "\\00\"\n"
  return (RegV reg, asignCode, CStr, strDeclarations)
complieExpression (Neg pos expr) =
  complieExpression (EAdd pos (ELitInt pos 0) (Minus pos) expr)
complieExpression (Not pos expr) = do
  (exprResult, code, ctype, strDeclarations) <- complieExpression expr
  reg <- useNewReg
  case exprResult of
    BoolV False -> do
      return (BoolV True, code, CBool, strDeclarations)
    BoolV True -> do
      return (BoolV False, code, CBool, strDeclarations)
    IntV exprVal -> do
      return (IntV exprVal, code, CBool, strDeclarations)
    RegV exprReg -> do
      return
        ( RegV reg
        , code ++ show (BoolI reg XorOp (IntV 1) (RegV exprReg))
        , CBool
        , strDeclarations)
complieExpression (EAnd pos e1 e2) = complieAndOr "and" pos e1 e2
complieExpression (EOr pos e1 e2) = complieAndOr "or" pos e1 e2

complieAndOr :: String -> Pos -> Expr -> Expr -> Compl ExpressionResult
complieAndOr f pos e1 e2 = do
  (Reg num) <- useNewReg
  let ident = Ident $ "log_op" ++ show num
  (varText, sd1) <- initVar CBool [Init pos ident (ELitTrue pos)]
  (setVarToE1Code, sd2) <- compileStmt (Ass pos ident e1)
  (code, sd) <-
    compileStmt
      (if f == "or" --type insted of string?
         then (Cond pos (Not pos (EVar pos ident)) (Ass pos ident e2))
         else (Cond pos (EVar pos ident) (Ass pos ident e2)))
  (_, resVal) <- getVar ident
  return (resVal, varText ++ setVarToE1Code ++ code, CBool, sd1 ++ sd2 ++ sd)

compileArgsExpr :: [Expr] -> Compl (String, String, String)
compileArgsExpr [] = return ("", "", "")
compileArgsExpr [expr] = do
  (exprRes, exprCode, ctype, strDeclarations) <- complieExpression expr
  return (show ctype ++ " " ++ show exprRes, exprCode, strDeclarations)
compileArgsExpr (expr:exprs) = do
  (exprRes, exprCode, ctype, strDeclarations1) <- complieExpression expr
  (argStr, argsCode, strDeclarations2) <- compileArgsExpr exprs
  return
    ( show ctype ++ " " ++ show exprRes ++ "," ++ argStr
    , exprCode ++ argsCode
    , strDeclarations1 ++ strDeclarations2)

{- Returns specified function application expresion
    Params:
      ident - function identificator
      argumentExpresions
-}
functionApplicationExpresion :: Ident -> [Expr] -> Expr
functionApplicationExpresion ident argumentExpresions =
  EApp (Just (0, 0)) ident argumentExpresions

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
      (result, code3, _, stringsDeclarations3) <-
        complieExpression $
        functionApplicationExpresion (Ident "concat") [e1, e2]
      return
        ( result
        , code1 ++ code2 ++ code3
        , CStr
        , stringsDeclarations1 ++ stringsDeclarations2 ++ stringsDeclarations3)
    _ -> do
      resultRegister <- useNewReg
      let instruction = show (ArtI resultRegister operator result1 result2)
      return
        ( RegV resultRegister
        , code1 ++ code2 ++ instruction
        , type1
        , stringsDeclarations1 ++ stringsDeclarations2)

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
  return
    ( RegV resultRegister
    , code1 ++
      code2 ++
      show (CompareInstruction resultRegister operator type1 result1 result2)
    , CBool
    , stringsDeclarations1 ++ stringsDeclarations2)
