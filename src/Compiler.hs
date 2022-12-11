module Compiler where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.List
import           Data.Map                      as Map
import           Env
import           GHC.RTS.Flags                  ( TraceFlags(user) )
import           Instructions
import           Latte.Abs
import           Numeric
import           Types


import           Utils


type LLVMCode = String

type ArgsCode = String

type InitArgsCode = String

compileProgram :: Program -> IO (Either Error String)
compileProgram program = do
  result <- runStateT (runExceptT (complieTopDefs program)) initEnv
  case fst result of
    (Left  error) -> return $ Left error
    (Right code ) -> return $ Right (builtinFuncDeclarations ++ code)

complieTopDefs :: Program -> Compl LLVMCode
complieTopDefs (Program _ defs) = do
  addFuncDefinition defs
  code  <- compileFuncDefs defs
  state <- get
  let strDeclarations = intercalate "\n" (sStrs state)
  return $ strDeclarations ++ code

addFuncDefinition :: [TopDef] -> Compl ()
addFuncDefinition []           = return ()
addFuncDefinition (def : defs) = do
  addFunc def
  addFuncDefinition defs

compileFuncDefs :: [TopDef] -> Compl LLVMCode
compileFuncDefs []           = return ""
compileFuncDefs (def : defs) = do
  code1 <- compileFuncDef def
  code2 <- compileFuncDefs defs
  return (code1 ++ code2)

compileFuncDef :: TopDef -> Compl LLVMCode
compileFuncDef (FnDef _ retType (Ident name) args block) = do
  let ctype = getCType retType
  prevState                <- get
  (argsCode, initArgsCode) <- compileArgs args
  blockCode                <- compileBlock block
  newState                 <- get
  -- TODO:
  put newState { sPenv  = sPenv prevState
               , sVenv  = sVenv prevState
               , sStore = sStore prevState
               }
  let blockCore =
        "\ndefine "
          ++ show ctype
          ++ " @"
          ++ name
          ++ "("
          ++ argsCode
          ++ ") {\n"
          ++ initArgsCode
          ++ "\n"
          ++ blockCode

  case ctype of
    CVoid -> return $ blockCore ++ show RetVoidI ++ "}\n"
    CStr  -> return $ blockCore ++ show RetDummyStrI ++ "}\n"
    _     -> return $ blockCore ++ show (RetDummyI ctype) ++ "}\n"

compileArgs :: [Arg] -> Compl (ArgsCode, InitArgsCode)
compileArgs [] = do
  return ("", "")
compileArgs [Arg pos argType ident] = do
  reg      <- useNewReg
  initCode <- initVar (getCType argType) [NoInit pos ident]
  var      <- lastVar
  return
    ( show (getCType argType) ++ " " ++ show reg
    , initCode ++ show (SetV var (getCType argType) (RegV reg))
    )
compileArgs (arg : args) = do
  (argCode , initArgCode ) <- compileArgs [arg]
  (argsCode, initArgsCode) <- compileArgs args
  return (argCode ++ "," ++ argsCode, initArgCode ++ initArgsCode)

compileBlock :: Block -> Compl LLVMCode
compileBlock (Block pos stmts) = compileStmts stmts

compileStmts :: [Stmt] -> Compl LLVMCode
compileStmts []             = return ""
compileStmts (stmt : stmts) = do
  code1 <- compileStmt stmt
  code2 <- compileStmts stmts
  return (code1 ++ code2)

compileStmt :: Stmt -> Compl LLVMCode
compileStmt (Empty pos              ) = return ""
compileStmt (BStmt _ (Block _ stmts)) = do
  state    <- get
  code     <- compileStmts stmts
  newState <- get
  put state { sStore    = sStore newState
            , sRegister = sRegister newState
            , sLabel    = sLabel newState
            , sStrs     = sStrs newState
            , sVar      = sVar newState
            }
  return code
compileStmt (Decl pos varType items) = initVar (getCType varType) items
compileStmt (Ass  pos ident   expr ) = do
  (exprReg, exprCode, _) <- compileExpr expr
  (varType, var)    <- getVar ident
  return (exprCode ++ show (SetV var varType exprReg))
compileStmt (Incr pos ident) = compileStmt
  (Ass pos ident (EAdd pos (EVar pos ident) (Plus pos) (ELitInt pos 1)))
compileStmt (Decr pos ident) = compileStmt
  (Ass pos ident (EAdd pos (EVar pos ident) (Minus pos) (ELitInt pos 1)))
compileStmt (Ret pos expr) = do
  (val, code, exprType) <- compileExpr expr
  case val of
    (IntV exprVal) -> return (code ++ "ret i32 " ++ show exprVal ++ "\n")
    (RegV exprReg) -> return (code ++ show (RetI exprType (RegV exprReg)))
    (VarV v      ) -> return (code ++ show (RetI exprType (VarV v)))
    (BoolV boolVal) ->
      return (code ++ "ret i1 " ++ show (BoolV boolVal) ++ "\n")
    VoidV -> return ""
compileStmt (VRet _                   ) = return (show VRetI)
compileStmt (Cond _ (ELitTrue  _) stmt) = compileStmt stmt
compileStmt (Cond _ (ELitFalse _) stmt) = return ""
compileStmt (Cond pos expr stmt) =
  compileStmt (CondElse pos expr stmt (Empty pos)) --TODO: Optymalizacja
compileStmt (CondElse _ (ELitTrue  _) stmt1 stmt2) = compileStmt stmt1
compileStmt (CondElse _ (ELitFalse _) stmt1 stmt2) = compileStmt stmt2
compileStmt (CondElse _ expr          stmt1 stmt2) = do
  (exprReg, exprCode, exprType) <- compileExpr expr
  stmt1Res                      <- compileStmt stmt1
  stmt2Res                      <- compileStmt stmt2
  labTrue                       <- useLabel
  labFalse                      <- useLabel
  labEnd                        <- useLabel
  return
    (exprCode ++ show
      (IfElseI exprReg labTrue labFalse labEnd (tab stmt1Res) (tab stmt2Res))
    )
compileStmt (While pos expr stmt) = do
  (exprReg, exprCode, exprType) <- compileExpr expr
  stmtRes                       <- compileStmt stmt
  labCheck                      <- useLabel
  labTrue                       <- useLabel
  labEnd                        <- useLabel
  return (show (WhileI exprReg exprCode labCheck labTrue labEnd (tab stmtRes)))
compileStmt (SExp pos expr) = do
  (_, code, _) <- compileExpr expr
  return code

initVar :: CType -> [Item] -> Compl LLVMCode
initVar varType [] = return ""
initVar CStr ((NoInit p i) : is) = initVar CStr (Init p i (EString p "") : is)
initVar CInt ((NoInit p i) : is) = initVar CInt (Init p i (ELitInt p 0) : is)
initVar CBool ((NoInit p i) : is) = initVar CBool (Init p i (ELitFalse p) : is)
initVar varType ((NoInit pos ident) : items) = do
  newVar    <- addVar varType ident
  (varCode) <- initVar varType items
  let declCode = show (AddV newVar varType)
  case varType of
    CStr -> return (varCode ++ declCode)
    _    -> return (varCode ++ declCode ++ show (InitI newVar varType) ++ "\n")
initVar varType ((Init pos ident expr) : items) = do
  (exprReg, exprCode, _) <- compileExpr expr
  newVar                 <- addVar varType ident
  let initCode = exprCode ++ show (SetV newVar varType exprReg)
  (varsCode) <- initVar varType items
  let declCode = show (AddV newVar varType)
  case varType of
    CStr -> return (varsCode ++ declCode ++ initCode)
    _ ->
      return
        (varsCode ++ declCode ++ show (InitI newVar varType) ++ initCode ++ "\n"
        )

------------------------------------------- Expressions ---------------------------------------------

type ExprResult = (Val, LLVMCode, CType)

compileExpr :: Expr -> Compl ExprResult
compileExpr (EAdd pos e1 (Plus  posOp) e2) = complieBinExpr e1 AddOp e2
compileExpr (EAdd pos e1 (Minus posOp) e2) = complieBinExpr e1 SubOp e2
compileExpr (EMul pos e1 (Times posOp) e2) = complieBinExpr e1 MulOp e2
compileExpr (EMul pos e1 (Div   posOp) e2) = complieBinExpr e1 DivOp e2
compileExpr (EMul pos e1 (Mod   posOp) e2) = complieBinExpr e1 ModOp e2
compileExpr (ERel pos e1 op            e2) = complieCmpExpr e1 e2 op
compileExpr (ELitTrue pos                ) = do
  reg <- useNewReg
  return (RegV reg, show reg ++ " = " ++ "or i1 1,1" ++ "\n", CBool)
compileExpr (ELitFalse pos) = do
  reg <- useNewReg
  return (RegV reg, show reg ++ " = " ++ "or i1 0,0" ++ "\n", CBool)
compileExpr (ELitInt pos num) = do
  reg <- useNewReg
  return
    ( RegV reg
    , show reg ++ " = " ++ "or" ++ " i32 " ++ "0," ++ show num ++ "\n"
    , CInt
    )
compileExpr (EVar pos ident) = do
  (vtype, var) <- getVar ident
  reg <- useNewReg
  return (RegV reg, show (GetV var vtype reg), vtype)
compileExpr (EApp pos (Ident name) exprs) = do
  (argStr , compileStr) <- compileArgsExpr exprs
  (retType, argsTypes ) <- getProc $ Ident name
  reg                   <- useNewReg
  case retType of
    CVoid -> return
      ( RegV reg
      , compileStr ++ "call void @" ++ name ++ "(" ++ argStr ++ ")\n"
      , CVoid
      )
    _ -> return
      ( RegV reg
      , compileStr
      ++ show reg
      ++ " = call "
      ++ show retType
      ++ " @"
      ++ name
      ++ "("
      ++ argStr
      ++ ")\n"
      , retType
      )
compileExpr (EString pos str) = do
  reg <- useNewReg
  let (Reg num) = reg
  let len       = length str + 1
  let asignCode = show (CastStrI reg len num)
  addString $ show (ConstI num len str)
  return (RegV reg, asignCode, CStr)
compileExpr (Neg pos expr) =
  compileExpr (EAdd pos (ELitInt pos 0) (Minus pos) expr)
compileExpr (EAnd _ e1 e2) = complieAndOr e1 LAnd e2
compileExpr (EOr  _ e1 e2) = complieAndOr e1 LOr e2
compileExpr (Not _ expr  ) = do
  (exprResult, code, ctype) <- compileExpr expr
  case exprResult of
    BoolV False   -> return (BoolV True, code, CBool)
    BoolV True    -> return (BoolV False, code, CBool)
    RegV  exprReg -> do
      reg <- useNewReg
      return
        ( RegV reg
        , code ++ show (BoolI reg XorOp (IntV 1) (RegV exprReg))
        , CBool
        )
    other -> return (other, code, CBool)

{- complie arguments of EApp
    Params:
      arguments' expressions
    Returns:
      arguments' string
      code
-}
compileArgsExpr :: [Expr] -> Compl (String, LLVMCode)
compileArgsExpr []     = return ("", "")
compileArgsExpr [expr] = do
  (exprRes, exprCode, ctype) <- compileExpr expr
  return (show ctype ++ " " ++ show exprRes, exprCode)
compileArgsExpr (expr : exprs) = do
  (exprRes, exprCode, ctype) <- compileExpr expr
  (argStr, argsCode)         <- compileArgsExpr exprs
  return
    (show ctype ++ " " ++ show exprRes ++ "," ++ argStr, exprCode ++ argsCode)

{- Complie binary expression
    Params:
      expression1
      expression2
      comparision operator
-}
complieBinExpr :: Expr -> ArtOp -> Expr -> Compl ExprResult
complieBinExpr e1 operator e2 = do

  state            <- get
  (_, _, exprType) <- compileExpr e1
  put state

  case exprType of
    CStr -> do
      (result, code, _) <- compileExpr
        $ EApp (Just (0, 0)) (Ident "concat") [e1, e2]
      return (result, code, CStr)
    _ -> do
      (result1, code1, type1) <- compileExpr e1
      (result2, code2, type2) <- compileExpr e2
      resultRegister          <- useNewReg
      let instruction = show (ArtI resultRegister operator result1 result2)
      return (RegV resultRegister, code1 ++ code2 ++ instruction, type1)

{- Complie comparision expresion
    Params:
      expression1 - compared expresion
      expression2 - compared expresion
 -}
complieCmpExpr :: Expr -> Expr -> RelOp -> Compl ExprResult
complieCmpExpr e1 e2 operator = do
  (result1, code1, type1) <- compileExpr e1
  (result2, code2, type2) <- compileExpr e2
  resultRegister          <- useNewReg
  return
    ( RegV resultRegister
    , code1 ++ code2 ++ show
      (CompareInstruction resultRegister operator type1 result1 result2)
    , CBool
    )

{- Complie and/or expresion
    Params:
      Operator string
      expression1
      expression2
-}
complieAndOr :: Expr -> LogicalOperator -> Expr -> Compl ExprResult
complieAndOr e1 operator e2 = do
  let pos = Just (0, 0)
  ident          <- logicalCmpVar
  initVarCode    <- initVar CBool [Init pos ident (ELitTrue pos)]
  setVarToE1Code <- compileStmt (Ass pos ident e1)
  setVarToE2Code <- compileStmt
    (if operator == LOr
      then Cond pos (Not pos (EVar pos ident)) (Ass pos ident e2)
      else Cond pos (EVar pos ident) (Ass pos ident e2)
    )
  (v, code, _) <- compileExpr (EVar pos ident)
  return (v, initVarCode ++ setVarToE1Code ++ setVarToE2Code ++ code, CBool)
