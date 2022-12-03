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
    (Right code ) -> return $ Right (funcDeclarations ++ code)

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
        -- strDeclarations ++
        "\ndefine "
          ++ typeToLLVM retType
          ++ " @"
          ++ name
          ++ "("
          ++ argsCode
          ++ ") {\n"
          ++ initArgsCode
          ++ "\n"
          ++ blockCode
  case retType of
    Void _ -> return $ blockCore ++ "ret void\n}\n"
    Str _ ->
      return $ blockCore ++ "%_ = call i8* @malloc(i32 1)\n ret i8* %_\n\n}\n"
    _ -> return $ blockCore ++ "ret " ++ typeToLLVM retType ++ " 0\n}\n"

compileArgs :: [Arg] -> Compl (ArgsCode, InitArgsCode)
compileArgs []                      = return ("", "")
compileArgs [Arg pos argType ident] = do
  reg <- addVar (getCType argType) ident
  return (show (getCType argType) ++ " " ++ show reg, "")
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
            }
  return code
compileStmt (Decl pos varType items) = initVar (getCType varType) items
compileStmt (Ass  pos ident   expr ) = do
  (val, code, _) <- complieExpr expr
  setVarVal ident val
  return code
compileStmt (Incr pos ident) = compileStmt
  (Ass pos ident (EAdd pos (EVar pos ident) (Plus pos) (ELitInt pos 1)))
compileStmt (Decr pos ident) = compileStmt
  (Ass pos ident (EAdd pos (EVar pos ident) (Minus pos) (ELitInt pos 1)))
compileStmt (Ret pos expr) = do
  (val, code, exprType) <- complieExpr expr
  case val of
    (IntV exprVal) -> return (code ++ "ret i32 " ++ show exprVal ++ "\n")
    (RegV exprReg) -> return (code ++ show (RetI exprType exprReg))
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
  (exprResult, exprCode, exprType) <- complieExpr expr
  prevState                        <- get
  stmt1Res                         <- compileStmt stmt1
  stateAfterTrueBlock              <- get
  put stateAfterTrueBlock { sStore = sStore prevState }
  stmt2Res             <- compileStmt stmt2
  stateAfterFalseBlock <- get
  put stateAfterFalseBlock { sStore = sStore prevState }
  labBase    <- useLabel
  labTrue    <- useLabel
  endTrue    <- useLabel
  labFalse   <- useLabel
  endFalse   <- useLabel
  labEnd     <- useLabel
  resultCode <- generatePhi (sStore prevState)
                            (sStore stateAfterTrueBlock)
                            (sStore stateAfterFalseBlock)
                            endTrue
                            endFalse
  return
    (  exprCode
    ++ show
         (IfElseI exprResult
                  labBase
                  labTrue
                  labFalse
                  labEnd
                  stmt1Res
                  stmt2Res
                  endTrue
                  endFalse
         )
    ++ resultCode
    )
compileStmt (While pos expr stmt) = do
  prevState <- get
  newRegisters
  updatedState                     <- get
  (exprResult, exprCode, exprType) <- complieExpr expr
  stmt1Res                         <- compileStmt stmt
  stateAfterBodyCompl              <- get
  labBase                          <- useLabel
  labCond                          <- useLabel
  labBody                          <- useLabel
  endBody                          <- useLabel
  labEnd                           <- useLabel
  condPhi                          <- generate3Phi (sStore updatedState)
                                                   (sStore prevState)
                                                   (sStore stateAfterBodyCompl)
                                                   labBase
                                                   endBody
  let result =
        show (JmpI labBase)
          ++ show labBase
          ++ ":\n"
          ++ show (JmpI labCond)
          ++ show labCond
          ++ ":\n"
          ++ condPhi
          ++ exprCode
          ++ show (BrI exprResult labBody labEnd)
          ++ show labBody
          ++ ":\n"
          ++ stmt1Res
          ++ show (JmpI endBody)
          ++ show endBody
          ++ ":\n"
          ++ show (JmpI labCond)
          ++ show (JmpI labEnd)
          ++ show labEnd
          ++ ":\n"
  return result
compileStmt (SExp pos expr) = do
  (_, code, _) <- complieExpr expr
  return code

initVar :: CType -> [Item] -> Compl LLVMCode
initVar varType [] = return ""
initVar CStr ((NoInit p i) : is) = initVar CStr (Init p i (EString p "") : is)
initVar CInt ((NoInit p i) : is) = initVar CInt (Init p i (ELitInt p 0) : is)
initVar CBool ((NoInit p i) : is) = initVar CBool (Init p i (ELitFalse p) : is)
initVar varType ((Init pos ident expr) : items) = do
  (val, code, _) <- complieExpr expr
  addVar varType ident
  setVarVal ident val
  codes <- initVar varType items
  return (code ++ codes)
initVar other _ = return "ERROR"

------------------------------------------- Expressions ---------------------------------------------

type ExprResult = (Val, LLVMCode, CType)

complieExpr :: Expr -> Compl ExprResult
complieExpr (EAdd pos e1 (Plus  posOp) e2) = complieBinExpr e1 AddOp e2
complieExpr (EAdd pos e1 (Minus posOp) e2) = complieBinExpr e1 SubOp e2
complieExpr (EMul pos e1 (Times posOp) e2) = complieBinExpr e1 MulOp e2
complieExpr (EMul pos e1 (Div   posOp) e2) = complieBinExpr e1 DivOp e2
complieExpr (EMul pos e1 (Mod   posOp) e2) = complieBinExpr e1 ModOp e2
complieExpr (ERel pos e1 op            e2) = complieCmpExpr e1 e2 op
complieExpr (ELitTrue  pos               ) = return (BoolV True, "", CBool)
complieExpr (ELitFalse pos               ) = return (BoolV False, "", CBool)
complieExpr (ELitInt pos num             ) = return (IntV num, "", CInt)
complieExpr (EVar    pos ident           ) = do
  (vtype, val) <- getVar ident
  return (val, "", vtype)
complieExpr (EApp pos (Ident name) exprs) = do
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
complieExpr (EString pos str) = do
  reg <- useNewReg
  let (Reg num) = reg
  let len       = length str + 1
  let asignCode =
        show reg
          ++ " = bitcast ["
          ++ show len
          ++ " x i8]* @s"
          ++ show num
          ++ " to i8*\n"
  let strDeclarations =
        "@s"
          ++ show num
          ++ " = private constant ["
          ++ show len
          ++ " x i8] c\""
          ++ prepString str
          ++ "\\00\"\n"
  addString strDeclarations
  return (RegV reg, asignCode, CStr)
complieExpr (Neg p expr) = complieExpr (EAdd p (ELitInt p 0) (Minus p) expr)
complieExpr (Not _ expr) = do
  (exprResult, code, ctype) <- complieExpr expr
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
complieExpr (EAnd _ e1 e2) = complieAndOr e1 LAnd e2
complieExpr (EOr  _ e1 e2) = complieAndOr e1 LOr e2

{- Complie function application arguments' expression
    Params:
      Arguments' expressions
    Returns:
      Application-arguments-string
      Expressions code
-}
compileArgsExpr :: [Expr] -> Compl (String, LLVMCode)
compileArgsExpr []     = return ("", "")
compileArgsExpr [expr] = do
  (exprRes, exprCode, ctype) <- complieExpr expr
  return (show ctype ++ " " ++ show exprRes, exprCode)
compileArgsExpr (expr : exprs) = do
  (exprRes, exprCode, ctype) <- complieExpr expr
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
  (_, _, exprType) <- complieExpr e1
  put state

  case exprType of
    CStr -> do
      (result, code, _) <- complieExpr
        $ EApp (Just (0, 0)) (Ident "concat") [e1, e2]
      return (result, code, CStr)
    _ -> do
      (result1, code1, type1) <- complieExpr e1
      (result2, code2, type2) <- complieExpr e2
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
  (result1, code1, type1) <- complieExpr e1
  (result2, code2, type2) <- complieExpr e2
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
  (_, resVal) <- getVar ident
  return (resVal, initVarCode ++ setVarToE1Code ++ setVarToE2Code, CBool)
