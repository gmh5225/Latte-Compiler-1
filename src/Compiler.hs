module Compiler where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map                      as Map
import           Env
import           Env
import           GHC.RTS.Flags                  ( TraceFlags(user) )
import           Instructions
import           Instructions
import           Latte.Abs
import           Latte.Abs
import           Numeric
import           Types
import           Types

import           Utils


type LLVMCode = String

type StrDeclarations = String

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
  compileFuncDefs defs

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
  prevState                    <- get
  (argsCode , initArgsCode   ) <- compileArgs args
  (blockCode, strDeclarations) <- compileBlock block
  newState                     <- get
  -- TODO:
  put newState { sPenv  = sPenv prevState
               , sVenv  = sVenv prevState
               , sStore = sStore prevState
               }
  let blockCore =
        strDeclarations
          ++ "\ndefine "
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
compileArgs [] = do
  return ("", "")
compileArgs [Arg pos argType ident] = do
  reg <- addVar (getCType argType) ident
  return (show (getCType argType) ++ " " ++ show reg, "")
compileArgs (arg : args) = do
  (argCode , initArgCode ) <- compileArgs [arg]
  (argsCode, initArgsCode) <- compileArgs args
  return (argCode ++ "," ++ argsCode, initArgCode ++ initArgsCode)

compileBlock :: Block -> Compl (LLVMCode, StrDeclarations)
compileBlock (Block pos stmts) = compileStmts stmts

compileStmts :: [Stmt] -> Compl (LLVMCode, StrDeclarations)
compileStmts [] = do
  return ("", "")
compileStmts (stmt : stmts) = do
  (code1, sd1) <- compileStmt stmt
  (code2, sd2) <- compileStmts stmts
  return (code1 ++ code2, sd1 ++ sd2)

compileStmt :: Stmt -> Compl (LLVMCode, StrDeclarations)
compileStmt (Empty pos) = do
  return ("", "")
compileStmt (BStmt _ (Block _ stmts)) = do
  state                   <- get
  (code, strDeclarations) <- compileStmts stmts
  newState                <- get
  put state { sStore    = sStore newState
            , sRegister = sRegister newState
            , sLabel    = sLabel newState
            }
  return (code, strDeclarations)
compileStmt (Decl pos varType items) = initVar (getCType varType) items
compileStmt (Ass  pos ident   expr ) = do
  (val, code, _, strDeclarations) <- complieExpr expr
  setVarVal ident val
  return (code, strDeclarations)
compileStmt (Incr pos ident) = compileStmt
  (Ass pos ident (EAdd pos (EVar pos ident) (Plus pos) (ELitInt pos 1)))
compileStmt (Decr pos ident) = compileStmt
  (Ass pos ident (EAdd pos (EVar pos ident) (Minus pos) (ELitInt pos 1)))
compileStmt (Ret pos expr) = do
  (val, code, exprType, strDeclarations) <- complieExpr expr
  case val of
    (IntV exprVal) ->
      return (code ++ "ret i32 " ++ show exprVal ++ "\n", strDeclarations)
    (RegV exprReg) ->
      return (code ++ show (RetI exprType exprReg), strDeclarations)
    (BoolV boolVal) -> return
      (code ++ "ret i1 " ++ show (BoolV boolVal) ++ "\n", strDeclarations)
    VoidV -> return ("", "")
compileStmt (VRet _                   ) = return (show VRetI, "")
compileStmt (Cond _ (ELitTrue  _) stmt) = compileStmt stmt
compileStmt (Cond _ (ELitFalse _) stmt) = return ("", "")
compileStmt (Cond pos expr stmt) =
  compileStmt (CondElse pos expr stmt (Empty pos)) --TODO: Optymalizacja
compileStmt (CondElse _ (ELitTrue  _) stmt1 stmt2) = compileStmt stmt1
compileStmt (CondElse _ (ELitFalse _) stmt1 stmt2) = compileStmt stmt2
compileStmt (CondElse _ expr          stmt1 stmt2) = do
  (exprResult, exprCode, exprType, strDeclarations1) <- complieExpr expr
  prevState                    <- get
  (stmt1Res, strDeclarations2) <- compileStmt stmt1
  stateAfterTrueBlock          <- get
  put stateAfterTrueBlock { sStore = sStore prevState }
  (stmt2Res, strDeclarations3) <- compileStmt stmt2
  stateAfterFalseBlock         <- get
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
    ( exprCode
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
    , strDeclarations1 ++ strDeclarations2 ++ strDeclarations3
    )
compileStmt (While pos expr stmt) = do
  prevState <- get
  newRegisters
  updatedState                <- get
  (exprResult, exprCode, exprType, strDeclarations1) <- complieExpr expr
  (stmt1Res, strDeclarations) <- compileStmt stmt
  stateAfterBodyCompl         <- get
  labBase                     <- useLabel
  labCond                     <- useLabel
  labBody                     <- useLabel
  endBody                     <- useLabel
  labEnd                      <- useLabel
  condPhi                     <- generate3Phi (sStore updatedState)
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
  return (result, strDeclarations)
compileStmt (SExp pos expr) = do
  (_, code, _, strDeclarations) <- complieExpr expr
  return (code, strDeclarations)

initVar :: CType -> [Item] -> Compl (LLVMCode, StrDeclarations)
initVar varType [] = return ("", "")
initVar CStr ((NoInit p i) : is) = initVar CStr (Init p i (EString p "") : is)
initVar CInt ((NoInit p i) : is) = initVar CInt (Init p i (ELitInt p 0) : is)
initVar CBool ((NoInit p i) : is) = initVar CBool (Init p i (ELitFalse p) : is)
initVar varType ((Init pos ident expr) : items) = do
  (val, code, _, sd1) <- complieExpr expr
  addVar varType ident
  setVarVal ident val
  (codes, sd2) <- initVar varType items
  return (code ++ codes, sd1 ++ sd2)
initVar other _ = return ("ERROR", "ERROR")

------------------------------------------- Expressions ---------------------------------------------

type ExprResult = (Val, LLVMCode, CType, StrDeclarations)

complieExpr :: Expr -> Compl ExprResult
complieExpr (EAdd pos e1 (Plus  posOp) e2) = complieBinExpr e1 AddOp e2
complieExpr (EAdd pos e1 (Minus posOp) e2) = complieBinExpr e1 SubOp e2
complieExpr (EMul pos e1 (Times posOp) e2) = complieBinExpr e1 MulOp e2
complieExpr (EMul pos e1 (Div   posOp) e2) = complieBinExpr e1 DivOp e2
complieExpr (EMul pos e1 (Mod   posOp) e2) = complieBinExpr e1 ModOp e2
complieExpr (ERel pos e1 op            e2) = complieCmpExpr e1 e2 op
complieExpr (ELitTrue  pos               ) = return (BoolV True, "", CBool, "")
complieExpr (ELitFalse pos               ) = return (BoolV False, "", CBool, "")
complieExpr (ELitInt pos num             ) = return (IntV num, "", CInt, "")
complieExpr (EVar    pos ident           ) = do
  (vtype, val) <- getVar ident
  return (val, "", vtype, "")
complieExpr (EApp pos (Ident name) exprs) = do
  (argStr, compileStr, strDeclarations) <- compileArgsExpr exprs
  (retType, argsTypes) <- getProc $ Ident name
  reg                  <- useNewReg
  case retType of
    CVoid -> return
      ( RegV reg
      , compileStr ++ "call void @" ++ name ++ "(" ++ argStr ++ ")\n"
      , CVoid
      , strDeclarations
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
      , strDeclarations
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
  return (RegV reg, asignCode, CStr, strDeclarations)
complieExpr (Neg p expr) = complieExpr (EAdd p (ELitInt p 0) (Minus p) expr)
complieExpr (Not _ expr) = do
  (exprResult, code, ctype, sd) <- complieExpr expr
  case exprResult of
    BoolV False   -> return (BoolV True, code, CBool, sd)
    BoolV True    -> return (BoolV False, code, CBool, sd)
    RegV  exprReg -> do
      reg <- useNewReg
      return
        ( RegV reg
        , code ++ show (BoolI reg XorOp (IntV 1) (RegV exprReg))
        , CBool
        , sd
        )
    other -> return (other, code, CBool, sd)
complieExpr (EAnd _ e1 e2) = complieAndOr e1 LAnd e2
complieExpr (EOr  _ e1 e2) = complieAndOr e1 LOr e2

{- Complie function application arguments' expression
    Params:
      Arguments' expressions
    Returns:
      Application-arguments-string
      Expressions code
      String-declarations
-}
compileArgsExpr :: [Expr] -> Compl (String, LLVMCode, String)
compileArgsExpr []     = return ("", "", "")
compileArgsExpr [expr] = do
  (exprRes, exprCode, ctype, strDeclarations) <- complieExpr expr
  return (show ctype ++ " " ++ show exprRes, exprCode, strDeclarations)
compileArgsExpr (expr : exprs) = do
  (exprRes, exprCode, ctype, strDeclarations1) <- complieExpr expr
  (argStr, argsCode, strDeclarations2)         <- compileArgsExpr exprs
  return
    ( show ctype ++ " " ++ show exprRes ++ "," ++ argStr
    , exprCode ++ argsCode
    , strDeclarations1 ++ strDeclarations2
    )

{- Complie binary expression
    Params:
      expression1
      expression2
      comparision operator
-}
complieBinExpr :: Expr -> ArtOp -> Expr -> Compl ExprResult
complieBinExpr e1 operator e2 = do
  (result1, code1, type1, sd1) <- complieExpr e1
  (result2, code2, type2, sd2) <- complieExpr e2
  case type1 of
    CStr -> do
      (result, code3, type3, sd3) <- complieExpr
        $ EApp (Just (0, 0)) (Ident "concat") [e1, e2]
      return (result, code1 ++ code2 ++ code3, CStr, sd1 ++ sd2 ++ sd3)
    _ -> do
      resultRegister <- useNewReg
      let instruction = show (ArtI resultRegister operator result1 result2)
      return
        (RegV resultRegister, code1 ++ code2 ++ instruction, type1, sd1 ++ sd2)

{- Complie comparision expresion
    Params:
      expression1 - compared expresion
      expression2 - compared expresion
 -}
complieCmpExpr :: Expr -> Expr -> RelOp -> Compl ExprResult
complieCmpExpr e1 e2 operator = do
  (result1, code1, type1, sd1) <- complieExpr e1
  (result2, code2, type2, sd2) <- complieExpr e2
  resultRegister               <- useNewReg
  return
    ( RegV resultRegister
    , code1 ++ code2 ++ show
      (CompareInstruction resultRegister operator type1 result1 result2)
    , CBool
    , sd1 ++ sd2
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
  ident                 <- logicalCmpVar
  (initVarCode   , sd1) <- initVar CBool [Init pos ident (ELitTrue pos)]
  (setVarToE1Code, sd2) <- compileStmt (Ass pos ident e1)
  (setVarToE2Code, sd ) <- compileStmt
    (if operator == LOr
      then Cond pos (Not pos (EVar pos ident)) (Ass pos ident e2)
      else Cond pos (EVar pos ident) (Ass pos ident e2)
    )
  (_, resVal) <- getVar ident
  return
    ( resVal
    , initVarCode ++ setVarToE1Code ++ setVarToE2Code
    , CBool
    , sd1 ++ sd2 ++ sd
    )
