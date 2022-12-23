module Compiler where

import           Control.Monad.Except
import Control.Monad.State
    ( MonadState(put, get), StateT(runStateT) )
import           Data.List
import           Data.Map                      as Map
import           Env
import           GHC.RTS.Flags                  ( TraceFlags(user) )
import           Instructions
import           Latte.Abs
import           Numeric
import           Types


import           Distribution.ParseUtils        ( field )
import           Utils


type LLVMCode = String

type ArgsCode = String

type InitArgsCode = String

compileProgram :: Program -> IO (Either Error String)
compileProgram program = do
  result <- runStateT (runExceptT (compileTopDefs program)) initEnv
  case fst result of
    (Left  error) -> return $ Left error
    (Right code ) -> return $ Right (builtinFuncDeclarations ++ code)

compileTopDefs :: Program -> Compl LLVMCode
compileTopDefs (Program _ defs) = do
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

itemStr :: [StructItem] -> Compl String
itemStr [] = do
  return ""
itemStr [SItem _ atype (Ident name)] = do
  return $ show (getCType atype)
itemStr (item : items) = do
  r    <- itemStr [item]
  rest <- itemStr items
  return $ r ++ ",\n" ++ rest

compileFuncDef :: TopDef -> Compl LLVMCode
compileFuncDef (SDef __ (Ident name) items) = do
  itemsS <- itemStr items
  return ("%" ++ name ++ " = type {\n" ++ tab itemsS ++ "\n}\n") --TODO
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
    CClass (Ident name) fields ->
      return $ blockCore ++ ";TODO \n ret %" ++ name ++ "* null \n}\n"
    _ -> return $ blockCore ++ show (RetDummyI ctype) ++ "}\n"

compileArgs :: [Arg] -> Compl (ArgsCode, InitArgsCode)
compileArgs [] = do
  return ("", "")
compileArgs [Arg __ argType ident] = do
  reg      <- useNewReg
  initCode <- initVar (getCType argType) [NoInit __ ident]
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
compileBlock (Block __ stmts) = compileStmts stmts

compileStmts :: [Stmt] -> Compl LLVMCode
compileStmts []             = return ""
compileStmts (stmt : stmts) = do
  code1 <- compileStmt stmt
  code2 <- compileStmts stmts
  return (code1 ++ code2)

compileStmt :: Stmt -> Compl LLVMCode
compileStmt (Empty __               ) = return ""
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
compileStmt (Decl __ varType        items) = initVar (getCType varType) items
compileStmt (Ass  __ (LVar p ident) expr ) = do
  (exprReg, exprCode, _) <- compileExpr expr
  (varType, var)         <- getVar ident
  return
    (  "\n;--- "
    ++ show ident
    ++ " = "
    ++ show expr
    ++ " ---\n"
    ++ exprCode
    ++ show (SetV var varType exprReg)
    ++ ";--- End of assignment --\n\n"
    )
compileStmt (Ass __ (LSField p2 expr2 ident) expr) = do
  (exprReg , exprCode , (CClass classIdent fields)) <- compileExpr expr2
  (exprReg2, exprCode2, vtype                     ) <- compileExpr expr

  (CClass _ fields) <- getClass classIdent
  let (fieldType, fieldNum) = getFieldNum fields ident

  reg <- useNewReg
  return
    (  ";--- Assigning to obj.field ---\n"
    ++ exprCode
    ++ exprCode2
    ++ show (SetFieldI reg classIdent exprReg fieldNum exprReg2 fieldType)
    ++ "\n;--- End assigning to obj.field ---\n\n"
    )
compileStmt (Incr __ ident) = compileStmt
  (Ass __
       (LVar __ ident)
       (EAdd __ (EVar __ (LVar __ ident)) (Plus __) (ELitInt __ 1))
  )
compileStmt (Decr __ ident) = compileStmt
  (Ass __
       (LVar __ ident)
       (EAdd __ (EVar __ (LVar __ ident)) (Minus __) (ELitInt __ 1))
  )
compileStmt (Ret __ expr) = do
  (val, code, exprType) <- compileExpr expr
  case val of
    (IntV exprVal) -> return (code ++ "ret i32 " ++ show exprVal ++ "\n")
    (RegV exprReg) -> return (code ++ show (RetI exprType (RegV exprReg)))
    (VarV v      ) -> return (code ++ show (RetI exprType (VarV v)))
    (BoolV boolVal) ->
      return (code ++ "ret i1 " ++ show (BoolV boolVal) ++ "\n")
    VoidV       -> return ""
    NullV ctype -> return $ "ret " ++ show ctype ++ " null\n"
compileStmt (VRet _                   ) = return (show VRetI)
compileStmt (Cond _ (ELitTrue  _) stmt) = compileStmt stmt
compileStmt (Cond _ (ELitFalse _) stmt) = return ""
compileStmt (Cond __ expr stmt) =
  compileStmt (CondElse __ expr stmt (Empty __)) --TODO: Optymalizacja
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
compileStmt (While __ expr stmt) = do
  (exprReg, exprCode, exprType) <- compileExpr expr
  stmtRes                       <- compileStmt stmt
  labCheck                      <- useLabel
  labTrue                       <- useLabel
  labEnd                        <- useLabel
  return (show (WhileI exprReg exprCode labCheck labTrue labEnd (tab stmtRes)))
compileStmt (SExp __ expr) = do
  (_, code, _) <- compileExpr expr
  return code

allocObj :: Ident -> Ident -> Compl LLVMCode
allocObj classIdent varIdent = do
  classType <- getClass classIdent

  newVar    <- addVar classType varIdent

  (Reg n)   <- useNewReg
  let varIdent = "_tmp" ++ show n


  let declCode = show (AddClassI varIdent newVar classType)
  return (declCode)


initVar :: CType -> [Item] -> Compl LLVMCode
initVar varType [] = return ""
initVar CStr ((NoInit p i) : is) = initVar CStr (Init p i (EString p "") : is)
initVar CInt ((NoInit p i) : is) = initVar CInt (Init p i (ELitInt p 0) : is)
initVar CBool ((NoInit p i) : is) = initVar CBool (Init p i (ELitFalse p) : is)
initVar (CClass classIdent _) ((NoInit __ ident) : items) = do
  classType <- getClass classIdent

  newVar    <- addVar classType ident

  varCode   <- initVar classType items

  let declCode = show (AddNullI newVar classType)
  return (varCode ++ declCode)

initVar varType ((NoInit __ ident) : items) = do
  newVar  <- addVar varType ident
  varCode <- initVar varType items
  let declCode = show (AddV newVar varType)
  case varType of
    CStr -> return (varCode ++ declCode)
    _    -> return (varCode ++ declCode ++ show (InitI newVar varType) ++ "\n")

initVar (CClass classIdent _) ((Init __ ident expr) : items) = do
  (exprReg, exprCode, _) <- compileExpr expr


  classType              <- getClass classIdent

  newVar                 <- addVar classType ident

  varCode                <- initVar classType items

  let declCode = show (AddNullI newVar classType)

  let initCode = exprCode ++ show (SetV newVar classType exprReg)

  return (varCode ++ declCode ++ initCode)

initVar varType ((Init __ ident expr) : items) = do
  (exprReg, exprCode, _) <- compileExpr expr

  newVar                 <- addVar varType ident
  varsCode               <- initVar varType items
  let declCode = show (AddV newVar varType)

  let initCode = exprCode ++ show (SetV newVar varType exprReg)
  case varType of
    CStr -> return (varsCode ++ declCode ++ initCode)
    _ ->
      return
        (varsCode ++ declCode ++ show (InitI newVar varType) ++ initCode ++ "\n"
        )

------------------------------------------- Expressions ---------------------------------------------

type ExprResult = (Val, LLVMCode, CType)

compileExpr :: Expr -> Compl ExprResult
compileExpr (ENull __ ident) = do
  (ctype, fields) <- getProc ident
  return (NullV ctype, "", ctype)--TODO
compileExpr (EStruct __ ident) = do
  (ctype, fields) <- getProc ident
  let (CClass (Ident name) fields) = ctype

  -- var <- lastVar
  -- newVar <- addVar ctype ident

  Reg r1   <- useNewReg
  code     <- allocObj ident (Ident (show r1))

  (_, var) <- getVar (Ident (show r1))
  res      <- useNewReg

  let code2 =
        show res
          ++ " = load %"
          ++ name
          ++ "*, %"
          ++ name
          ++ "** "
          ++ show var
          ++ "\n"

  initCode <- initStructFields (Ident (show r1)) fields

  return
    ( RegV res
    , "\n;INIT NEW\n" ++ code ++ "\n;-END-\n\n" ++ code2 ++ initCode
    , (CClass (Ident name) fields)
    )--TODO
compileExpr (EAdd __ e1 (Plus  __Op) e2) = compileBinExpr e1 AddOp e2
compileExpr (EAdd __ e1 (Minus __Op) e2) = compileBinExpr e1 SubOp e2
compileExpr (EMul __ e1 (Times __Op) e2) = compileBinExpr e1 MulOp e2
compileExpr (EMul __ e1 (Div   __Op) e2) = compileBinExpr e1 DivOp e2
compileExpr (EMul __ e1 (Mod   __Op) e2) = compileBinExpr e1 ModOp e2
compileExpr (ERel __ e1 op           e2) = compileCmpExpr e1 e2 op
compileExpr (ELitTrue __               ) = do
  reg <- useNewReg
  return (RegV reg, show reg ++ " = " ++ "or i1 1,1" ++ "\n", CBool)
compileExpr (ELitFalse __) = do
  reg <- useNewReg
  return (RegV reg, show reg ++ " = " ++ "or i1 0,0" ++ "\n", CBool)
compileExpr (ELitInt __ num) = do
  reg <- useNewReg
  return
    ( RegV reg
    , show reg ++ " = " ++ "or" ++ " i32 " ++ "0," ++ show num ++ "\n"
    , CInt
    )
compileExpr (EVar __ (LVar p2 ident)) = do
  (vtype, var) <- getVar ident
  case vtype of
    _ -> do
      reg <- useNewReg
      return (RegV reg, show (GetV var vtype reg), vtype)

compileExpr (EVar __ (LSField p2 (EVar _ (LVar _ objIdent)) fieldIdent)) = do
  let objExpr = EVar __ (LVar __ objIdent)
  (exprResult, code, _) <- compileExpr objExpr
  (ctype, var)          <- getVar objIdent
  let (CClass (Ident name) fields) = ctype
  state <- get
  let (ctype, fieldNum) = getFieldNum fields fieldIdent

  reg <- useNewReg
  let fieldCode =
        show reg
          ++ " = getelementptr %"
          ++ name
          ++ ", %"
          ++ name
          ++ "* "
          ++ show exprResult
          ++ ", i32 0, i32 "
          ++ show fieldNum
          ++ "\n"

  reg2 <- useNewReg
  let accesCode =
        show reg2
          ++ " = load "
          ++ show ctype
          ++ ", "
          ++ show ctype
          ++ "* "
          ++ show reg
          ++ "\n"

  return
    ( RegV reg2
    , "\n;--- Get "
    ++ name
    ++ "."
    ++ identString fieldIdent
    ++ "---\n"
    ++ code
    ++ fieldCode
    ++ accesCode
    ++ ";--- End of get field ---\n\n"
    , ctype
    )--TODO
compileExpr (EVar __ (LSField p2 obj fieldIdent)) = do --TODO
  (result1, code1, type1) <- compileExpr obj
  let (CClass i f) = type1
  ctype <- getClass i
  let (CClass (Ident name) fields) = ctype

  state <- get
  let (ctype, fieldNum) = getFieldNum fields fieldIdent

  reg <- useNewReg
  let fieldCode =
        show reg
          ++ " = getelementptr %"
          ++ name
          ++ ", %"
          ++ name
          ++ "* "
          ++ show result1
          ++ ", i32 0, i32 "
          ++ show fieldNum
          ++ "\n"

  reg2 <- useNewReg
  let accesCode =
        show reg2
          ++ " = load "
          ++ show ctype
          ++ ", "
          ++ show ctype
          ++ "* "
          ++ show reg
          ++ "\n"

  return
    ( RegV reg2
    , "\n;--- Get "
    ++ name
    ++ "."
    ++ identString fieldIdent
    ++ "---\n"
    ++ code1
    ++ fieldCode
    ++ accesCode
    ++ ";--- End of get field ---\n\n"
    , ctype
    )
compileExpr (EApp __ (Ident name) exprs) = do
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
compileExpr (EString __ str) = do
  reg <- useNewReg
  let (Reg num) = reg
  let len       = length str + 1
  let asignCode = show (CastStrI reg len num)
  addString $ show (ConstI num len str)
  return (RegV reg, asignCode, CStr)
compileExpr (Neg __ expr) =
  compileExpr (EAdd __ (ELitInt __ 0) (Minus __) expr)
compileExpr (EAnd _ e1 e2) = compileAndOr e1 LAnd e2
compileExpr (EOr  _ e1 e2) = compileAndOr e1 LOr e2
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

{- initialize object.fields with default values
    Params:
      object's ident
      object's fields
    Returns:
      initialization string
-}
initStructFields :: Ident -> [(CType, Ident)] -> Compl String
initStructFields objIdent []                             = return ""
initStructFields objIdent ((fieldType, fieldIdent) : fields) = do
  let lvalue = LSField __ (EVar __ (LVar __ objIdent)) fieldIdent
  results <- initStructFields objIdent fields
  result  <- initStructField fieldType lvalue
  return $ result ++ results

{- initialize object.field with default value
    Params:
      field's type
      lvalue (obj.field)
    Returns:
      initialization string
-}
initStructField :: CType -> LValue -> Compl String
initStructField CInt  lv = compileStmt (Ass __ lv (ELitInt __ 0))
initStructField CBool lv = compileStmt (Ass __ lv (ELitFalse __))
initStructField (CClass classI _) lv =
  compileStmt (Ass __ lv (ENull __ classI))
initStructField CStr       lv = compileStmt (Ass __ lv (EString __ ""))
initStructField CVoid      lv = return ""
initStructField (CFun _ _) lv = return ""

{- compile arguments of EApp
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

{- compile binary expression
    Params:
      expression1
      expression2
      comparision operator
-}
compileBinExpr :: Expr -> ArtOp -> Expr -> Compl ExprResult
compileBinExpr e1 operator e2 = do

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

{- compile comparision expresion
    Params:
      expression1 - compared expresion
      expression2 - compared expresion
 -}
compileCmpExpr :: Expr -> Expr -> RelOp -> Compl ExprResult
compileCmpExpr e1 e2 operator = do
  (result1, code1, type1) <- compileExpr e1
  (result2, code2, type2) <- compileExpr e2
  resultRegister          <- useNewReg
  return
    ( RegV resultRegister
    , code1 ++ code2 ++ show
      (CompareInstruction resultRegister operator type1 result1 result2)
    , CBool
    )

{- compile and/or expresion
    Params:
      Operator string
      expression1
      expression2
-}
compileAndOr :: Expr -> LogicalOperator -> Expr -> Compl ExprResult
compileAndOr e1 operator e2 = do
  let __ = Just (0, 0)
  ident          <- logicalCmpVar
  initVarCode    <- initVar CBool [Init __ ident (ELitTrue __)]
  setVarToE1Code <- compileStmt (Ass __ (LVar __ ident) e1)
  setVarToE2Code <- compileStmt
    (if operator == LOr
      then Cond __
                (Not __ (EVar __ (LVar __ ident)))
                (Ass __ (LVar __ ident) e2)
      else Cond __ (EVar __ (LVar __ ident)) (Ass __ (LVar __ ident) e2)
    )
  (v, code, _) <- compileExpr (EVar __ (LVar __ ident))
  return (v, initVarCode ++ setVarToE1Code ++ setVarToE2Code ++ code, CBool)
