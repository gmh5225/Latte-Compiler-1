module StaticAnalysis where

import qualified Control.Monad
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map                      as Map
                                                ( Map
                                                , fromList
                                                , insert
                                                , lookup
                                                , toList
                                                )
import           Language.Haskell.TH            ( varT )
import           Latte.Abs
import           Prelude
import           Text.Parsec.Token              ( GenLanguageDef(identLetter) )
import           Text.Read.Lex                  ( expect )
import           Utils

--------------------------------------------
type Pos = BNFC'Position

data CType
  = CInt
  | CStr
  | CBool
  | CVoid
  | CFun CType [CType]
  | CClass Ident [(CType,Ident)]
  deriving (Eq)

getCType :: Type -> CType
getCType (Int  _            ) = CInt
getCType (Str  _            ) = CStr
getCType (Bool _            ) = CBool
getCType (Void _            ) = CVoid
getCType (Fun _ retType args) = CFun (getCType retType) (map getCType args)
getCType (Class _ ident     ) = CClass ident []

instance Show CType where
  show CInt                         = "int"
  show CStr                         = "string"
  show CBool                        = "bool"
  show CVoid                        = "void"
  show (CFun   _            _     ) = "function"
  show (CClass (Ident name) fields) = name

--------------------------------------------
type Env = (Map Ident (CType, Bool))

type Loc = Int

type Val = String

type Error = String

type Compl a = ExceptT Error (StateT Env IO) a

printError :: Pos -> String -> Compl a
printError pos text = throwError $ "error" ++ showPos pos ++ ": " ++ text

showPos :: Pos -> String
showPos (Just (l, c)) = " at line " ++ show l ++ " column " ++ show c
showPos Nothing       = ""

initEnv :: Env
initEnv = fromList
  [ (Ident "printInt"   , (CFun CVoid [CInt], False))
  , (Ident "printString", (CFun CVoid [CStr], False))
  , (Ident "error"      , (CFun CVoid [], False))
  , (Ident "readInt"    , (CFun CInt [], False))
  , (Ident "readString" , (CFun CStr [], False))
  ]

runStaticAnallysis :: Program -> IO (Either Error String)
runStaticAnallysis program = do
  co <- runStateT (runExceptT (checkProgram program)) initEnv
  case fst co of
    (Left  error) -> return $ Left error
    (Right r    ) -> return $ Right ("Program:" ++ r ++ "\n")

checkProgram :: Program -> Compl Val
checkProgram (Program pos topDefs) = do
  _      <- addDefs topDefs
  _      <- addDecls topDefs
  result <- checkDefs topDefs
  env    <- get
  case Map.lookup (Ident "main") env of
    Nothing                -> printError Nothing "No main function"
    Just (CFun CInt [], _) -> return ""
    Just (CFun CInt x, _) ->
      printError Nothing "Main should not have any arguments"
    Just (CFun retType _, _) ->
      printError Nothing $ "Main needs to return int, not " ++ show retType
    Just (r, _) -> printError Nothing "Main needs to be a function"

addDefs :: [TopDef] -> Compl Val
addDefs []           = return ""
addDefs (def : defs) = do
  result  <- addDef def
  results <- addDefs defs
  return ""


addDef :: TopDef -> Compl Val
addDef (FnDef pos retType ident args block) = do
  env <- get
  let (Ident varName) = ident
  case Map.lookup ident env of
    (Just (storedType, modif)) ->
      printError pos $ "Name " ++ varName ++ " is already taken."
    Nothing -> do
      assertArgType args
      put $ Map.insert
        ident
        (CFun (getCType retType) (Prelude.map getArgType args), False)
        env
      return ""
addDef (SDef pos ident items) = do
  env <- get
  let (Ident varName) = ident
  case Map.lookup ident env of
    (Just (storedType, modif)) ->
      printError pos $ "Name " ++ varName ++ " is already taken."
    Nothing -> do
      put $ Map.insert ident (CClass ident [], False) env
      return ""

addDecls :: [TopDef] -> Compl Val
addDecls []           = return ""
addDecls (def : defs) = do
  result  <- addDecl def
  results <- addDecls defs
  return ""

addDecl :: TopDef -> Compl Val
addDecl (FnDef pos retType ident args block) = do
  env <- get
  let (Ident varName) = ident
  assertArgType args
  put $ Map.insert
    ident
    (CFun (getCType retType) (Prelude.map getArgType args), False)
    env
  return ""
addDecl (SDef pos ident items) = do
  env <- get
  let (Ident varName) = ident
  checkItems items
  _ <- checkRep items
  put $ Map.insert ident (CClass ident (itemsToFields items), False) env
  return ""

checkRep :: [StructItem] -> Compl String
checkRep items = do
  forM_
    [ cIfExist i1 i2 | i1 <- items, i2 <- items ]
    (\x -> do
      x
    )
  return ""

cIfExist :: StructItem -> StructItem -> Compl String
cIfExist (SItem p1 _ i1) (SItem p2 _ i2) = do
  if p2 /= p1 && i1 == i2
    then do
      printError p2 $ identString i2 ++ " was already defined" ++ showPos p1
    else return ""

checkItems :: [StructItem] -> Compl String
checkItems []                        = return ""
checkItems ((SItem pos t i) : items) = do
  assertTypeExist pos (getCType t)
  checkItems items

assertTypeExist :: Pos -> CType -> Compl String
assertTypeExist pos (CClass ident fields) = do
  env <- get
  case Map.lookup ident env of
    Just sth -> return ""
    Nothing  -> printError pos $ (identString ident) ++ " is not defined"
assertTypeExist _ _ = return ""

itemsToFields :: [StructItem] -> [(CType, Ident)]
itemsToFields []                        = []
itemsToFields ((SItem pos t i) : items) = (getCType t, i) : itemsToFields items

{- Check if arguments' types
    Params:
      arguments
-}
assertArgType :: [Arg] -> Compl String
assertArgType [] = return ""
assertArgType ((Arg _ (Void p) (Ident name)) : args) =
  printError p $ "Argument " ++ name ++ " cannot be of type void"
assertArgType (Arg{} : args) = assertArgType args

getArgType :: Arg -> CType
getArgType (Arg pos argType ident) = getCType argType

checkDefs :: [TopDef] -> Compl Val
checkDefs []           = return ""
checkDefs (def : defs) = do
  result  <- checkDef def
  results <- checkDefs defs
  return (result ++ "," ++ results)

checkDef :: TopDef -> Compl Val
checkDef (FnDef pos retType ident args block) = do
  env <- get
  loopArgs args
  let (Block pos stmts) = block
  checkStmts (getCType retType) stmts
  validRet <- checkReturn stmts (getCType retType)
  if not validRet
    then printError pos $ "Function needs to return " ++ show (getCType retType)
    else return ""
  put env
  return ""
checkDef (SDef pos ident items) = return ""

checkStmts :: CType -> [Stmt] -> Compl Val
checkStmts retType []             = return ""
checkStmts retType (stmt : stmts) = do
  result  <- checkStmt retType stmt
  results <- checkStmts retType stmts
  return ""

initVar :: Pos -> CType -> [Item] -> Compl Val
initVar pos varType []                          = return ""
initVar p1  varType ((NoInit p2 ident) : items) = do
  addVar p1 varType ident
  initVar p1 varType items
initVar p1 varType ((Init p2 ident expr) : items) = do
  addVar p1 varType ident
  checkStmt CVoid (Ass p1 (LVar p2 ident) expr)
  initVar p1 varType items
  -- case lvalue of
  --   (LVar p2 ident) -> initVar p1 varType items
  --   (LSField p2 expr ident) -> initVar p1 varType items


checkReturn :: [Stmt] -> CType -> Compl Bool
checkReturn []                       CVoid        = return True
checkReturn []                       expectedType = return False
checkReturn ((Ret pos expr) : stmts) expectedType = do
  assertExprType expr expectedType
  checkReturn stmts expectedType
  return True
checkReturn ((VRet pos) : stmts) CVoid = do
  res <- checkReturn stmts CVoid
  return True
checkReturn ((VRet pos) : stmts) expectedType =
  printError pos $ "expedted " ++ show expectedType ++ " got void"
checkReturn ((Cond pos (ELitTrue _) stmt) : stmts) expectedType = do
  r1 <- checkReturn [stmt] expectedType
  r2 <- checkReturn stmts expectedType
  return (r1 || r2)
checkReturn ((Cond pos expr stmt) : stmts) expectedType =
  checkReturn stmts expectedType
checkReturn ((CondElse pos (ELitFalse _) stmt1 stmt2) : stmts) expectedType =
  do
    r2 <- checkReturn [stmt2] expectedType
    r3 <- checkReturn stmts expectedType
    return (r2 || r3)
checkReturn ((CondElse pos (ELitTrue _) stmt1 stmt2) : stmts) expectedType = do
  r1 <- checkReturn [stmt1] expectedType
  r3 <- checkReturn stmts expectedType
  return (r1 || r3)
checkReturn ((CondElse pos expr stmt1 stmt2) : stmts) expectedType = do
  r1 <- checkReturn [stmt1] expectedType
  r2 <- checkReturn [stmt2] expectedType
  r3 <- checkReturn stmts expectedType
  return (r1 && r2 || r3)
checkReturn ((While pos (ELitTrue _) stmt) : stmts) expectedType = do
  r1 <- checkReturn [stmt] expectedType
  r2 <- checkReturn stmts expectedType
  return (r1 || r2)
checkReturn ((While pos expr stmt) : stmts) expectedType =
  checkReturn stmts expectedType
checkReturn ((BStmt pos block) : stmts) expectedType = do
  let (Block pos bStmts) = block
  r1 <- checkReturn bStmts expectedType
  r2 <- checkReturn stmts expectedType
  return (r1 || r2)
checkReturn (stmt : stmts) expectedType = checkReturn stmts expectedType

newContext :: (Ident, (CType, Bool)) -> (Ident, (CType, Bool))
newContext (ident, (CFun retType args, modif)) =
  (ident, (CFun retType args, False))
newContext (ident, (storedType, modif)) = (ident, (storedType, True))

assertField :: Pos -> [(CType, Ident)] -> Ident -> Compl CType
assertField pos [] (Ident name) = printError pos $ " no such field " ++ name
assertField pos ((fieldType, fieldIdent) : fields) ident = do
  if fieldIdent == ident then return fieldType else assertField pos fields ident

checkStmt :: CType -> Stmt -> Compl Val
checkStmt retType (Empty pos      ) = return ""
checkStmt retType (BStmt pos block) = do
  let (Block pos stmts) = block
  env <- get
  put $ fromList $ Prelude.map newContext $ toList env
  checkStmts retType stmts
  put env
  return ""
checkStmt retType (Decl pos (Void vPos) items) =
  printError vPos "Cannot declare variable of type void"
checkStmt retType (Decl pos varType items) = do
  _ <- assertTypeExist pos (getCType varType)
  initVar pos (getCType varType) items
checkStmt retType (Ass pos (LVar p2 ident) expr) = do
  varType <- assertDecl pos ident
  assertExprType expr varType
checkStmt retType (Ass pos (LSField p2 expr ident) valExpr) = do
  objType <- getExprType expr
  let (CClass i fields) = objType
  e <- get
  let (Just (CClass classIdent fields, modif)) = Map.lookup i e
  fieldType <- assertField pos fields ident
  exprType  <- getExprType valExpr
  assertExprType valExpr fieldType
checkStmt retType (Incr pos ident) = assertVarType pos ident CInt
checkStmt retType (Decr pos ident) = assertVarType pos ident CInt
checkStmt retType (Ret  pos expr ) = assertExprType expr retType
checkStmt CVoid   (VRet pos      ) = return ""
checkStmt retType (VRet pos) =
  printError pos $ "Function should return " ++ show retType
checkStmt retType (Cond pos expr stmt) = do
  assertExprType expr CBool
  checkStmt retType stmt
checkStmt retType (CondElse pos expr stmt1 stmt2) = do
  assertExprType expr CBool
  checkStmt retType stmt1
  checkStmt retType stmt2
checkStmt retType (While pos expr stmt) = do
  assertExprType expr CBool
  checkStmt retType stmt
checkStmt retType (SExp pos expr) = do
  expType <- getExprType expr
  assertExprType expr expType

checkIfIntOverflow :: Integer -> Pos -> Compl ()
checkIfIntOverflow num pos =
  Control.Monad.when (num > 2147483647) $ printError pos "Integer overflow "

getExprType :: Expr -> Compl CType
getExprType (EVar pos (LVar p2 ident        )) = assertDecl pos ident
getExprType (EVar pos (LSField p2 expr ident)) = do
  objType <- getExprType expr
  let (CClass i fields) = objType
  e <- get
  let (Just (CClass classIdent fields, modif)) = Map.lookup i e
  return (CClass classIdent fields)
getExprType (ELitInt pos num) = do
  checkIfIntOverflow num pos
  return CInt
getExprType (ELitTrue  pos       ) = return CBool
getExprType (ELitFalse pos       ) = return CBool
getExprType (EOr  pos e1 e2      ) = return CBool
getExprType (EAnd pos e1 e2      ) = return CBool
getExprType (ERel pos e1 op e2   ) = return CBool
getExprType (EAdd pos e1 op e2   ) = getExprType e1
getExprType (EMul pos e1 op e2   ) = return CInt
getExprType (Not     pos expr    ) = return CBool
getExprType (Neg     pos expr    ) = return CInt
getExprType (EString pos string  ) = return CStr
getExprType (EApp pos ident exprs) = do
  (CFun retType args) <- assertDecl pos ident
  return retType
getExprType (EStruct p ident) = return $ CClass ident [] -- TODO
getExprType (ENull   p ident) = return $ CClass ident [] -- TODO

getField :: [(CType, Ident)] -> Ident -> CType
getField ((ctype, fieldIdent) : fields) ident
  | fieldIdent == ident = ctype
  | otherwise           = getField fields ident
getField [] ident = CVoid

assertExprType :: Expr -> CType -> Compl Val
assertExprType (EVar pos (LVar p2 ident)) exprType =
  assertVarType pos ident exprType
assertExprType (EVar pos (LSField p2 expr ident)) exprType = do
  objType <- getExprType expr
  let (CClass i fields) = objType
  e <- get
  let (Just (CClass classIdent fields, modif)) = Map.lookup i e
  let ctype = getField fields ident
  if ctype /= exprType
    then do
      printError pos "Error type"
    else return ""
assertExprType (ELitInt pos num) CInt = do
  checkIfIntOverflow num pos
  return ""
assertExprType (ELitTrue  pos) CBool = return ""
assertExprType (ELitFalse pos) CBool = return ""
assertExprType (EOr pos e1 e2) CBool = do
  assertExprType e1 CBool
  assertExprType e2 CBool
assertExprType (EAnd pos e1 e2) CBool = do
  assertExprType e1 CBool
  assertExprType e2 CBool
  return ""
assertExprType (ERel pos e1 op e2) CBool = do
  t1 <- getExprType e1
  t2 <- getExprType e2
  case t1 of
    (CClass i1 _) -> do
      let (CClass i2 _) = t2
      if i1 == i2
        then do
          return ""
        else
          printError (hasPosition op)
          $  "Cannot compare "
          ++ show i1
          ++ " with "
          ++ show i2
    _ -> do
      if t1 == t2
        then do
          case t1 of
            CStr  -> printError (hasPosition op) "Cannot compare Strings"
            CVoid -> printError (hasPosition op) "Cannot compare Voids"
            CFun ct cts ->
              printError (hasPosition op) "Cannot compare Functions"
            _ -> return ""
        else
          printError (hasPosition op)
          $  "Cannot compare "
          ++ show t1
          ++ " with "
          ++ show t2
assertExprType (EAdd pos e1 op e2) CInt = do
  assertExprType e1 CInt
  assertExprType e2 CInt
assertExprType (EAdd pos e1 (Plus opPos) e2) CStr = do
  assertExprType e1 CStr
  assertExprType e2 CStr
assertExprType (EAdd pos e1 (Minus opPos) e2) CStr =
  printError opPos "Cannot subtract string"
assertExprType (EMul pos e1 op e2) CInt = do
  assertExprType e1 CInt
  assertExprType e2 CInt
assertExprType (Not     pos expr    ) CBool        = assertExprType expr CBool
assertExprType (Neg     pos expr    ) CInt         = assertExprType expr CInt
assertExprType (EString pos string  ) CStr         = return ""
assertExprType (EApp pos ident exprs) expectedType = do
  storedType <- assertDecl pos ident
  let (Ident varName) = ident
  case storedType of
    (CFun retType argTypes) -> if retType /= expectedType
      then
        printError pos
        $  "Function"
        ++ varName
        ++ " should return "
        ++ show expectedType
      else checkArgTypes pos argTypes exprs
    _ -> printError pos $ varName ++ " should be a function "
  return ""
assertExprType (EStruct p ident) (CClass ident2 []) = do
  let (Ident name) = ident2
  if ident2 /= ident
    then do
      printError p $ "Expresion should be of type " ++ name ++ "\n"
    else do
      return ""
assertExprType (ENull p ident) exprectedType =
  assertExprType (EStruct p ident) exprectedType
assertExprType expr expedtedType =
  printError (hasPosition expr)
    $  "Expresion should be of type "
    ++ show expedtedType

checkArgTypes :: Pos -> [CType] -> [Expr] -> Compl Val
checkArgTypes pos []                   []             = return ""
checkArgTypes pos (argType : argTypes) (expr : exprs) = do
  assertExprType expr argType
  checkArgTypes pos argTypes exprs
checkArgTypes pos [] exprs =
  printError pos $ " expected " ++ show (length exprs) ++ " less arguments"
checkArgTypes pos args [] =
  printError pos $ " expected " ++ show (length args) ++ " more arguments"

assertVarType :: Pos -> Ident -> CType -> Compl Val
assertVarType pos ident expectedType = do
  env <- get
  let (Ident varName) = ident
  case Map.lookup ident env of
    (Just (varType, modif)) -> do
      if varType == expectedType
        then return ""
        else
          printError pos
          $  "Variable"
          ++ varName
          ++ " should be of type "
          ++ show expectedType
      return ""
    Nothing -> printError pos $ varName ++ " is not declared"

assertDecl :: Pos -> Ident -> Compl CType
assertDecl pos ident = do
  env <- get
  let (Ident varName) = ident
  case Map.lookup ident env of
    (Just (varType, modif)) -> return varType
    Nothing                 -> printError pos $ varName ++ " is not declared"

loopArgs :: [Arg] -> Compl Val
loopArgs []           = return ""
loopArgs (arg : args) = do
  let (Arg pos argType ident) = arg
  addVar pos (getCType argType) ident
  loopArgs args

addVar :: Pos -> CType -> Ident -> Compl Val
addVar pos varType ident = do
  env <- get
  let (Ident varName) = ident
  case Map.lookup ident env of
    (Just (storedType, False)) ->
      printError pos $ "Name " ++ varName ++ " is already defined"
    (Just (storedType, True)) -> do
      put $ Map.insert ident (varType, False) env
      return ""
    Nothing -> do
      put $ Map.insert ident (varType, False) env
      return ""
