module Env where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map                      as Map
import           Latte.Abs
import           StaticAnalysis                 ( printError )
import           Types

type Error = String

type Loc = Int

type VEnv = Map Ident Loc

type PEnv = Map Ident CType

type Store = Map Loc (CType, Var)

data Env = Env
  { sPenv     :: PEnv
  , sVenv     :: VEnv
  , sStore    :: Store
  , sLoc      :: Loc
  , sRegister :: Register
  , sLabel    :: Label
  , sStrs     :: [String]
  , sVar      :: Var
  }

type Compl a = ExceptT Error (StateT Env IO) a

initEnv :: Env
initEnv = Env
  { sPenv     = fromList
                  [ (Ident "printInt"   , CFun CVoid [CInt])
                  , (Ident "printString", CFun CVoid [CStr])
                  , (Ident "error"      , CFun CVoid [])
                  , (Ident "readInt"    , CFun CInt [])
                  , (Ident "concat"     , CFun CStr [CStr, CStr])
                  , (Ident "error"      , CFun CVoid [])
                  , (Ident "readString" , CFun CStr [])
                  ]
  , sVenv     = Map.empty
  , sStore    = Map.empty
  , sLoc      = 0
  , sRegister = Reg 0
  , sLabel    = Lab 0
  , sStrs     = []
  , sVar      = Var 0
  }

addString :: String -> Compl ()
addString decl = do
  state <- get
  if decl `elem` sStrs state
    then return ()
    else put state { sStrs = sStrs state ++ [decl] }

addVar :: CType -> Ident -> Compl Var
addVar varType ident = do
  state <- get
  let venv  = sVenv state
  let store = sStore state
  let reg   = sRegister state
  let loc   = sLoc state
  let var   = sVar state

  put state { sVenv  = Map.insert ident loc venv
            , sStore = Map.insert loc (varType, var) store
            , sLoc   = loc + 1
            , sVar   = nextVar var
            }
  return var

setVarVal :: Ident -> Var -> Compl ()
setVarVal ident var = do
  state <- get
  let (Just loc)        = Map.lookup ident (sVenv state)
  let (Just (vtype, _)) = Map.lookup loc (sStore state)
  put state { sStore = Map.insert loc (vtype, var) (sStore state) }

getArgCType :: Arg -> CType
getArgCType (Arg pos argType ident) = getCType argType

addFunc :: TopDef -> Compl ()
addFunc (FnDef pos retType ident args block) = do
  state <- get
  put state
    { sPenv = Map.insert
                ident
                (CFun (getCType retType) (Prelude.map getArgCType args))
                (sPenv state)
    }

useNewReg :: Compl Register
useNewReg = do
  state <- get
  put state { sRegister = nextReg (sRegister state) }
  return $ sRegister state

useLabel :: Compl Label
useLabel = do
  state <- get
  put state { sLabel = nextLabel (sLabel state) }
  return $ sLabel state

getVar :: Ident -> Compl (CType, Var)
getVar ident = do
  state <- get
  let (Just loc)    = Map.lookup ident $ sVenv state
  let (Just result) = Map.lookup loc $ sStore state
  return result

getProc :: Ident -> Compl (CType, [CType])
getProc ident = do
  state <- get
  let (Just (CFun retType argsTypes)) = Map.lookup ident $ sPenv state
  return (retType, argsTypes)

lastVar :: Compl Var
lastVar = do
  state <- get
  let Var v = sVar state
  return (Var $ v -1)

