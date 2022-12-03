module Env where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map             as Map
import           Latte.Abs
import           StaticAnalysis       (printError)
import           Types

type Error = String

type Loc = Int

type VEnv = Map Ident Loc

type PEnv = Map Ident CType

type Store = Map Loc (CType, Val)

type StoreArray = [(Loc, (CType, Val))]

data Env =
  Env
    { sPenv     :: PEnv
    , sVenv     :: VEnv
    , sStore    :: Store
    , sLoc      :: Loc
    , sRegister :: Register
    , sLabel    :: Label
    }

type Compl a = ExceptT Error (StateT Env IO) a

initEnv :: Env
initEnv =
  Env
    { sPenv =
        fromList
          [ (Ident "printInt", CFun CVoid [CInt])
          , (Ident "printString", CFun CVoid [CStr])
          , (Ident "error", CFun CVoid [])
          , (Ident "readInt", CFun CInt [])
          , (Ident "concat", CFun CStr [CStr, CStr])
          , (Ident "error", CFun CVoid [])
          , (Ident "readString", CFun CStr [])
          ]
    , sVenv = Map.empty
    , sStore = Map.empty
    , sLoc = 0
    , sRegister = Reg 0
    , sLabel = Lab 0
    }

-- Prawdopodobnie w jakims miejscu nie aktualalizuje loc TODO
addVar :: CType -> Ident -> Compl Register
addVar varType ident = do
  state <- get
  let reg = sRegister state
  let loc = sLoc state
  let venv = sVenv state
  let store = sStore state
  put
    state
      { sVenv = Map.insert ident (loc + 1) venv
      , sStore = Map.insert (loc + 1) (varType, RegV reg) store
      , sLoc = loc + 2
      , sRegister = nextReg reg
      }
  return reg

setVarVal :: Ident -> Val -> Compl ()
setVarVal ident val = do
  state <- get
  let (Just loc) = Map.lookup ident (sVenv state)
  let (Just (vtype, _)) = Map.lookup loc (sStore state)
  put state {sStore = Map.insert loc (vtype, val) (sStore state)}

getArgCType :: Arg -> CType
getArgCType (Arg pos argType ident) = getCType argType

addFunc :: TopDef -> Compl ()
addFunc (FnDef pos retType ident args block) = do
  state <- get
  put
    state
      { sPenv =
          Map.insert
            ident
            (CFun (getCType retType) (Prelude.map getArgCType args))
            (sPenv state)
      }

useNewReg :: Compl Register
useNewReg = do
  state <- get
  put state {sRegister = nextReg (sRegister state)}
  return $ sRegister state

useLabel :: Compl Label
useLabel = do
  state <- get
  put state {sLabel = nextLabel (sLabel state)}
  return $ sLabel state

setStore :: Store -> Compl ()
setStore store = do
  state <- get
  put state {sStore = store}

getVar :: Ident -> Compl (CType, Val)
getVar ident = do
  state <- get
  let (Just loc) = Map.lookup ident $ sVenv state
  let (Just result) = Map.lookup loc $ sStore state
  return result

getProc :: Ident -> Compl (CType, [CType])
getProc ident = do
  state <- get
  let (Just (CFun retType argsTypes)) = Map.lookup ident $ sPenv state
  return (retType, argsTypes)

setLocVal :: Loc -> Val -> Compl ()
setLocVal loc val = do
  state <- get
  let (Just (vtype, _)) = Map.lookup loc (sStore state)
  put state {sStore = Map.insert loc (vtype, val) (sStore state)}

storeToArray :: Store -> Compl StoreArray
storeToArray store = do
  let f k v a = (a ++ [(k, v)])
  return $ foldrWithKey f [] store

-- TODO: Cleanup
-- Generuje instukcje phi dla kazdej zminnej z store1 z [lablel,val] odpowiednio z store2/3
generatePhi :: Store -> Store -> Store -> Label -> Label -> Compl String
generatePhi pStore tStore fStore endTrue endFalse = do
  pArr <- storeToArray pStore
  mapPhi pArr tStore fStore endTrue endFalse

mapPhi :: StoreArray -> Store -> Store -> Label -> Label -> Compl String
mapPhi [] tStore fStore endTrue endFalse = return ""
mapPhi ((loc, (ctype, val)):pArr) tStore fStore endTrue endFalse = do
  result <- mapPhi pArr tStore fStore endTrue endFalse
  reg <- useNewReg
  r <- setLocVal loc (RegV reg)
  let (Just (_, valTrue)) = Map.lookup loc tStore
  let (Just (_, valFalse)) = Map.lookup loc fStore
  let currResult =
        show reg ++
        "= phi " ++
        show ctype ++
        " [" ++
        show valTrue ++
        ", %" ++
        show endTrue ++
        "], " ++ "[" ++ show valFalse ++ ", %" ++ show endFalse ++ "]\n"
  return $ result ++ currResult ++ "\n\n"

newRegisters :: Compl ()
newRegisters = do
  state <- get
  pArr <- storeToArray (sStore state)
  newRegister pArr

newRegister :: StoreArray -> Compl ()
newRegister [] = return ()
newRegister ((vloc, (ctype, val)):arr) = do
  newReg <- useNewReg
  state <- get
  put state {sStore = Map.insert vloc (ctype, RegV newReg) (sStore state)}
  newRegister arr

-- tak jak generatePhi generuje phi ale tutaj mapPhi nie dodaje nowych rejestrow tylko bierze bo juz zrobilismy newRegister
generate3Phi :: Store -> Store -> Store -> Label -> Label -> Compl String
generate3Phi updatedStore store1 store2 label1 label2 = do
  pArr <- storeToArray updatedStore
  map3Phi store1 store2 pArr label1 label2

map3Phi :: Store -> Store -> StoreArray -> Label -> Label -> Compl String
map3Phi store1 store2 [] label1 label2 = return ""
map3Phi store1 store2 ((loc, (ctype, val)):pArr) label1 label2 = do
  result <- map3Phi store1 store2 pArr label1 label2
  -- reg <- useNewReg -- juz dodalismy nowe rejestry co chcemy przypisac dla phi
  let (RegV reg) = val
  r <- setLocVal loc (RegV reg)
  let (Just (_, val1)) = Map.lookup loc store1
  let (Just (_, val2)) = Map.lookup loc store2
  let currResult =
        show reg ++
        "= phi " ++
        show ctype ++
        " [" ++
        show val1 ++
        ", %" ++
        show label1 ++
        "], " ++ "[" ++ show val2 ++ ", %" ++ show label2 ++ "]\n"
  return $ result ++ currResult ++ "\n\n"

getDepr :: Compl (PEnv, VEnv, Store, Loc, Register, Label)
getDepr = do
  state <- get
  return
    ( sPenv state
    , sVenv state
    , sStore state
    , sLoc state
    , sRegister state
    , sLabel state)

putDepr :: (PEnv, VEnv, Store, Loc, Register, Label) -> Compl ()
putDepr (penv, venv, store, loc, register, label) = do
  state <- get
  put
    state
      { sPenv = penv
      , sVenv = venv
      , sStore = store
      , sLoc = loc
      , sRegister = register
      , sLabel = label
      }
