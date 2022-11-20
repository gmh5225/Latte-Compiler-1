module Env where

import Control.Monad.Except
import Control.Monad.State
import Data.Map as Map
import Latte.Abs
import StaticAnalysis (printError)
import Types

type Error = String

type Loc = Int

type VEnv = Map Ident Loc

type PEnv = Map Ident CType

type Store = Map Loc (CType, Val)

data Env = Env { sPenv :: PEnv,
                  sVenv :: VEnv,
                  sStore :: Store,
                  sLoc :: Loc,
                  sRegister :: Register,
                  sLabel :: Label,
                  -- var :: PEnv,
                  sVar :: Var}

type Compl a = ExceptT Error (StateT Env IO) a

-- initEnv :: Env
-- initEnv = Env {}
initEnv :: Env
initEnv = Env { sPenv = fromList
      [ (Ident "printInt", CFun CVoid [CInt]),
        (Ident "printString", CFun CVoid [CStr]),
        (Ident "error", CFun CVoid []),
        (Ident "readInt", CFun CInt []),
        (Ident "concat", CFun CStr [CStr, CStr]),
        (Ident "error", CFun CVoid []),
        (Ident "readString", CFun CStr [])
      ],
    sVenv = Map.empty,
    sStore = Map.empty,
    sLoc = 0,
    sRegister = Reg 0,
    sLabel = Lab 0,
    sVar = Var 0
  }

-- Prawdopodobnie w jakims miejscu nie aktualalizuje loc TODO
addVar :: CType -> Ident -> Compl Register
addVar varType ident = do
  state <- get
  let reg = sRegister state
  let loc = sLoc state
  let venv = sVenv state
  let store = sStore state

  put state {sVenv = Map.insert ident (loc+1) venv,
              sStore = Map.insert (loc+1) (varType, RegV reg) store,
              sLoc = loc + 2,
              sRegister = nextReg reg}
  return reg

setVarVal :: Ident -> Val -> Compl ()
setVarVal ident val = do
    state <- get
    let venv = sVenv state
    let store = sStore state

    let (Just varLoc) = Map.lookup ident venv
    let (Just (varType, _)) = Map.lookup varLoc store
    
    put state {sStore = Map.insert varLoc (varType, val) store}

addProc :: CType -> Ident -> [CType] -> Compl ()
addProc retType ident argsTypes = do
  state <- get
  put state {sPenv = Map.insert ident (CFun retType argsTypes) (sPenv state)}

useNewReg :: Compl Register
useNewReg = do
  state <- get
  let reg = sRegister state
  put state {sRegister = nextReg reg}
  return reg

useLabel :: Compl Label
useLabel = do
  state <- get
  let label = sLabel state
  put state {sLabel = nextLabel label}
  return label
  
setStore :: Store -> Compl ()
setStore store = do
  state <- get
  put state {sStore = store}
  -- put (penv, venv, store, loc, reg, nextLabel label, var)

getVar :: Ident -> Compl (CType, Val)
getVar ident = do
  state <- get
  let venv = sVenv state
  let store = sStore state
  
  let (Just varLoc) = Map.lookup ident venv
  let (Just (ctype, varVal)) = Map.lookup varLoc store
  return (ctype, varVal)  

getProc :: Ident -> Compl (CType, [CType])
getProc ident = do
  state <- get
  let penv = sPenv state
  
  let (Just (CFun retType argsTypes)) = Map.lookup ident penv
  return (retType, argsTypes)

setLocVal :: Loc -> Val -> Compl ()
setLocVal loc val = do
  state <- get
  let store = sStore state
  
  let (Just (varType, _)) = Map.lookup loc store
  put state {sStore = Map.insert loc (varType, val) store}

-- TODO: Cleanup
generatePhi :: Store -> Store -> Store -> Label -> Label -> Label -> Label -> Label -> Compl String
generatePhi pStore tStore fStore bLab tLab fLab endTrue endFalse = do
  let f k v a = (a ++  [(k, v)])  
  let pArr = foldrWithKey f [] pStore

  result <- mapPhi bLab tLab fLab pArr tStore fStore endTrue endFalse
  return result

mapPhi :: Label -> Label -> Label -> [(Loc, (CType, Val))] -> Store -> Store -> Label -> Label -> Compl String
mapPhi bL tL fL [] tStore fStore endTrue endFalse  = return "" 
mapPhi bL tL fL ((loc,(ctype,val)):pArr) tStore fStore  endTrue endFalse = do
  result <- mapPhi bL tL fL pArr tStore fStore endTrue endFalse

  reg <- useNewReg

  r <- setLocVal loc (RegV reg)

  let (Just (_,valTrue)) = Map.lookup loc tStore
  let (Just (_,valFalse)) = Map.lookup loc fStore

  let currResult =  show reg  ++ "= phi " ++ show ctype  ++ " ["++ show valTrue ++", %"++ show endTrue ++ "], " ++  "["++ show valFalse ++", %"++ show endFalse ++ "]\n"

  return $ result ++ currResult ++ "\n\n"

newRegisters :: Compl ()
newRegisters = do
  state <- get
  let store = sStore state
  let f k v a = (a ++  [(k, v)])  
  let pArr = foldrWithKey f [] store
  newRegister pArr

newRegister :: [(Loc,(CType,Val))] -> Compl ()
newRegister [] = return ()
newRegister ((vloc,(ctype,val)):rest) = do
  newReg <- useNewReg
  -- (penv, venv, store,loc, reg, label, var) <- get
  state <- get
  let store = sStore state
  put state {sStore = Map.insert vloc (ctype,RegV newReg) store}

  newRegister rest
  return ()
  
generate3Phi :: Store -> Store -> Store -> Label -> Label -> Compl String
generate3Phi updatedStore store1 store2 label1 label2 = do
  let f k v a = (a ++  [(k, v)])  
  let pArr = foldrWithKey f [] updatedStore
  
  result <- map3Phi store1 store2 pArr label1 label2 
  return result

map3Phi :: Store -> Store -> [(Loc, (CType, Val))] -> Label -> Label -> Compl String
map3Phi store1 store2 [] label1 label2  = return "" 
map3Phi store1 store2  ((loc,(ctype,val)):pArr) label1 label2 = do
  result <- map3Phi store1 store2 pArr label1 label2

  -- reg <- useNewReg -- juz dodalismy nowe rejestry co chcemy przypisac dla phi
  let (RegV reg) = val

  r <- setLocVal loc (RegV reg)

  let (Just (_,val1)) = Map.lookup loc store1
  let (Just (_,val2)) = Map.lookup loc store2

  let currResult =  show reg  ++ "= phi " ++ show ctype  ++ " ["++ show val1 ++", %"++ show label1 ++ "], " ++  "["++ show val2 ++", %"++ show label2 ++ "]\n"

  return $ result ++ currResult ++ "\n\n"


getDepr :: Compl (PEnv, VEnv, Store, Loc, Register, Label, Var)
getDepr = do
  state <- get
  return (sPenv state, sVenv state, sStore state, sLoc state, sRegister state, sLabel state, sVar state)


putDepr :: (PEnv, VEnv, Store, Loc, Register, Label, Var) -> Compl ()
putDepr (penv, venv, store, loc, register, label, var) = do
  state <- get
  put state {sPenv = penv, 
            sVenv = venv, 
            sStore = store,
            sLoc =loc,
            sRegister=register,
            sLabel = label,
            sVar = var}