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

type Env = (PEnv, VEnv, Store, Loc, Register, Label, Var)

type Compl a = ExceptT Error (StateT Env IO) a

initEnv :: Env
initEnv =
  ( fromList
      [ (Ident "printInt", CFun CVoid [CInt]),
        (Ident "printString", CFun CVoid [CStr]),
        (Ident "error", CFun CVoid []),
        (Ident "readInt", CFun CInt []),
        (Ident "concat", CFun CStr [CStr, CStr]),
        (Ident "error", CFun CVoid []),
        (Ident "readString", CFun CStr [])
      ],
    Map.empty,
    Map.empty,
    0,
    Reg 0,
    Lab 0,
    Var 0
  )

addVar :: CType -> Ident -> Compl Register
addVar varType ident = do
  (penv, venv, store, loc, reg, label, var) <- get
  put (penv, Map.insert ident loc venv, Map.insert loc (varType, RegV reg) store, loc + 1, nextReg reg, label,  var)
  return reg

setVarReg :: Ident -> Register -> Compl ()
setVarReg ident newReg = do
    (penv, venv, store, loc, reg, label, var) <- get
    let (Just varLoc) = Map.lookup ident venv
    let (Just (varType, _)) = Map.lookup varLoc store
    put  (penv, venv, Map.insert varLoc (varType, RegV newReg) store, loc, reg, label, var)
    return ()

setVarVal :: Ident -> Val -> Compl ()
setVarVal ident val = do
    (penv, venv, store, loc, reg, label, var) <- get
    let (Just varLoc) = Map.lookup ident venv
    let (Just (varType, _)) = Map.lookup varLoc store
    put  (penv, venv, Map.insert varLoc (varType, val) store, loc, reg, label, var)
    return ()

addProc :: CType -> Ident -> [CType] -> Compl ()
addProc retType ident argsTypes = do
  (penv, venv, store, loc, reg, label, var) <- get
  put (Map.insert ident (CFun retType argsTypes) penv, venv, store, loc, reg, label, var)
  return ()

useNewReg :: Compl Register
useNewReg = do
  (penv, venv, store, loc, reg, label, var) <- get
  put (penv, venv, store, loc, nextReg reg, label, var)
  return reg

useLabel :: Compl Label
useLabel = do
  (penv, venv, store, loc, reg, label, var) <- get
  put (penv, venv, store, loc, reg, nextLabel label, var)
  return label

setStore :: Store -> Compl ()
setStore store = do
  (penv, venv, _, loc, reg, label, var) <- get
  put (penv, venv, store, loc, reg, nextLabel label, var)
  return ()

getVar :: Ident -> Compl (CType, Val)
getVar ident = do
  (penv, venv, store, loc, reg, label, var) <- get
  let (Just varLoc) = Map.lookup ident venv
  let (Just (ctype, varVal)) = Map.lookup varLoc store
  return (ctype, varVal)

getProc :: Ident -> Compl (CType, [CType])
getProc ident = do
  (penv, venv, store, loc, reg, label, var) <- get
  let (Just (CFun retType argsTypes)) = Map.lookup ident penv
  return (retType, argsTypes)

setLocVal :: Loc -> Val -> Compl ()
setLocVal loc val = do
  (penv, venv, store, _, reg, label, var) <- get
  let (Just (varType, _)) = Map.lookup loc store
  put  (penv, venv, Map.insert loc (varType, val) store, loc, reg, label, var)
  return ()


generatePhi :: Store -> Store -> Store -> Label -> Label -> Label -> Compl String
generatePhi pStore tStore fStore bLab tLab fLab = do
  let f k v a = (a ++  [(k, v)]) 
  let pArr = foldrWithKey f [] pStore -- [(Loc, (CType, Val))]

  result <- mapPhi bLab tLab fLab pArr tStore fStore
  return result

mapPhi :: Label -> Label -> Label -> [(Loc, (CType, Val))] -> Store -> Store -> Compl String
mapPhi bL tL fL [] tStore fStore  = return "" 
mapPhi bL tL fL ((loc,(ctype,val)):pArr) tStore fStore  = do
  result <- mapPhi bL tL fL pArr tStore fStore

  reg <- useNewReg

  r <- setLocVal loc (RegV reg)

  let (Just (_,valTrue)) = Map.lookup loc tStore
  let (Just (_,valFalse)) = Map.lookup loc fStore

  let currResult =  show reg  ++ "= phi " ++ show ctype  ++ " ["++ show valTrue ++", %"++ show tL ++ "], " ++  "["++ show valFalse ++", %"++ show fL ++ "]\n"

  return $ result ++ currResult ++ "\n\n"