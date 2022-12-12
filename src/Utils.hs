module Utils where

import           Data.Char                      ( ord )
import           Env
import           Latte.Abs
import           Numeric
import           Types


deleteLast :: [a] -> [a]
deleteLast []      = []
deleteLast [h    ] = []
deleteLast (h : t) = h : deleteLast t

{- Map string to llvm-const form
    Params:
      string to map
-}
prepString :: [Char] -> [Char]
prepString []        = ""
prepString (c : str) = "\\" ++ pref (showHex (ord c) "") ++ prepString str
 where
  pref :: String -> String
  pref str | length str > 1 = str
           | otherwise      = "0" ++ str

{- Get unique variable name (for cmp expr) -}
logicalCmpVar :: Compl Ident
logicalCmpVar = do
  (Reg num) <- useNewReg
  let ident = Ident $ "_logical_cmp_" ++ show num
  return ident

{- Add indention before every line
    Params:
      string 
-}
tab :: String -> String
tab s = indention ++ tabH s
 where
  tabH :: String -> String
  tabH []            = []
  tabH ('\n' : rest) = "\n" ++ indention ++ tabH rest
  tabH (char : rest) = char : tabH rest

  indention :: String
  indention = "    "


{- Get string with build-in functions declarations -}
builtinFuncDeclarations :: String
builtinFuncDeclarations =
  "declare i32 @puts(i8*)\n"
    ++ "declare i8* @readString()\n"
    ++ "declare i32 @readInt()\n"
    ++ "declare i8* @malloc(i32)\n"
    ++ "declare i8* @strcat(i8*,i8*)\n"
    ++ "declare i32 @strlen(i8*)\n"
    ++ "declare i8* @strcpy(i8*,i8*)\n"
    ++ "declare void @printInt(i32 %x)\n"
    ++ "declare void @printString(i8* %x)\n"
    ++ "declare i32 @printf(i8*, ...)\n"
    ++ "declare i32 @scanf(i8*, ...)\n"
    ++ "declare void @error()\n"
    ++ "declare i8* @concat(i8* %s1, i8* %s2)\n"
    ++ "declare void @realloc(i8*, i32)\n"
    ++ "declare void @free(i8*)\n\n\n"

identString :: Ident -> String
identString (Ident name) = name
