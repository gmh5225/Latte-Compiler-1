module Utils where

import           Data.Char                      ( ord )
import           Env
import           Latte.Abs
import           Numeric
import           Types

prepString :: [Char] -> [Char]
prepString (c : str) = "\\" ++ pref (showHex (ord c) "") ++ prepString str
prepString []        = ""

pref :: String -> String
pref str | length str > 1 = str
         | otherwise      = "0" ++ str

logicalCmpVar :: Compl Ident
logicalCmpVar = do
    (Reg num) <- useNewReg
    let ident = Ident $ "_logical_cmp_" ++ show num
    return ident

funcDeclarations :: String
funcDeclarations =
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
