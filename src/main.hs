module Main where

import           Compiler
import           Latte.Abs
import           Latte.Par
import           StaticAnalysis
import           System.Environment (getArgs)
import           System.Exit
import           System.FilePath    (dropExtension, replaceExtension,
                                     takeDirectory, takeFileName)
import           System.IO          (hPrint, hPutStr, hPutStrLn, stderr)
import           System.Process
import           Text.Parsec.Prim   (putState)

helpStr :: String
helpStr =
  "---- Latte compiler ----\n\n" ++
  "Compile latte file:\n" ++
  "./latc <filename>\n\n" ++ "------------------------\n"

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> putStr helpStr
    [filename] -> do
      code <- readFile filename
      let tokens = myLexer code
      let outputPath = replaceExtension filename ".ll"
      let outFile = replaceExtension filename ".bc"
      let outputDir = takeDirectory outputPath
      let programName = dropExtension $ takeFileName filename
      case pProgram tokens of
        Right program -> do
          print program
          result <- runStaticAnallysis program
          case result of
            (Right text) -> do
              putStrLn "OK\n"
              compilerResult <- compileProgram program
              case compilerResult of
                (Right generatedText) -> do
                  writeFile
                    (outputDir ++ "/" ++ programName ++ ".ll")
                    generatedText
                  processHandle <- runCommand ("llvm-as " ++ outputPath)
                  waitForProcess processHandle
                  processHandle <-
                    runCommand
                      ("llvm-link -o " ++
                       outFile ++ " " ++ outFile ++ " lib/runtime.bc")
                  waitForProcess processHandle
                  putStrLn $ "Generated: " ++ outputPath ++ " and " ++ outFile
                (Left error) -> hPutStrLn stderr $ "ERROR\n" ++ error ++ "\n"
              exitSuccess
            (Left error) -> do
              hPutStrLn stderr $ "ERROR\n" ++ error ++ "\n"
              exitFailure
        Left error -> do
          hPutStrLn stderr $ "ERROR\n" ++ error ++ "\n"
          exitFailure
      return ()
    _ -> putStr helpStr
