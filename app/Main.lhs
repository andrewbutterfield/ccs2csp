\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2020--22

LICENSE: BSD3, see file LICENSE at ccs2csp root
\end{verbatim}
\begin{code}
module Main where

import System.IO
import System.Environment
import System.FilePath
import Data.Char

import Syntax
import Examples
import Semantics
import Translate
import CSPm
import CCSm

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = Main.dbg ('@':nm++":\n") x
\end{code}

\subsection{Version}

\begin{code}
progName = "ccs2csp"
version = "0.5.0.0"
name_version = progName++" "++version
\end{code}

\subsection{Program Top-Level}

The program provides an ability to convert a single CCS process,
or a complete CCS program.
It can work with \texttt{stdin} and \text{stdout},
or with named files.
Control is achieved with command-line arguments.

\subsubsection{Program Configuration}

We need to know input and output files,
and what (program/process) is to be translated:
\begin{code}
data Mode = DoProgram | DoProcess deriving Eq
data Config
  = Config  { helpout  ::  Bool
            , ccsfile  ::  Handle
            , cspfile  ::  Handle
            , mode     ::  Mode
            }
config0 = Config False stdin stdout DoProcess
\end{code}

Command-line argument handling:
\begin{code}
processArgs :: [String] -> IO Config
processArgs [] = return config0
processArgs [arg]
  | arg == "--help"  =  return $ config0{ helpout = True }
  | arg == "-prog"   =  return $ config0{ mode = DoProgram }
  | otherwise        =  openInput config0 arg
processArgs [arg1,arg2]
  | arg1 == "-prog"  =  openInput config0{ mode = DoProgram } arg2
  | otherwise  =  do configI <- openInput config0 arg1
                     openOutput configI arg2
processArgs [arg1,arg2,arg3]
  | arg1 == "-prog"
    = do let configP = config0{ mode = DoProgram }
         configI <- openInput configP arg2
         openOutput configI arg3
processArgs _  =  help >> stop

defaultCCSextension = "proc" -- used by CAAL
defaultCSPextension = "csp"  -- used by FDR

fixExt ext fname
  | takeExtension fname == ""  =  addExtension fname ext
  | otherwise                  =  fname

openInput config arg
  = do h <- openFile (fixExt defaultCCSextension arg) ReadMode
       return config{ ccsfile = h }

openOutput config arg
  = do h <- openFile (fixExt defaultCSPextension arg) WriteMode
       return config{ cspfile = h }

help  = putStrLn $ unlines
          [ "usage: ccs2csp [-prog] [infile[.ext1]] [outfile[.ext2]]"
          , "-prog expects a full CCS program rather than a single CCS process"
          , "infile[.ext1] defaults to 'stdin'"
          , "outfile[.ext1] defaults to 'stdout'"
          , "ext1 defaults to '"++defaultCCSextension++"'"
          , "ext2 defaults to '"++defaultCSPextension++"'"
          ]

stop = fail "ccs2csp run aborted"
\end{code}

\subsubsection{Mainline}

\begin{code}
main :: IO ()
main
  = do args <- getArgs
       config <- processArgs args
       if helpout config
       then help
       else if mode config == DoProgram
       then putStrLn ("CCS Program translation not yet implemented!")
       else do
         putStrLn ("Translating CCS Process to CSPm...")
         ccsm <- hGetContents $ ccsfile config
         case processParser ccsm of
           Left err -> putStrLn err
           Right proc
            -> let
                 generation = genExample $ proc2CCS proc
                 (CSP csp) = snd $ last generation
                 -- csp = ccs2csp $ proc2CCS proc
                 cspm = generateCSPm "FROM_CCS" csp
               in do putStrLn $ showExample generation
                     hPutStr (cspfile config) cspm
                     hClose (cspfile config)
\end{code}
