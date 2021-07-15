\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Main where

import System.IO
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
version = "0.0.1.1"
name_version = progName++" "++version
\end{code}

\subsection{Mainline}

\begin{code}
main :: IO ()
main
  = do putStrLn name_version
       putStr "Enter Filename root: " ; hFlush stdout
       root <- getLine
       let ccsfile = root ++ ".proc"
       let procname = map toUpper root
       let cspfile = root ++ ".csp"
       putStrLn ( "Converting CCS process in "
                ++ ccsfile
                ++ " to CSP process named "
                ++ procname
                ++ " in "
                ++ cspfile
                )
       ccsm <- readFile ccsfile
       case processParser ccsm of
         Left err -> putStrLn err
         Right proc
          -> let
               csp = ccs2csp $ proc2CCS proc
               cspm = generateCSPm procname csp
             in writeFile cspfile cspm
       putStrLn "Goodbye!"
\end{code}
