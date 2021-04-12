\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Main where

import Syntax
import Examples
import Semantics
import Translate

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = Main.dbg ('@':nm++":\n") x
\end{code}

\subsection{Version}

\begin{code}
progName = "ccs2csp"
version = "0.0.1.0"
name_version = progName++" "++version
\end{code}

\subsection{Mainline}

\begin{code}
main :: IO ()
main
  = do putStrLn name_version
       putStrLn "Nothing to see here yet."
       putStrLn "Suggest you use ghci"
       putStrLn "stack ghci src/Examples.lhs"
       putStrLn "\n, Goodbye."
\end{code}
