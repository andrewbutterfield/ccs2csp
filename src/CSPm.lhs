\section{Generating CSPm}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2020-21

LICENSE: BSD3, see file LICENSE at ccs2csp root
\end{verbatim}
\begin{code}
module CSPm where
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Control
import Syntax
import Semantics

import Debug.Trace
dbg msg x = trace (msg++show x) x
--pdbg nm x = Translate.dbg ("\n@"++nm++":\n") x
\end{code}

\subsection{Introduction}

We convert CSP process into text using CSPm syntax,
as accepted by FDR4.

\begin{code}
generateCSPm :: CSP -> String
generateCSPm = unlines . genCSPm

genCSPm :: CSP -> [String]
genCSPm = outputCSPm . gatherCSPm


type CSPmDecls = ()

gatherCSPm :: CSP -> (CSPmDecls, CSP)
gatherCSPm csp = ((),csp)

outputCSPm :: (CSPmDecls, CSP) -> [String]
outputCSPm (_,csp) = ["CSPm N.Y.I."]
\end{code}
