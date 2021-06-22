genProcs\section{Generating CSPm}
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
generateCSPm csp
 = unlines $ assemble (genDecls [] csp) (genProcs [] csp)

genDecls :: [String] -> CSP -> [String]
genDecls slced Stop = slced
genDecls slced Skip = slced
genDecls slced (CSPpfx evt csp) = genDecls (("channel "++evt):slced) csp
genDecls slced (Seq csp1 csp2) = ("NYfI":slced)
genDecls slced (IntC csp1 csp2) = ("NYfI":slced)
genDecls slced (ExtC csp1 csp2) = ("NYfI":slced)
genDecls slced (Par evts csp1 csp2) = ("NYfI":slced)
genDecls slced (Hide evts csp) = ("NYfI":slced)
genDecls slced (CSPren rename csp) = ("NYfI":slced)
genDecls slced (CSPvar v) = slced
genDecls slced (CSPmu x csp) = ("NYfI":slced)

genProcs :: [String] -> CSP -> [String]
genProcs scorp Stop = ("STOP":scorp)
genProcs scorp Skip = ("SKIP":scorp)
genProcs scorp (CSPpfx pfx csp) = genProcs ((pfx ++ " -> "):scorp) csp
genProcs scorp (Seq csp1 csp2) = ("NYfI":scorp)
genProcs scorp (IntC csp1 csp2) = ("NYfI":scorp)
genProcs scorp (ExtC csp1 csp2) = ("NYfI":scorp)
genProcs scorp (Par evts csp1 csp2) = ("NYfI":scorp)
genProcs scorp (Hide evts csp) = ("NYfI":scorp)
genProcs scorp (CSPren rename csp) = ("NYfI":scorp)
genProcs scorp (CSPvar v) = ("NYfI":scorp)
genProcs scorp (CSPmu x csp) = ("NYfI":scorp)

assemble slced scorp  =  assemble' (reverse scorp) ("":slced)

assemble' cspm [] = cspm
assemble' cspm (decl:slced) = assemble' (decl:cspm) slced
\end{code}
