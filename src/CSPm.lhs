genProc\section{Generating CSPm}
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

We convert a single CSP process into text using CSPm syntax,
as accepted by FDR4.

\subsection{Generation Top-Level}


\begin{code}
generateCSPm :: String -> CSP -> String
generateCSPm name csp
 = unlines $ assemble (genDecls ["-- Declarations:"] csp)
                      (genProc 0 2 [name ++ " =","-- Process:"] csp)
\end{code}

\subsection{Generate Declarations}

\begin{code}
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
\end{code}

\newpage
\subsection{CSPM Operator Precedence}

We note the following precedence order from
\verb"https://cocotec.io/fdr/manual/cspm/syntax.html#csp-binding-strength".
\begin{verbatim}
 1. Parenthesis (non-associative), Rename (non-associative)
 2. Concat (left-associative)
 3. List Length (left-associative)
 4. * / % (left-associative)
 5. +, - (left-associative)
 6. Comparison (non-associative), Equality Comparison (non-associative)
 7. not (left-associative)
 8. and (left-associative)
 9. or (left-associative)
10. : (non-associative)
11. Dot (right-associative)
12. ?, !, $ (all left-associative)
13. Guarded Expression, Prefix (all right-associative)
14. Sequential Composition (left-associative)
15. Sliding Choice or Timeout (left-associative)
16. Interrupt (left-associative)
17. External Choice (left-associative)
18. Internal Choice (left-associative)
19. Exception, Generalised Parallel, Alphabetised Parallel (all non-associative)
20. Interleave (left-associative)
21. Hide (left-associative)
22. Replicated Operators (non-associative)
23. Double Pattern (non-associative)
24. Let, If (non-associative)
\end{verbatim}

We define binding strength for the operators we support:
\begin{code}
prec :: CSP -> Int
prec (CSPpfx _ _)  =  13 -- rassoc
prec (Seq _ _)     =  14 -- lassoc
prec (IntC _ _)    =  18 -- lassoc
prec (ExtC _ _)    =  17 -- lassoc
prec (Par _ _ _)   =  19 -- nassoc
prec (Hide _ _)    =  21 -- lassoc
prec (CSPren _ _)  =   1 -- nassoc
prec _             =  42 -- whatever!
\end{code}

\subsection{Generate Process}

\begin{code}
genProc :: Int -> Int -> [String] -> CSP -> [String]
genProc p i scorp Stop = (ind i "STOP":scorp)
genProc p i scorp Skip = (ind i "SKIP":scorp)
genProc p i scorp (CSPvar v) = (ind i v:scorp)
genProc p i scorp (CSPpfx pfx csp)
  = genProc p (i+2) (ind i (pfx ++ " -> "):scorp) csp
genProc p i scorp (Seq csp1 csp2) = ("NYfI":scorp)
genProc p i scorp (IntC csp1 csp2) = ("NYfI":scorp)
genProc p i scorp (ExtC csp1 csp2) = ("NYfI":scorp)
genProc p i scorp (Par evts csp1 csp2) = ("NYfI":scorp)
genProc p i scorp (Hide evts csp) = ("NYfI":scorp)
genProc p i scorp (CSPren rename csp) = ("NYfI":scorp)
genProc p i scorp (CSPmu x csp) = ("NYfI":scorp)
\end{code}

\subsection{Assembly and Indentation.}

\begin{code}


assemble slced scorp  =  assemble' (reverse scorp) ("":slced)

assemble' cspm [] = cspm
assemble' cspm (decl:slced) = assemble' (decl:cspm) slced

ind i s  =  replicate i ' ' ++ s
\end{code}
