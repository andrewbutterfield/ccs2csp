genProc\section{Generating CSPm}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2020-21

LICENSE: BSD3, see file LICENSE at ccs2csp root
\end{verbatim}
\begin{code}
module CSPm where
import Data.Maybe
import Data.List
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

We generate reversed lists of strings using tail-recursive code.

\begin{code}
generateCSPm :: String -> CSP -> String
generateCSPm name csp
 = let
     lcd = map ("channel "++) $ filter (not . null) $ nub $ chDecls [] csp  -- in reverse order
     rpn = nmdProcs [(name,csp)] csp -- in order
     crp = genProcesses lcd rpn -- in reverse order
   in unlines (banner : "" : reverse crp)
 where banner = "-- CSPm generated by ccs2csp"

genProcesses :: [String] -> [(String,CSP)] -> [String]
genProcesses crp [] = crp
genProcesses crp ((nm,proc):procs)
 = genProcesses (genProc 42 2 ((nm++" ="):"":crp) proc) procs
\end{code}

\subsection{Generate Channel Declarations}

\begin{code}
chDecls :: [String] -> CSP -> [String]
chDecls lcd (CSPpfx evt csp)  =  chDecls (evt:lcd) csp
chDecls lcd (Seq csp1 csp2)   =  chDecls (chDecls lcd csp1) csp2
chDecls lcd (IntC csp1 csp2)  =  chDecls (chDecls lcd csp1) csp2
chDecls lcd (ExtC csp1 csp2)  =  chDecls (chDecls lcd csp1) csp2
chDecls lcd (CSPren rn csp)   =  chDecls (genRNEvts lcd rn) csp
chDecls lcd (Hide evts csp)   =  chDecls (genEvts lcd (S.toList evts)) csp
chDecls lcd (Par evts csp1 csp2)
  =  chDecls (chDecls (genEvts lcd (S.toList evts)) csp1) csp2
chDecls lcd (CSPmu x csp)     =  chDecls lcd csp
chDecls lcd _                 =  lcd

genEvts lcd [] = lcd
genEvts lcd (evt:evts) = genEvts (evt:lcd) evts

genRNEvts lcd = genEvts lcd . map snd
\end{code}

\subsection{Generate Name-Process Pairs}

\begin{code}
nmdProcs :: [(String,CSP)] -> CSP -> [(String,CSP)]
nmdProcs rpn (CSPpfx _ csp)    =  nmdProcs rpn csp
nmdProcs rpn (Seq csp1 csp2)   =  nmdProcs (nmdProcs rpn csp1) csp2
nmdProcs rpn (IntC csp1 csp2)  =  nmdProcs (nmdProcs rpn csp1) csp2
nmdProcs rpn (ExtC csp1 csp2)  =  nmdProcs (nmdProcs rpn csp1) csp2
nmdProcs rpn (CSPren _ csp)    =  nmdProcs rpn csp
nmdProcs rpn (Hide _ csp)      =  nmdProcs rpn csp
nmdProcs rpn (Par _ csp1 csp2) =  nmdProcs (nmdProcs rpn csp1) csp2
nmdProcs rpn (CSPmu x csp)     =  nmdProcs ((x,csp):rpn) csp
nmdProcs rpn _                 =  rpn
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
genProc p i crp Stop = (ind i "STOP":crp)
genProc p i crp Skip = (ind i "SKIP":crp)
genProc p i crp (CSPvar v) = (ind i v:crp)
genProc p i crp (CSPpfx pfx csp)
  = genProc p (i+2) (ind i (pfx ++ " -> "):crp) csp
genProc p i crp (Seq csp1 csp2)  = genInfix p i crp csp1 ";" csp2
genProc p i crp (IntC csp1 csp2) = genInfix p i crp csp1 "|~|" csp2
genProc p i crp (ExtC csp1 csp2) = genInfix p i crp csp1 "[]" csp2
genProc p i crp (Par evts csp1 csp2)
 = genInfix p i crp csp1 parevts csp2
 where
   parevts = "[| {"++levts++"} |]"
   levts = concat $ intersperse "," $ S.toList evts
genProc p i crp (Hide evts csp) = ("Hide-NYfI":crp)
genProc p i crp (CSPren rename csp) = ("CSPren-NYfI":crp)
genProc p i crp (CSPmu x csp) = (ind i x:crp)

genInfix p i crp csp1 opstr csp2
  = let crp1 = genProc p (i+1) (ind i "(":crp) csp1
        crp2 = ind i opstr : crp1
        crp3 = genProc p (i+1) crp2 csp2
    in ind i ")" : crp3
\end{code}

\subsection{Assembly and Indentation.}

\begin{code}


assemble lcd crp  =  assemble' (reverse crp) ("":lcd)

assemble' cspm [] = cspm
assemble' cspm (decl:lcd) = assemble' (decl:cspm) lcd

ind i s  =  replicate i ' ' ++ s
\end{code}
