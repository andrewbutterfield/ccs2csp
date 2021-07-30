\section{Syntax}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2020-21

LICENSE: BSD3, see file LICENSE at ccs2csp root
\end{verbatim}
\begin{code}
{-# LANGUAGE CPP #-}
module Syntax where

import Data.Set (Set)
import qualified Data.Set as S
import Data.List

--import Debug.Trace
--dbg msg x = trace (msg++show x) x
\end{code}

We have a meeting of two worlds here,
CSP and CCS.

\subsection{Calculus of Communicating Systems}

\subsubsection{CCS Syntax}

For CCS, we define start by defining labels:
\begin{code}
data Label = Std String | Bar String deriving (Eq,Ord,Read)

instance Show Label where
  show (Std s)  =  s
  show (Bar s)  =  s ++ "-bar"

root :: Label -> String
root (Std s)  =  s
root (Bar s)  =  s

bar :: Label -> Label
bar (Std s)  =  Bar s
bar (Bar s)  =  Std s
\end{code}

We then introduce a representation of possibly having up to two indices.
\begin{code}
data Index
  = None
  | One Int
  | Two Int Int
  deriving (Eq,Ord,Read)

instance Show Index where
  show None       =  ""
  show (One i)    =  show i
  show (Two i j)  =  show (One i) ++ ";" ++ show (One j)
\end{code}

Our CCS ``labels'' are indexable.
\begin{code}
type IxLab = (Label, Index)

event :: Label -> IxLab
event ell = (ell,None)

ievent :: Label -> Int -> IxLab
ievent ell i = (ell,One i)

i2event :: Label -> Int -> Int -> IxLab
i2event ell i j -- reorder indices so first <= second
  | i > j      =  (ell,Two j i)
  | otherwise  =  (ell,Two i j)

showIxLab :: IxLab -> String
showIxLab (Std ell,i) = ell ++ show i
showIxLab (Bar ell,i) = ell ++ show i ++ "-bar"

ixlbar :: IxLab -> IxLab
ixlbar (ell,i) = (bar ell,i)
\end{code}

A CCS prefix is either a tau ($\tau$),
or a (possibly indexed) label ($\ell$,$\bar\ell$).
For CCSTau, we also add (possibly indexed) visible synchronisations
($\tau[a|\bar a]$).
\begin{code}
data Event
  = T                 -- CSS tau
  | Lbl IxLab         -- CCS a or a-bar
  | T' String Index   -- CCStau  t[a|a-bar]
  deriving (Eq,Ord,Read)

isLbl :: Event -> Bool
isLbl (Lbl _)  =  True
isLbl _        =  False

instance Show Event where
  show T                =  "t"
  show (Lbl (Std s,i))  =  s ++ show i
  show (Lbl (Bar s,i))  =  s ++ show i ++ "-bar"
  show (T' n i)           =  show T ++ show i++"["++n++"|"++n++"-bar]"

pfxbar :: Event -> Event
pfxbar (Lbl e)  =  Lbl $ ixlbar e
pfxbar pfx      =  pfx

lbl2tau :: Event -> Event
lbl2tau (Lbl (Std s,i))  =  T' s i
lbl2tau (Lbl (Bar s,i))  =  T' s i
lbl2tau pfx              =  pfx
\end{code}

\begin{code}
type RenPairs = [(String,String)] -- (from,to)
\end{code}

For CCS we have the syntax%
\footnote{
Note that we use $\restrict$ to represent CCS restriction here,
to avoid confusion with $\hide$, which denotes CSP's hide operator.
}:
\begin{eqnarray*}
  P,Q &::=&  0
             \mid \alpha.P
             \mid P|Q
             \mid P+Q
             \mid P\restrict L
             \mid P[f]
             \mid X
             \mid \mu X \bullet P
\end{eqnarray*}
For CCS$\tau$ we have the syntax:
\begin{eqnarray*}
  P,Q &::=&  0
             \mid \alpha.P
             \mid P+Q
             \mid P\restrict L
             \mid P[f]
             \mid X
             \mid \mu X \bullet P
             \mid P|_T Q
             \mid P \hide_T \alpha
\end{eqnarray*}
\begin{code}
data CCS -- and CCStau
  = Zero
  | CCSpfx Event CCS
  | Sum CCS CCS
  | Comp CCS CCS
  | Rstr (Set IxLab) CCS
  | CCSren RenPairs CCS
  | CCSvar String
  | CCSmu String CCS
  | CCStauPar CCS CCS             -- CCStau
  | CCStauHide (Set Event) CCS  -- CCStau
  deriving (Eq,Ord,Read)
type CCSTau = CCS
\end{code}

\subsubsection{CCS Renaming}

\begin{code}
renameEvt :: RenPairs -> Event -> Event
renameEvt _   T          =  T
renameEvt s2s (T' s i)     =  T' (renameStr s s2s) i
renameEvt s2s (Lbl ell)  =  Lbl $ renameIxL s2s ell

renameIxL :: RenPairs -> IxLab -> IxLab
renameIxL s2s ((Std s),i)  =  ((Std $ renameStr s s2s),i)
renameIxL s2s ((Bar s),i)  =  ((Bar $ renameStr s s2s),i)
\end{code}

\subsubsection{CCS Alphabets}

\begin{code}
alf :: CCS -> Set Event
alf (CCSpfx pfx ccs)       =  S.singleton pfx `S.union` alf ccs
alf (Sum p1 p2)            =  alf p1 `S.union` alf p2
alf (Comp p1 p2)           =  alf p1 `S.union` alf p2
alf (Rstr es ccs)          =  alf ccs S.\\ S.map Lbl es
alf (CCSren s2s ccs)       =  S.map (renameEvt s2s) $ alf ccs
alf (CCSmu s ccs)          =  alf ccs
alf (CCStauPar p1 p2)      =  alf p1 `S.union` alf p2
alf (CCStauHide pfxs ccs)  =  alf ccs S.\\ pfxs
alf _                      =  S.empty

alfPfx (Lbl evt)  =  S.singleton evt
alfPfx _          =  S.empty
\end{code}

\subsubsection{CCS Printing}

CCS Symbols:
\begin{code}
#ifdef mingw32_HOST_OS
restrictSym  =  " |' "
#endif
#ifndef mingw32_HOST_OS
restrictSym  =  " \x21be "
#endif
\end{code}


\begin{code}
instance Show CCS where

  showsPrec p Zero  = showString "0"

  showsPrec p (CCSpfx pfx Zero) = showString $ show pfx
  showsPrec p (CCSpfx pfx ccs)
    = showParen (p > pPfx) $
        showString (show pfx) .
        showString "." .
        showsPrec pPfx ccs

  showsPrec p (Sum p1 p2) = showsInfix p pSum pSum' showSum [p1,p2]

  showsPrec p (Comp p1 p2) = showsInfix p pComp pComp' showComp [p1,p2]

  showsPrec p (CCStauPar p1 p2) = showsInfix p pComp pComp' showParTau [p1,p2]

  showsPrec p (Rstr es ccs)
   | S.null es  =  showsPrec p ccs
   | otherwise  = showParen (p > pRstr) $
                    showsPrec pRstr' ccs .
                    showString restrictSym .
                    showSet showIxLab (S.toList es)

  showsPrec p (CCStauHide pfxs ccs)
   | S.null pfxs  =  showsPrec p ccs
   | otherwise    = showParen (p > pRstr) $
                      showsPrec pRstr' ccs .
                      showString " \\T " .
                      showSet show (S.toList pfxs)

  showsPrec p (CCSren s2s ccs)
    = showParen (p > pRen) $
        showsPrec pRen' ccs .
        showString "[" .
        showRenFun s2s .
        showString "]"

  showsPrec p (CCSvar v) = showString v

  showsPrec p (CCSmu nm ccs)
    = showParen True $
        showString muSym .
        showString nm .
        showString bulletSym .
        showsPrec 0 ccs

showSum p ccss  = showI p " + " ccss

showComp p ccss  = showI p " | " ccss

showParTau p ccss  = showI p " |T " ccss
\end{code}


\subsubsection{CCS Smart Builders}

\begin{code}
cfold :: (CCS -> CCS -> CCS) -> [CCS] -> CCS
cfold _ [] = Zero
cfold _ [ccs] = ccs
cfold op (ccs:ccss) = ccs `op` cfold op ccss

csum :: [CCS] -> CCS
csum = cfold Sum

cpar :: [CCS] -> CCS
cpar = cfold Comp

ctpar :: [CCSTau] -> CCSTau
ctpar = cfold CCStauPar


rstr :: [IxLab] -> CCS -> CCS
rstr [] ccs = ccs
rstr es ccs = Rstr (S.fromList es) ccs
\end{code}


\subsubsection{CCS Queries}

\begin{code}
prefixesOf :: CCS -> Set Event
prefixesOf (CCSpfx pfx ccs)     =  S.singleton pfx `S.union` prefixesOf ccs
prefixesOf (Sum p1 p2)          =  prefixesOf p1 `S.union` prefixesOf p2
prefixesOf (Comp p1 p2)         =  prefixesOf p1 `S.union` prefixesOf p2
prefixesOf (Rstr ss ccs)        =  prefixesOf ccs
prefixesOf (CCSren s2s ccs)     =  prefixesOf $ doRename (endo s2s) ccs
prefixesOf (CCSmu s ccs)        =  prefixesOf ccs
prefixesOf (CCStauPar p1 p2)    =  prefixesOf p1 `S.union` prefixesOf p2
prefixesOf (CCStauHide ss ccs)  =  prefixesOf ccs
prefixesOf _                    =  S.empty
\end{code}

\subsubsection{CCS Actions}


\begin{code}
doRename :: (String -> String) -> CCS -> CCS
doRename s2s (CCSpfx pfx ccs)   =  CCSpfx (renPfx s2s pfx) $ doRename s2s ccs
doRename s2s (Sum p1 p2)        =  Sum (doRename s2s p1) (doRename s2s p2)
doRename s2s (Comp p1 p2)       =  Comp (doRename s2s p1) (doRename s2s p2)
doRename s2s (Rstr es ccs)
  =  Rstr (S.map (renIxLab s2s) es) $ doRename s2s ccs
doRename s2s (CCSren s2s' ccs)  =  doRename s2s (doRename (endo s2s') ccs)
doRename s2s (CCSmu s ccs)      =  CCSmu s $ doRename s2s ccs
doRename s2s (CCStauPar p1 p2)  =  CCStauPar (doRename s2s p1) (doRename s2s p2)
doRename s2s (CCStauHide pfxs ccs)
  =  CCStauHide (S.map (renPfx s2s) pfxs) $ doRename s2s ccs
doRename _   ccs             = ccs

renPfx :: (String -> String) -> Event -> Event
renPfx _ T            =  T
renPfx s2s (T' s i)     =  T' (s2s s) i
renPfx s2s (Lbl ell)  =  Lbl $ renIxLab s2s ell

renIxLab :: (String -> String) -> IxLab -> IxLab
renIxLab s2s (ell,i)  =  (renName s2s ell,i)

renName :: (String -> String) -> Label -> Label
renName s2s (Std ell)  =  Std $ s2s ell
renName s2s (Bar ell)  =  Bar $ s2s ell
\end{code}

\newpage
\subsection{Communicating Sequential Processes}

\subsubsection{CSP Syntax}


For CSP we have the syntax:
\begin{eqnarray*}
  P,Q &::=&  Stop
             \mid Skip
             \mid a \then P
             \mid P;Q
             \mid P \parallel_A Q
             \mid P \sqcap Q
             \mid P \Box Q
             \mid P\hide H
             \mid f(P)
             \mid X
             \mid \mu X \bullet P
\end{eqnarray*}
\begin{code}
data CSP
  = Stop
  | Skip
  | CSPpfx Event CSP
  | Seq CSP CSP
  | IntC CSP CSP
  | ExtC CSP CSP
  | Par (Set Event) CSP CSP
  | Hide (Set Event) CSP
  | CSPren RenPairs CSP
  | CSPvar String
  | CSPmu String CSP
  deriving (Eq,Ord,Read)

(|~|)  =  IntC
(<>)   =  ExtC -- Can't use [], or '[' or ']' in any way
($>)   =  Seq  -- Can't use ; in any way
($\)   =  Hide -- Can't use \ by itself
par              =  Par  . S.fromList
hide             =  Hide . S.fromList
pfx a csp        =  CSPpfx a csp
pfxs [] csp      =  csp
pfxs (a:as) csp  =  pfx a $ pfxs as csp
\end{code}


\subsubsection{CSP Alphabets}

\begin{code}
alpha :: CSP -> Set Event
alpha (CSPpfx pfx csp)   =  S.singleton pfx `S.union` alpha csp
alpha (Seq csp1 csp2)    =  alpha csp1 `S.union` alpha csp2
alpha (IntC csp1 csp2)   =  alpha csp1 `S.union` alpha csp2
alpha (ExtC csp1 csp2)   =  alpha csp1 `S.union` alpha csp2
alpha (Par _ csp1 csp2)  =  alpha csp1 `S.union` alpha csp2
alpha (Hide _ csp)       =  alpha csp
alpha (CSPren s2s csp)   =  S.map (renameEvt s2s) $ alpha csp
alpha (CSPmu _ csp)      =  alpha csp
alpha _                  =  S.empty
\end{code}

\subsubsection{CSP Printing}

CSP Symbols:
\begin{code}
#ifdef mingw32_HOST_OS
thenSym  =  " -> "
ndcSym   =  " |~| "
extCSym  =  " [] "
#endif
#ifndef mingw32_HOST_OS
thenSym  =  " \x2192 "
ndcSym   =  " \x2a05 "
extCSym  =  " \x25a1 "
#endif
\end{code}

\begin{code}
instance Show CSP where

  showsPrec p Stop  = showString "Stop"

  showsPrec p Skip  = showString "Skip"

  showsPrec p (CSPpfx pfx Stop) = showString $ show pfx
  showsPrec p (CSPpfx pfx csp)
    = showParen (p > pPfx) $
        showString (show pfx) .
        showString thenSym .
        showsPrec pPfx csp

  showsPrec p (IntC p1 p2) = showsInfix p pInt pInt' showIntC [p1,p2]

  showsPrec p (ExtC p1 p2) = showsInfix p pExt pExt' showExtC [p1,p2]

  showsPrec p (Par nms p1 p2)
    | S.null nms  =  showsInfix p pPar pPar' showPar0 [p1,p2]
    | otherwise   =  showsInfix p pPar pPar' (showPar nms) [p1,p2]

  showsPrec p (Seq p1 p2) = showsInfix p pSeq pSeq' showSeq [p1,p2]

  showsPrec p (Hide es ccs)
   | S.null es  =  showsPrec p ccs
   | otherwise  = showParen (p > pRstr) $
                    showsPrec pRstr' ccs .
                    showString "\\" .
                    showSet show (S.toList es)

  showsPrec p (CSPren s2s csp)
    = showParen (p > pRen) $
        showsPrec pRen' csp .
        showString "[" .
        showRenFun s2s .
        showString "]"

  showsPrec p (CSPvar v) = showString v

  showsPrec p (CSPmu nm csp)
    = showParen True $
        showString muSym .
        showString nm .
        showString bulletSym .
        showsPrec 0 csp

showIntC p csps  = showI p ndcSym csps

showExtC p csps  = showI p extCSym csps

-- || is \x2225 in unicode  ||| is \x2af4
showPar0 p csps  = showI p " ||| " csps
showPar nms p csps  = showI p (" |"++showEvt nms++"| ") csps

showEvt nms = concat $ intersperse "," $ map show $ S.toList nms

showSeq p csps = showI p " ; " csps
\end{code}

% % Uncomment only when content available
% \subsubsection{CSP Smart Builders}
%
% \subsubsection{CSP Queries}
%
% \subsubsection{CSP Actions}




\subsection{Shared CCS/CSP Functions}

\subsubsection{CCS/CSP Renaming}

\begin{code}
renameStr :: String -> RenPairs -> String
renameStr s []  =  s
renameStr s ((f,t):s2s)
  |  s == f     =  t
  |  otherwise  =  renameStr s s2s

endo :: Eq a => [(a,a)] -> a -> a
endo [] a = a
endo ((a1,a2):as) a
 | a == a1    =  a2
 | otherwise  =  endo as a
\end{code}

\subsubsection{CCS/CSP Printing}

Common Symbols:
\begin{code}
#ifdef mingw32_HOST_OS
muSym      =  "mu "
bulletSym  =  " @ "
#endif
#ifndef mingw32_HOST_OS
muSym      =  "\x03bc "
bulletSym  =  " \x2022 "
#endif
\end{code}

\begin{code}
showsInfix p pI pI' showI [] = showsPrec p Zero
showsInfix p pI pI' showI [ccs] = showsPrec p ccs
showsInfix p pI pI' showI (ccs:ccss)
    = showParen (p > pI) $
        showsPrec pI' ccs .
        showI pI' ccss

showI p op [] = id
showI p op (ccs:ccss)
  = showString op .
    showsPrec p ccs .
    showI p op ccss

showSet showElem [] = id
showSet showElem [e] = showString $ showElem e
showSet showElem (e:es)
  = showString "{" .
    showString (showElem e) .
    showString "," .
    showSet' showElem es .
    showString "}"

showSet' showElem [] = id
showSet' showElem [e] = showString $ showElem e
showSet' showElem (e:es)
  = showString (showElem e) .
    showString "," .
    showSet showElem es

showRenFun [] = showString ""
showRenFun [ee] = showEE ee
showRenFun (ee:ees)
  = showEE ee .
    showString "," .
    showRenFun ees

showEE (e1,e2) = showString e1 .
                 showString "/" .
                 showString e2
\end{code}

Precedences:
\begin{code}
-- Comm+Conc, p44
-- tightest: {CCSren,Rstr}, CCSpfx, Seq, Comp, Ext, Sum :loosest
pSum  =    2;  pSum'  = pSum+1
pInt  =    2;  pInt'  = pInt+1
pExt  =    4;  pExt'  = pSum+1
pComp =    6;  pComp' = pComp+1
pPar  =    6;  pPar'  = pPar+1
pSeq  =    8;  pSeq'  = pPfx+1
pPfx  =   10;  pPfx'  = pPfx+1
pRen  =   12;  pRen'  = pRen+1
pRstr = pRen;  pRstr' = pRstr+1
pHide = pRen;  pHide' = pHide+1
\end{code}
