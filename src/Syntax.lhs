\section{Syntax}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2020

LICENSE: BSD3, see file LICENSE at ccs2csp root
\end{verbatim}
\begin{code}
module Syntax where

import Data.Set (Set)
import qualified Data.Set as S
import Data.List

--import Debug.Trace
--dbg msg x = trace (msg++show x) x
\end{code}

We use CCS notion of ``label'' as basic.
A CSP ``event'' is represented a \texttt{Std} label.
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

showEvent :: IxLab -> String
showEvent (Std ell,i) = ell ++ show i
showEvent (Bar ell,i) = ell ++ show i ++ "-bar"

evtbar :: IxLab -> IxLab
evtbar (ell,i) = (bar ell,i)
\end{code}

\begin{code}
data Prefix
  = T           -- CSS     tau
  | Lbl IxLab   -- CCS     a or a-bar
  | T' String   -- CCStau  t[a|a-bar]
  | Evt String  -- CSP     Event
  deriving (Eq,Ord,Read)

instance Show Prefix where
  show T = "t"
  show (Lbl (Std s,i)) = s ++ show i
  show (Lbl (Bar s,i)) = s ++ show i ++ "-bar"
  show (T' n) = show T ++ "["++n++"|"++n++"-bar]"

pfxbar :: Prefix -> Prefix
pfxbar (Lbl e)  =  Lbl $ evtbar e
pfxbar pfx      =  pfx
\end{code}

\begin{code}
type RenFun = [(String,String)]
\end{code}


We are going to define an abstract syntax that will cover
both CSS (and its variants), as well as CSP.

For CCS we have the syntax:
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
We can re-use the same constructs for:
CCS $0$ and CSP $Stop$;
CCS $|$ and CSP $\parallel$;
and
CCS $+$ and CSP $\sqcap$.
We need an extra choice for:
CSP $Skip$;
CSP $;$;
and
CSP $\Box$.
\begin{code}
data Proc                   -- which? CSS? CSP? both?
  = Zero                    -- both  0, STOP
  | Skip                    -- CSP SKIP
  | Pfx Prefix Proc         -- both, Evt for CSP, others for CCS
  | Seq Proc Proc           -- CSP ;
  | Sum Proc Proc           -- both + |~|
  | Ext Proc Proc           -- CSP []
  | Par [String] Proc Proc  -- both  | |..|
  | Rstr [IxLab] Proc       -- both |' \
  | Ren RenFun Proc         -- both  _[f]  f(_)
  | PVar String             -- both
  | Rec String Proc         -- both
  deriving (Eq,Ord,Read)

comp :: Proc -> Proc -> Proc
comp = Par []

isCCS :: Proc -> Bool
isCCS Skip             =  False
isCCS (Seq _ _)        =  False
isCCS (Ext _ _)        =  False
isCCS (Pfx _ prc)      =  isCCS prc
isCCS (Sum p1 p2)      =  isCCS p1 && isCCS p2
isCCS (Par nms p1 p2)  =  null nms && isCCS p1 && isCCS p2
isCCS (Rstr _ prc)     =  isCCS prc
isCCS (Ren _ prc)      =  isCCS prc
isCCS (Rec _ prc)      =  isCCS prc
isCCS _                =  True  -- Zero, PVar

isCSP :: Proc -> Bool
isCSP (Pfx pfx csp)  =  isCSPPfx pfx && isCSP csp
isCSP (Seq p1 p2)    =  isCSP p1 && isCSP p2
isCSP (Sum p1 p2)    =  isCSP p1 && isCSP p2
isCSP (Ext p1 p2)    =  isCSP p1 && isCSP p2
isCSP (Par _ p1 p2)  =  isCSP p1 && isCSP p2
isCSP (Rstr _ csp)   =  isCSP csp
isCSP (Ren _ csp)    =  isCSP csp
isCSP (Rec _ csp)    =  isCSP csp
isCSP _              =  True  -- Zero, Skip, PVar

isCSPPfx (Lbl (_,None))  =  True
isCSPPfx _               =  False

-- f s2s Zero
-- f s2s Skip
-- f s2s (Pfx pfx prc)
-- f s2s (Seq p1 p2)
-- f s2s (Sum p1 p2)
-- f s2s (Ext p1 p2)
-- f s2s (Par nms p1 p2)
-- f s2s (Rstr es prc)
-- f s2s (Ren s2s prc)
-- f s2s (PVar s)
-- f s2s (Rec s prc)
-- f s2s prc
\end{code}

\begin{code}
renameEvt :: RenFun -> IxLab -> IxLab
renameEvt s2s ((Std s),i)  =  ((Std $ renameStr s s2s),i)
renameEvt s2s ((Bar s),i)  =  ((Bar $ renameStr s s2s),i)

renameStr s []  =  s
renameStr s ((f,t):s2s)
  |  s == f     =  t
  |  otherwise  =  renameStr s s2s
\end{code}

\begin{code}
alf :: Proc -> Set IxLab
alf Zero           =  S.empty
alf Skip           =  S.empty
alf (Pfx pfx prc)  =  alfPfx pfx `S.union` alf prc
alf (Seq p1 p2)     =  alf p1 `S.union` alf p2
alf (Sum p1 p2)     =  alf p1 `S.union` alf p2
alf (Ext p1 p2)     =  alf p1 `S.union` alf p2
alf (Par nms p1 p2) =  alf p1 `S.union` alf p2
alf (Rstr es prc)  =  alf prc
alf (Ren s2s prc)  =  S.map (renameEvt s2s) $ alf prc
alf (PVar s)       =  S.empty
alf (Rec s prc)    =  alf prc

alfPfx (Lbl evt)  =  S.singleton evt
alfPfx _          =  S.empty
\end{code}

\begin{code}
-- Comm+Conc, p44
-- tightest: {Ren,Rstr}, Pfx, Seq, Par, Ext, Sum :loosest
pSum  =    2;  pSum'  = pSum+1
pExt  =    4;  pExt'  = pSum+1
pPar  =    6;  pPar'  = pPar+1
pSeq  =    8;  pSeq'  = pPfx+1
pPfx  =   10;  pPfx'  = pPfx+1
pRen  =   12;  pRen'  = pRen+1
pRstr = pRen;  pRstr' = pRstr+1
\end{code}


\begin{code}
instance Show Proc where

  showsPrec p Zero  = showString "0"

  showsPrec p Skip  = showString "SKIP"

  showsPrec p (Pfx pfx Zero) = showString $ show pfx
  showsPrec p (Pfx pfx prc)
    = showParen (p > pPfx) $
        showString (show pfx) .
        showString "." .
        showsPrec pPfx prc

  showsPrec p (Sum p1 p2) = showsInfix p pSum pSum' showSum [p1,p2]

  showsPrec p (Ext p1 p2) = showsInfix p pExt pExt' showExt [p1,p2]

  showsPrec p (Par nms p1 p2) = showsInfix p pPar pPar' (showPar nms) [p1,p2]

  showsPrec p (Seq p1 p2) = showsInfix p pSeq pSeq' showSeq [p1,p2]

  showsPrec p (Rstr [] prc) = showsPrec p prc
  showsPrec p (Rstr es prc)
    = showParen (p > pRstr) $
        showsPrec pRstr' prc .
        showString "|'" .
        showEvents es

  showsPrec p (Ren s2s prc)
    = showParen (p > pRen) $
        showsPrec pRen' prc .
        showString "[" .
        showRenFun s2s .
        showString "]"

  showsPrec p (PVar ell) = showString ell

  showsPrec p (Rec ell prc)
    = showParen True $
        showString "mu " .
        showString ell .
        showString " @ " .
        showsPrec 0 prc
\end{code}

\begin{code}
showsInfix p pI pI' showI [] = showsPrec p Zero
showsInfix p pI pI' showI [prc] = showsPrec p prc
showsInfix p pI pI' showI (prc:ccss)
    = showParen (p > pI) $
        showsPrec pI' prc .
        showI pI' ccss

showSum p ccss  = showI p " + " ccss

showExt p ccss = showI p " [] " ccss

showPar nms p ccss
  | null nms = showI p " | " ccss
  | otherwise  = showI p (" |"++showNms nms++"| ") ccss

showNms nms = concat $ intersperse "," nms

showSeq p ccss = showI p " ; " ccss

showI p op [] = id
showI p op (prc:ccss)
  = showString op .
    showsPrec p prc .
    showI p op ccss

showEvents [] = id
showEvents [e] = showString $ showEvent e
showEvents (e:es)
  = showString "{" .
    showString (showEvent e) .
    showString "," .
    showEvents' es .
    showString "}"

showEvents' [] = id
showEvents' [e] = showString $ showEvent e
showEvents' (e:es)
  = showString (showEvent e) .
    showString "," .
    showEvents' es

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

Smart Builders:
\begin{code}
csum :: [Proc] -> Proc
csum [] = Zero
csum [prc] = prc
csum (prc:prcs) = Sum prc $ csum prcs

cpar :: [Proc] -> Proc
cpar [] = Zero
cpar [prc] = prc
cpar (prc:prcs) = comp prc $ cpar prcs


rstr :: [IxLab] -> Proc -> Proc
rstr [] prc = prc
rstr es prc = Rstr es prc

endo :: Eq a => [(a,a)] -> a -> a
endo [] a = a
endo ((a1,a2):as) a
 | a == a1    =  a2
 | otherwise  =  endo as a
\end{code}

Summaries:
\begin{code}
prefixesOf :: Proc -> Set Prefix
prefixesOf (Pfx pfx prc)   =  S.singleton pfx `S.union` prefixesOf prc
prefixesOf (Seq p1 p2)      =  prefixesOf p1 `S.union` prefixesOf p2
prefixesOf (Sum p1 p2)      =  prefixesOf p1 `S.union` prefixesOf p2
prefixesOf (Par _ p1 p2)    =  prefixesOf p1 `S.union` prefixesOf p2
prefixesOf (Ext p1 p2)      =  prefixesOf p1 `S.union` prefixesOf p2
prefixesOf (Rstr ss prc)   =  prefixesOf prc
prefixesOf (Ren s2s prc)   =  prefixesOf $ doRename (endo s2s) prc
prefixesOf (Rec s prc)     =  prefixesOf prc
prefixesOf _               =  S.empty
\end{code}


Actions:
\begin{code}
doRename :: (String -> String) -> Proc -> Proc
doRename s2s (Pfx pfx prc)   =  Pfx (renPfx s2s pfx) $ doRename s2s prc
doRename s2s (Sum p1 p2)      =  Sum (doRename s2s p1) (doRename s2s p2)
doRename s2s (Seq p1 p2)      =  Seq (doRename s2s p1) (doRename s2s p2)
doRename s2s (Ext p1 p2)      =  Ext (doRename s2s p1) (doRename s2s p2)
doRename s2s (Par nms p1 p2)  =  Par (map s2s nms)
                                     (doRename s2s p1) (doRename s2s p2)
doRename s2s (Rstr es prc)   =  Rstr (map (renIxLab s2s) es) $ doRename s2s prc
doRename s2s (Ren s2s' prc)  =  doRename s2s (doRename (endo s2s') prc)
doRename s2s (Rec s prc)     =  Rec s $ doRename s2s prc
doRename _   prc             = prc

renPfx :: (String -> String) -> Prefix -> Prefix
renPfx _ T            =  T
renPfx s2s (T' s)     =  T' $ s2s s
renPfx s2s (Lbl ell)  =  Lbl $ renIxLab s2s ell
renPfx s2s (Evt e)    =  Evt $ s2s e

renIxLab :: (String -> String) -> IxLab -> IxLab
renIxLab s2s (ell,i)  =  (renName s2s ell,i)

renName :: (String -> String) -> Label -> Label
renName s2s (Std ell)  =  Std $ s2s ell
renName s2s (Bar ell)  =  Bar $ s2s ell
\end{code}
