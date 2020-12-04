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
data Process
  = Zero                    -- both  0, STOP
  | Skip                    -- CSP SKIP
  | Pfx Prefix Process      -- both, Evt for CSP, others for CCS
  | Seq [Process]           -- CSP ;
  | Sum [Process]           -- both + |~|
  | Ext [Process]           -- CSP []
  | Par [String] [Process]  -- both  | |..|
  | Rstr [IxLab] Process    -- both |' \
  | Ren RenFun Process      -- both  _[f]  f(_)
  | PVar String             -- both
  | Rec String Process      -- both
  deriving (Eq,Ord,Read)

isCCS :: Process -> Bool
isCCS Skip            =  False
isCCS (Seq _)         =  False
isCCS (Ext _)         =  False
isCCS (Pfx _ ccs)     =  isCCS ccs
isCCS (Sum ccss)      =  all isCCS ccss
isCCS (Par nms ccss)  =  null nms && all isCCS ccss
isCCS (Rstr _ ccs)    =  isCCS ccs
isCCS (Ren _ ccs)     =  isCCS ccs
isCCS (Rec _ ccs)     =  isCCS ccs
isCCS _               =  True  -- Zero, PVar

isCSP :: Process -> Bool
isCSP (Pfx pfx ccs)  =  isCSPPfx pfx && isCSP ccs
isCSP (Seq ccss)     =  all isCSP ccss
isCSP (Sum ccss)     =  all isCSP ccss
isCSP (Ext ccss)     =  all isCSP ccss
isCSP (Par _ ccss)   =  all isCSP ccss
isCSP (Rstr _ ccs)   =  isCSP ccs
isCSP (Ren _ ccs)    =  isCSP ccs
isCSP (Rec _ ccs)    =  isCSP ccs
isCSP _              =  True  -- Zero, Skip, PVar

isCSPPfx (Lbl (_,None))  =  True
isCSPPfx _               =  False

-- f s2s Zero
-- f s2s Skip
-- f s2s (Pfx pfx ccs)
-- f s2s (Seq ccss)
-- f s2s (Sum ccss)
-- f s2s (Ext ccss)
-- f s2s (Par nms ccss)
-- f s2s (Rstr es ccs)
-- f s2s (Ren s2s ccs)
-- f s2s (PVar s)
-- f s2s (Rec s ccs)
-- f s2s ccs
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
alf :: Process -> Set IxLab
alf Zero           =  S.empty
alf Skip           =  S.empty
alf (Pfx pfx ccs)  =  alfPfx pfx `S.union` alf ccs
alf (Seq ccss)     =  S.unions $ map alf ccss
alf (Sum ccss)     =  S.unions $ map alf ccss
alf (Ext ccss)     =  S.unions $ map alf ccss
alf (Par nms ccss) =  S.unions $ map alf ccss
alf (Rstr es ccs)  =  alf ccs
alf (Ren s2s ccs)  =  S.map (renameEvt s2s) $ alf ccs
alf (PVar s)       =  S.empty
alf (Rec s ccs)    =  alf ccs

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
instance Show Process where

  showsPrec p Zero  = showString "0"

  showsPrec p Skip  = showString "SKIP"

  showsPrec p (Pfx pfx Zero) = showString $ show pfx
  showsPrec p (Pfx pfx ccs)
    = showParen (p > pPfx) $
        showString (show pfx) .
        showString "." .
        showsPrec pPfx ccs

  showsPrec p (Sum ccss) = showsInfix p pSum pSum' showSum ccss

  showsPrec p (Ext ccss) = showsInfix p pExt pExt' showExt ccss

  showsPrec p (Par nms ccss) = showsInfix p pPar pPar' (showPar nms) ccss

  showsPrec p (Seq ccss) = showsInfix p pSeq pSeq' showSeq ccss

  showsPrec p (Rstr [] ccs) = showsPrec p ccs
  showsPrec p (Rstr es ccs)
    = showParen (p > pRstr) $
        showsPrec pRstr' ccs .
        showString "|'" .
        showEvents es

  showsPrec p (Ren s2s ccs)
    = showParen (p > pRen) $
        showsPrec pRen' ccs .
        showString "[" .
        showRenFun s2s .
        showString "]"

  showsPrec p (PVar ell) = showString ell

  showsPrec p (Rec ell ccs)
    = showParen True $
        showString "mu " .
        showString ell .
        showString " @ " .
        showsPrec 0 ccs
\end{code}

\begin{code}
showsInfix p pI pI' showI [] = showsPrec p Zero
showsInfix p pI pI' showI [ccs] = showsPrec p ccs
showsInfix p pI pI' showI (ccs:ccss)
    = showParen (p > pI) $
        showsPrec pI' ccs .
        showI pI' ccss

showSum p ccss  = showI p " + " ccss

showExt p ccss = showI p " [] " ccss

showPar nms p ccss
  | null nms = showI p " | " ccss
  | otherwise  = showI p (" |"++showNms nms++"| ") ccss

showNms nms = concat $ intersperse "," nms

showSeq p ccss = showI p " ; " ccss

showI p op [] = id
showI p op (ccs:ccss)
  = showString op .
    showsPrec p ccs .
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
csum :: [Process] -> Process
csum [] = Zero
csum [ccs] = ccs
csum ccss = Sum ccss

cpar :: [Process] -> Process
cpar [] = Zero
cpar [ccs] = ccs
cpar ccss = Par [] ccss


rstr :: [IxLab] -> Process -> Process
rstr [] ccs = ccs
rstr es ccs = Rstr es ccs

endo :: Eq a => [(a,a)] -> a -> a
endo [] a = a
endo ((a1,a2):as) a
 | a == a1    =  a2
 | otherwise  =  endo as a
\end{code}

Summaries:
\begin{code}
prefixesOf :: Process -> Set Prefix
prefixesOf (Pfx pfx ccs)   =  S.singleton pfx `S.union` prefixesOf ccs
prefixesOf (Seq ccss)      =  S.unions $ map prefixesOf $ ccss
prefixesOf (Sum ccss)      =  S.unions $ map prefixesOf $ ccss
prefixesOf (Par _ ccss)    =  S.unions $ map prefixesOf $ ccss
prefixesOf (Ext ccss)      =  S.unions $ map prefixesOf $ ccss
prefixesOf (Rstr ss ccs)   =  prefixesOf ccs
prefixesOf (Ren s2s ccs)   =  prefixesOf $ doRename (endo s2s) ccs
prefixesOf (Rec s ccs)     =  prefixesOf ccs
prefixesOf _               =  S.empty
\end{code}


Actions:
\begin{code}
doRename :: (String -> String) -> Process -> Process
doRename s2s (Pfx pfx ccs)   =  Pfx (renPfx s2s pfx) $ doRename s2s ccs
doRename s2s (Sum ccss)      =  Sum $ map (doRename s2s) ccss
doRename s2s (Seq ccss)      =  Seq $ map (doRename s2s) ccss
doRename s2s (Ext ccss)      =  Ext $ map (doRename s2s) ccss
doRename s2s (Par nms ccss)  =  Par (map s2s nms) $ map (doRename s2s) ccss
doRename s2s (Rstr es ccs)   =  Rstr (map (renIxLab s2s) es) $ doRename s2s ccs
doRename s2s (Ren s2s' ccs)  =  doRename s2s (doRename (endo s2s') ccs)
doRename s2s (Rec s ccs)     =  Rec s $ doRename s2s ccs
doRename _   ccs             = ccs

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
