\section{Syntax}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Syntax where

import Data.Set (Set)
import qualified Data.Set as S

--import Debug.Trace
--dbg msg x = trace (msg++show x) x
\end{code}

We making barring part of a name:
\begin{code}
data Name = Std String | Bar String deriving (Eq,Ord,Read)

instance Show Name where
  show (Std s)  =  s
  show (Bar s)  =  s ++ "-bar"

bar :: Name -> Name
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
type Event = (Name, Index)

event :: Name -> Event
event nm = (nm,None)

ievent :: Name -> Int -> Event
ievent nm i = (nm,One i)

i2event :: Name -> Int -> Int -> Event
i2event nm i j -- reorder indices so first <= second
  | i > j      =  (nm,Two j i)
  | otherwise  =  (nm,Two i j)

showEvent :: Event -> String
showEvent (nm,i) = show nm ++ show i

evtbar :: Event -> Event
evtbar (nm,i) = (bar nm,i)
\end{code}

\begin{code}
data Prefix
  = T          -- tau
  | Evt Event  -- a or a-bar
  | T' String   -- t[a|a-bar]
  deriving (Eq,Ord,Read)

instance Show Prefix where
  show T = "t"
  show (Evt (Std s,i)) = s ++ show i
  show (Evt (Bar s,i)) = s ++ show i ++ "-bar"
  show (T' n) = show T ++ "["++n++"|"++n++"-bar]"

pfxbar :: Prefix -> Prefix
pfxbar (Evt e)  =  Evt $ evtbar e
pfxbar pfx      =  pfx
\end{code}

\begin{code}
type RenFun = [(String,String)]
\end{code}

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
\begin{code}
data CCS
  = Zero
  | Pfx Prefix CCS
  | Sum [CCS]
  | Par [CCS]
  | Rstr [Event] CCS
  | Ren RenFun CCS
  | PVar String
  | Rec String CCS
  deriving (Eq,Ord,Read)

-- f s2s Zero
-- f s2s (Pfx pfx ccs)
-- f s2s (Sum ccss)
-- f s2s (Par ccss)
-- f s2s (Rstr es ccs)
-- f s2s (Ren s2s ccs)
-- f s2s (PVar s)
-- f s2s (Rec s ccs)
-- f s2s ccs
\end{code}

\begin{code}
renameEvt :: RenFun -> Event -> Event
renameEvt s2s ((Std s),i)  =  ((Std $ renameStr s s2s),i)
renameEvt s2s ((Bar s),i)  =  ((Bar $ renameStr s s2s),i)

renameStr s []  =  s
renameStr s ((f,t):s2s)
  |  s == f     =  t
  |  otherwise  =  renameStr s s2s
\end{code}

\begin{code}
alf :: CCS -> Set Event
alf Zero           =  S.empty
alf (Pfx pfx ccs)  =  alfPfx pfx `S.union` alf ccs
alf (Sum ccss)     =  S.unions $ map alf ccss
alf (Par ccss)     =  S.unions $ map alf ccss
alf (Rstr es ccs)  =  alf ccs S.\\ S.fromList es  -- is this right?
alf (Ren s2s ccs)  =  S.map (renameEvt s2s) $ alf ccs
alf (PVar s)       =  S.empty
alf (Rec s ccs)    =  alf ccs

alfPfx (Evt evt)  =  S.singleton evt
alfPfx _          =  S.empty
\end{code}


\begin{code}
instance Show CCS where
  showsPrec p Zero  = showString "0"
  showsPrec p (Pfx pfx Zero) = showString $ show pfx
  showsPrec p (Pfx pfx ccs)
    = showParen (p > pPfx) $
        showString (show pfx) .
        showString "." .
        showsPrec pPfx ccs
  showsPrec p (Sum []) = showsPrec p Zero
  showsPrec p (Sum [ccs]) = showsPrec p ccs
  showsPrec p (Sum (ccs:ccss))
    = showParen (p > pSum) $
        showsPrec pSum' ccs .
        showSum pSum' ccss
  showsPrec p (Par []) = showsPrec p Zero
  showsPrec p (Par [ccs]) = showsPrec p ccs
  showsPrec p (Par (ccs:ccss))
    = showParen (p > pPar) $
        showsPrec pPar' ccs .
        showPar pPar' ccss
  showsPrec p (Rstr es ccs)
    = showParen (p > pRstr) $
        showsPrec pRstr' ccs .
        showString "\\" .
        showEvents es
  showsPrec p (Ren s2s ccs)
    = showParen (p > pRen) $
        showsPrec pRen' ccs .
        showString "[" .
        showRenFun s2s .
        showString "]"
  showsPrec p (PVar nm) = showString nm
  showsPrec p (Rec nm ccs)
    = showParen True $
        showString "mu " .
        showString nm .
        showString " @ " .
        showsPrec 0 ccs
\end{code}

\begin{code}
-- Comm+Conc, p44
-- tightest: {Ren,Rstr}, Pfx, Par, Sum :loosest

pSum = 2; pSum' = pSum+1
pPar = 4; pPar' = pPar+1
pPfx = 6; pPfx' = pPfx+1
pRen = 8; pRen' = pRen+1
pRstr = pRen; pRstr' = pRstr+1

showSum p [] = id
showSum p (ccs:ccss)
  = showString " + " .
    showsPrec p ccs .
    showSum p ccss

showPar p [] = id
showPar p (ccs:ccss)
  = showString " | " .
    showsPrec p ccs .
    showPar p ccss

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
csum :: [CCS] -> CCS
csum [] = Zero
csum [ccs] = ccs
csum ccss = Sum ccss

cpar :: [CCS] -> CCS
cpar [] = Zero
cpar [ccs] = ccs
cpar ccss = Par ccss


rstr :: [Event] -> CCS -> CCS
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
prefixesOf :: CCS -> Set Prefix
prefixesOf (Pfx pfx ccs)   =  S.singleton pfx `S.union` prefixesOf ccs
prefixesOf (Sum ccss)      =  S.unions $ map prefixesOf $ ccss
prefixesOf (Par ccss)      =  S.unions $ map prefixesOf $ ccss
prefixesOf (Rstr ss ccs)   =  prefixesOf ccs
prefixesOf (Ren s2s ccs)   =  prefixesOf $ doRename (endo s2s) ccs
prefixesOf (Rec s ccs)     =  prefixesOf ccs
prefixesOf _               =  S.empty
\end{code}


Actions:
\begin{code}
doRename :: (String -> String) -> CCS -> CCS
doRename s2s (Pfx pfx ccs)   =  Pfx (renPfx s2s pfx) $ doRename s2s ccs
doRename s2s (Sum ccss)      =  Sum $ map (doRename s2s) ccss
doRename s2s (Par ccss)      =  Par $ map (doRename s2s) ccss
doRename s2s (Rstr es ccs)   =  Rstr (map (renEvent s2s) es) $ doRename s2s ccs
doRename s2s (Ren s2s' ccs)  =  doRename s2s (doRename (endo s2s') ccs)
doRename s2s (Rec s ccs)     =  Rec s $ doRename s2s ccs
doRename _   ccs             = ccs

renPfx :: (String -> String) -> Prefix -> Prefix
renPfx _ T          =  T
renPfx s2s (T' s)   =  T' $ s2s s
renPfx s2s (Evt e)  =  Evt $ renEvent s2s e

renEvent :: (String -> String) -> Event -> Event
renEvent s2s (nm,i)  =  (renName s2s nm,i)

renName :: (String -> String) -> Name -> Name
renName s2s (Std nm)  =  Std $ s2s nm
renName s2s (Bar nm)  =  Bar $ s2s nm
\end{code}
