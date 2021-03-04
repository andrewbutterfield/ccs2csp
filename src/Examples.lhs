\section{Examples}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Examples where

import Control.Monad
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Syntax
import Translate
import Semantics

--import Debug.Trace
--dbg msg x = trace (msg++show x) x
\end{code}

Milners ``Comms and Conc'' book.
\begin{code}
  -- p44  R+a.P|b.Q\L = R+((a.P)|(b.(Q\L)))
na = Std "a" ; ea = (na,None);  a = Lbl ea
nb = Std "b" ; b = Lbl (nb,None)
r = PVar "R"
p = PVar "P"
ell = (Std "L",None)
q = PVar "Q"
cc44 = csum [ r
            , cpar [ Pfx a p
                   , Pfx b (Rstr [ell] q)
                   ]
            ]
\end{code}

Examples from Gerard's document, v17.
\begin{code}
-- v17, 4.1.2, p18
s = PVar "S"
abar = pfxbar a
x18 = Rstr [ea] $ cpar [Pfx a p, cpar [Pfx abar q, cpar [Pfx abar r, Pfx abar s]]]

--v17, 4.1.2., p19
xl19 = cpar [Pfx a Zero, Pfx abar Zero]
ta = T' "a"
a0 = Pfx a Zero; abar0 = Pfx abar Zero
b0 = Pfx b Zero; bbar0 = Pfx bbar Zero
xr19 = csum [Pfx a $ abar0, csum [Pfx abar $ a0, Pfx ta Zero]]

--v17, 4.1.2, p19 bottom
xb19 = cpar [ Pfx a (cpar [a0,a0,a0,a0])
            , abar0
            , Pfx abar (cpar [a0,a0])
            ]
\end{code}

\newpage
Examples from Vasileios MS Team whiteboard, 24th Sep.
\begin{code}
-- a.b.0 | b-bar.a-bar.0
bbar = pfxbar b
xms1 = cpar [ Pfx a (Pfx b Zero), Pfx bbar (Pfx abar Zero)]

-- a.b.(abar.0|b.0) | bbar.abar.0
xms2 = cpar [ Pfx a (Pfx b (cpar [ Pfx abar Zero, Pfx b Zero]))
              , Pfx bbar (Pfx abar Zero)
              ]
-- manually laid out below -- need better pretty-printing
-- ( (   a0.(   b1.((a-bar2 + a-bar0;2) | (b3 + b3;4))
--          + b1;4.((a-bar2 + a-bar0;2) | (b3 + b3;4))
--          )
--   + a0;2.(   b1.((a-bar2 + a-bar0;2) | (b3 + b3;4))
--          + b1;4.((a-bar2 + a-bar0;2) | (b3 + b3;4))
--          )
--   + a0;5.(   b1.((a-bar2 + a-bar0;2) | (b3 + b3;4))
--          + b1;4.((a-bar2 + a-bar0;2) | (b3 + b3;4))
--          )
--   )
--   |
--   (   b-bar4.(a-bar5 + a-bar0;5)
--   + b-bar1;4.(a-bar5 + a-bar0;5)
--   + b-bar3;4.(a-bar5 + a-bar0;5)
--   )
-- )
-- \{a0;5,b1;4,b3;4}
\end{code}

Examples from [GEN, v19 Note4+] and [VK Note 4]

\begin{code}
mkExample ccs
 = putStrLn $ unlines $ map shExample
            $ zip ["ccs ","c2ix","g*  ","csp "] [ccs,ccsi,ccsg,csp]
 where
   shExample (label,proc) = label ++ " : " ++ show proc 
   ccsi = indexNames ccs
   ccsg = gsp0 ccsi
   csp = tl ccsg

-- GEN: v19 Note 4 (update):
-- p20 g*({},a.0 | a-bar.0) =  (a1.0+a12.0)|(a2-bar.0+a12-bar.0)
aIabar = cpar [a0,abar0]
xmp_aIabar = mkExample aIabar

-- p21 g*({},(a.0 | a-bar.0)|' {a})
   -- =  ((a1.0+a12.0)|(a2-bar.0+a12-bar.0)) |' {a1,a2}
noaIabar = Rstr [ea] aIabar
xmp_noaIabar = mkExample noaIabar

-- p29  g*((a.0 | a-bar.0)|' {a} + b.0)
bAndaIabar = csum [noaIabar,b0]
xmp_bAndaIabar = mkExample bAndaIabar

-- VK:
-- (a1 | a2-bar)[g*]   -->  (a1 + a12 | a2-bar + a12-bar)
-- a \restrict a | a-bar  -->  a2
-- (a1 | a2-bar) \restrict a   -->  a2  STOP  (?)
-- (a1 | a2-bar)\restrict(a1,a2)[g*,0]  --> a2 STOP ?
-- ( a1 \restrict a1 |  a2-bar)[g*,0]
    -- -->  (a1+a12)\restrict a1,a12 | a2-bar + a12-bar
\end{code}


In [GEN v18, Def 2.1, p7] we have:
\begin{eqnarray*}
   P \hide A &\defeq& ( P \mid \mu X (\Pi_{} a.X))\restrict A
\end{eqnarray*}

Looking up the referecence ([16])  cited there (Milner)
we see the following, simplified here a bit:
\begin{eqnarray*}
   Ever(\alpha) &=& \alpha.Ever(\alpha)
\\ P \hide H &=&
   ( P \mid Ever(\bar\ell_1) \mid \dots \mid Ever(\bar\ell_n)) \restrict H
\\ && \where H =\{ \ell_1, \dots, \ell_n\}
\\ P \hide H
   &\defeq&
   ( P \mid \Pi_{\ell \in H} (\mu X . \bar\ell . X) ) \restrict H
\end{eqnarray*}
Note that the recursion is under the iterated parallel,
not enclosing it.
\begin{code}
ever :: IxLab -> Proc
ever evt = Rec "X" $ Pfx (Lbl $ evtbar evt) $ PVar "X"
infixl 7 \\
(\\) :: Proc -> [IxLab] -> Proc
ccs \\ ilbls  =  Rstr ilbls $ cpar (ccs:map ever ilbls)
\end{code}

Here we want to prove(?) that
\begin{eqnarray*}
\\ g^*(S,P \hide B) &=& g^*(S,P) \hide g^*(S\cup B,B)
\end{eqnarray*}
\begin{code}
prop_gstar_hide evts ccs ilbls
 = gsp evts (ccs \\ ilbls)
   ==
   gsp evts ccs \\ gsb (evts `S.union` S.fromList ilbls) ilbls
\end{code}
