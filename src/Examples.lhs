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

\subsection{Showing Examples}

\begin{code}
mkExample ccs
 = putStrLn $ unlines $ map shExample
            $ zip ["ccs  ","c2ix ","g*0  ","cs4  ","tlp  ","t2csp"]
                  [ ccs   , ccsi  , ccsg  , ccs4  , tlp   , csp   ]
 where
   shExample (label,proc) = label ++ " : " ++ show proc
   ccsi = indexNames ccs
   ccsg = gsp0 ccsi
   ccs4 = c4star S.empty ccs
   tlp  = tl ccs4
   csp = t2csp S.empty ccs
\end{code}

\subsection{Milners ``Comms and Conc'' book.}

\begin{code}
  -- p44  R+a.P|b.Q\L = R+((a.P)|(b.(Q\L)))
na = Std "a" ; ea = (na,None);  a = Lbl ea
nb = Std "b" ; b = Lbl (nb,None)
nc = Std "c" ; ec = (nc,None); c = Lbl ec
r = PVar "R"
p = PVar "P"
ell = (Std "L",None)
q = PVar "Q"
cc44 = csum [ r
            , cpar [ Pfx a p
                   , Pfx b (Rstr (S.singleton ell) q)
                   ]
            ]
\end{code}

\subsection{Gerard's Examples (recent)}

Based on G. Ekembe N., ``From CCS to CSP'', April 15th 2021:

\paragraph{Defn 3.1, p11}

\begin{eqnarray*}
  c2ccs\tau(P|Q)
  &\defeq&
 (c2ccs\tau(P)|_T c2ccs\tau(Q))
 \hide_T
 \{\tau[\bar a|a] | a \in \Alf P, \bar a \in \Alf Q\}
\end{eqnarray*}

\paragraph{Lemma 1, p12}

For CCSTau processes:
\begin{equation*}
   P_\tau | Q_\tau
   =
   (P_\tau |_T Q_\tau)
   \hide_T
   \{\tau[\bar a|a] | a \in \Alf P, \bar a \in \Alf Q\}
\end{equation*}

\paragraph{Defn 4.8, p21}

\begin{eqnarray*}
   \vdots
\\ tl(P_1 | P_2)
   &\defeq&
   tl(P_1) \parallel_{\setof{a | a \in \Alf P_1 \cap \Alf P_2}} tl(P_2)
\\ \vdots
\end{eqnarray*}

\paragraph{Example 4.7, p21}

\begin{eqnarray*}
   c4star(a.0|\bar a.0)
   &=&
   (a_1.0 + a_{12}.0)|(\bar a_2.0 + \bar a_{12}.0)
\\ c4star(a.0|\bar a.0)
   &=&
   (a_1.0 + a_{12}.0)|(a_2.0 + a_{12}.0)
\\ tl(c4star(a.0|\bar a.0))
   &=&
   (a_1 \then Stop \extc a_{12} \then Stop)
   \parallel_{\setof{a_12}}
   (a_2 \then Stop \extc a_{12} \then Stop)
\end{eqnarray*}

\paragraph{Example 4.8, pp23--4}

\begin{eqnarray*}
   (a.0|\bar a.0)\restrict \setof{a} + b.0
   &\equiv& \tau.0 + b.0
\end{eqnarray*}

\begin{eqnarray*}
   && t2csp((a.0|\bar a.0)\restrict \setof{a} + b.0)
\\&=& ccs-par\; def
\\ && t2csp((a.0|_T\bar a.0)\hide_T \setof{a} + b.0)
\\&=& t2csp\; def
\\ && t2csp((a.0|_T\bar a.0)\hide_T \setof{a} \restrict\setof a) \extc  t2csp(b.0)
\\&=& t2csp\; def
\\ && ((a_1 \then Stop \extc a_{12} \then Stop)
\parallel_{\setof{a_12}}
(a_2 \then Stop \extc a_{12} \then Stop))
       \hide_{csp} \setof{a_1,a_2,a_{12}}
       \restrict_{csp}\setof{a_1,a_2})
      \extc  b \then STOP
\end{eqnarray*}


\paragraph{Defn 4.8, p21}

Should be:
\begin{eqnarray*}
    CCS: && Stop \extc b \then Stop
\\  CCS\tau: && a_{12} \then Stop \extc b \then Stop
\end{eqnarray*}



\subsection{Old Examples}

Examples from Gerard's document, v17.
\begin{code}
-- v17, 4.1.2, p18
s = PVar "S"
abar = pfxbar a
x18 = Rstr (S.singleton ea)
       $ cpar [Pfx a p, cpar [Pfx abar q, cpar [Pfx abar r, Pfx abar s]]]

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
-- GEN: v19 Note 4 (update):
-- p20 g*({},a.0 | a-bar.0) =  (a1.0+a12.0)|(a2-bar.0+a12-bar.0)
aIabar = cpar [a0,abar0]
xmp_aIabar = mkExample aIabar

-- p21 g*({},(a.0 | a-bar.0)|' {a})
   -- =  ((a1.0+a12.0)|(a2-bar.0+a12-bar.0)) |' {a1,a2}
noaIabar = Rstr (S.singleton ea) aIabar
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

\begin{code}
ac0 = Pfx a $ Pfx c Zero
acIabar = cpar [ac0,abar0]
noacIabar = Rstr (S.singleton ea) acIabar
bAndacIabar = csum [noacIabar,b0]
xmp_bAndacIabar = mkExample bAndacIabar
\end{code}
\begin{verbatim}
*Examples> xmp_bAndacIabar
ccs   : (a.c | a-bar)|'a + b
c2ix  : (a1.c2 | a3-bar)|'{a1,a3-bar} + b4
g*0   : ((a1.c2 + a1;3.c2) | (a3-bar + a1;3-bar))|'{a1,a3-bar} + b4
cs4   : ((a1.c2 + a1;3.c2) | (a3-bar + a1;3-bar))|'{a1,a3-bar} + b4
tlp   : ((a_1.c_2 [] a_1_3.c_2) |a_1_3| (a_3 [] a_1_3)) |a_1,a_3| 0 [] b_4 + c_2 | 0
t2csp : ((a_1.c_2 [] a_1_3.c_2) |a_1_3| (a_3 [] a_1_3)) |a_1,a_3| 0 [] b_4 + c_2 | 0
\end{verbatim}
We should not have \verb"c_2" at the end, just \verb"b_4".
\subsection{CSP Hiding in CCS}


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
ever evt = Rec "X" $ Pfx (Lbl $ ixlbar evt) $ PVar "X"
infixl 7 \\
(\\) :: Proc -> (Set IxLab) -> Proc
ccs \\ ilbls  =  Rstr ilbls $ cpar (ccs:map ever (S.toList ilbls))
\end{code}

Here we want to prove(?) that
\begin{eqnarray*}
\\ g^*(S,P \hide B) &=& g^*(S,P) \hide g^*(S\cup B,B)
\end{eqnarray*}
\begin{code}
prop_gstar_hide evts ccs ilbls
 = gsp evts (ccs \\ ilbls)
   ==
   gsp evts ccs \\ gsb (evts `S.union` ilbls) ilbls
\end{code}
