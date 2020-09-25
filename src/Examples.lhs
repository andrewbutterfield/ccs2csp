\section{Examples}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Examples where

import Control.Monad
import Syntax
import Translate
import Semantics

--import Debug.Trace
--dbg msg x = trace (msg++show x) x
\end{code}

Milners ``Comms and Conc'' book.
\begin{code}
  -- p44  R+a.P|b.Q\L = R+((a.P)|(b.(Q\L)))
na = Std "a" ; ea = (na,None);  a = Evt ea
nb = Std "b" ; b = Evt (nb,None)
r = PVar "R"
p = PVar "P"
ell = (Std "L",None)
q = PVar "Q"
cc44 = Sum [ r
           , Par [ Pfx a p
                 , Pfx b (Rstr [ell] q)
                 ]
           ]
\end{code}

Examples from Gerard's document, v17.
\begin{code}
-- v17, 4.1.2, p18
s = PVar "S"
abar = pfxbar a
x18 = Rstr [ea] $ Par [Pfx a p, Pfx abar q, Pfx abar r, Pfx abar s]

--v17, 4.1.2., p19
xl19 = Par [Pfx a Zero, Pfx abar Zero]
ta = T' "a"
a0 = Pfx a Zero; abar0 = Pfx abar Zero
xr19 = Sum [Pfx a $ abar0, Pfx abar $ a0, Pfx ta Zero]

--v17, 4.1.2, p19 bottom
xb19 = Par [ Pfx a (Par [a0,a0,a0,a0])
           , abar0
           , Pfx abar (Par [a0,a0])
           ]
\end{code}

\newpage
Examples from Vasileios MS Team whiteboard, 24th Sep.
\begin{code}
-- a.b.0 | b-bar.a-bar.0
bbar = pfxbar b
xms1 = Par [ Pfx a (Pfx b Zero), Pfx bbar (Pfx abar Zero)]

-- a.b.(abar.0|b.0) | bbar.abar.0
xms2 = Par [ Pfx a (Pfx b (Par [ Pfx abar Zero, Pfx b Zero]))
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
