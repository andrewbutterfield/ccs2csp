\section{Examples}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2020-22

LICENSE: BSD3, see file LICENSE at demoCCS2CSP root
\end{verbatim}
\begin{code}
module Examples where
import Prelude hiding ( (<>) )

import Control.Monad
import System.IO
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Syntax
import Translate
import Semantics
import CSPm
import CCSm

--import Debug.Trace
--dbg msg x = trace (msg++show x) x
\end{code}

\subsection{Milners ``Comms and Conc'' book.}

The following example is used to demonstrate the precedence
of the various CCS binary operators.
\begin{code}
-- p44  R+a.P|b.Q\L = R+((a.P)|(b.(Q\L)))
p = CCSvar "P" ; q = CCSvar "Q" ; r = CCSvar "R" ; s = CCSvar "S"
ell = (Std "L",None)
cc44 = csum [ r
            , cpar [ CCSpfx a p
                   , CCSpfx b (Rstr (S.singleton ell) q)
                   ]
            ]
\end{code}
It does not play well with the translation because the abstract syntax
does not support names for restriction sets, only explicit set enumerations.

\newpage
\subsection{Showing Examples}

We create a datatype that can be either CCS or CSP,
so we can have lists showing the steps in a transformation
from CCS to CSP.
\begin{code}
data Proc = CCS CCS | CSP CSP deriving Show
\end{code}

The \texttt{genExample} function takes a CCS term
and applies the translation step-by-step,
to generate a list of same, paired with meaningful names.
\begin{code}
genExample :: CCS ->  [(String,Proc)]
genExample ccs
 = [ ("ccs  ", CCS ccs)
   , ("ccsT ", CCS ccstau)
   , ("ccsTi", CCS ccsi)
   , ("g*0  ", CCS ccsg)
   , ("tlp  ", CSP tlp)
   , ("tlh  ", CSP tlh)
   , ("csp  ", CSP csp)
   ]
 where
   ccstau = c2ccsT ccs
   ccsi = ix ccstau
   ccsg = gsp0 ccsi
   tlp  = tl ccsg
   tlh = t2csp ccstau
   csp = ccs2csp ccs
\end{code}

We use \texttt{runExample} to display that list
\begin{code}
showExample :: [(String,Proc)] -> String
showExample  =  unlines . map shExample
 where
   shExample (label,proc) = label ++ " : " ++ show proc
\end{code}

We use \texttt{runExample} to to generate and display that list
\begin{code}
runExample :: CCS -> IO ()
runExample  =  putStrLn . showExample . genExample
\end{code}


\newpage
\subsection{Collection of Useful ``Bits''}

\begin{code}
na = Std "a" ; ea = (na,None);  a = Lbl ea ; abar = pfxbar a
nb = Std "b" ; eb = (nb,None);  b = Lbl eb ; bbar = pfxbar b
nc = Std "c" ; ec = (nc,None);  c = Lbl ec ; cbar = pfxbar c
nd = Std "d" ; ed = (nd,None);  d = Lbl ed ; dbar = pfxbar d
a0 = CCSpfx a Zero; abar0 = CCSpfx abar Zero
b0 = CCSpfx b Zero; bbar0 = CCSpfx bbar Zero
c0 = CCSpfx c Zero; cbar0 = CCSpfx cbar Zero
\end{code}

\subsection{Small Test Examples}

\begin{eqnarray*}
   \lefteqn{a.0|\bar a.0}
\\ &\leadsto&
   ((a \then Stop \extc a_{12} \then Stop)
   \parallel_{\setof{a_{12}}}
   (a \then Stop \extc a_{12} \then Stop))\hide \{tau,a_{12}\}
\end{eqnarray*}
This is Example 26 from \cite{DBLP:conf/sefm/NgondiKB21}.
\begin{code}
aIabar = cpar [a0,abar0]
xmp_aIabar = runExample aIabar
\end{code}


$$(a.0|\bar a.0)\restrict\setof a$$
\begin{code}
noaIabar = Rstr (S.singleton ea) aIabar
xmp_noaIabar = runExample noaIabar
\end{code}


$$ (a.0|\bar a.0)\restrict\setof a + b.0$$
\begin{code}
--  g*((a.0 | a_bar.0)|' {a} + b.0)
bAndaIabar = csum [noaIabar,b0]
xmp_bAndaIabar = runExample bAndaIabar
\end{code}

$$ (a.c.0|\bar a.0)\restrict\setof a + b.0$$
\begin{code}
ac0 = CCSpfx a $ CCSpfx c Zero
acIabar = cpar [ac0,abar0]
noacIabar = Rstr (S.singleton ea) acIabar
bAndacIabar = csum [noacIabar,b0]
xmp_bAndacIabar = runExample bAndacIabar
\end{code}


$$a.P + \tau.Q \leadsto (t2csp(a.P)\Box t2csp(Q)) \sqcap t2csp(Q)$$
\begin{code}
xmp2 = cpar [CCSpfx a p,CCSpfx T q]
\end{code}


$$ a.b.0 | \bar b.\bar a.0$$
\begin{code}
-- a.b.0 | b_bar.a_bar.0
xms1 = cpar [ CCSpfx a (CCSpfx b Zero), CCSpfx bbar (CCSpfx abar Zero)]
\end{code}

\newpage
$$ a.b.(\bar a.0|b.0) | \bar b.\bar a.0$$
\begin{code}
-- a.b.(abar.0|b.0) | bbar.abar.0
xms2 = cpar [ CCSpfx a (CCSpfx b (cpar [ CCSpfx abar Zero, CCSpfx b Zero]))
              , CCSpfx bbar (CCSpfx abar Zero)
              ]
\end{code}



$$(a.P|\bar a.Q|\bar a.R|\bar a.S)\restrict\setof a$$
\begin{code}
x18 = Rstr (S.singleton ea)
       $ cpar [CCSpfx a p, cpar [CCSpfx abar q, cpar [CCSpfx abar r, CCSpfx abar s]]]
\end{code}

$$a.0|\bar a.0|\bar a.0|\bar a.0$$
\begin{code}
xb19 = cpar [ CCSpfx a (cpar [a0,a0,a0,a0])
            , abar0
            , CCSpfx abar (cpar [a0,a0])
            ]
\end{code}

$$(a.P)\restrict\setof a = 0$$
\begin{code}
aPra = Rstr (S.singleton ea) (CCSpfx a p)
\end{code}

\subsection{CSP Hiding in CCS}


We see the following definition of hiding by Milner,
simplified here a bit:
\begin{eqnarray*}
   Ever(\alpha) &=& \alpha.Ever(\alpha)
\\ P \hide H &=&
   ( P \mid Ever(\bar\ell_1) \mid \dots \mid Ever(\bar\ell_n)) \restrict H
\\ && \where H =\{ \ell_1, \dots, \ell_n\}
\\ P \hide H
   &\defeq&
   ( P \mid \Pi_{\ell \in H} (\mu X . \bar\ell . X) ) \restrict H
\end{eqnarray*}
\begin{code}
ever :: IxLab -> CCS
ever evt = CCSmu "X" $ CCSpfx (Lbl $ ixlbar evt) $ CCSvar "X"
infixl 7 \\
(\\) :: CCS -> (Set IxLab) -> CCS
ccs \\ ilbls  =  Rstr ilbls $ cpar (ccs:map ever (S.toList ilbls))
\end{code}
Key question:
is our translation of $P\hide H$ as defined above
equivalent to translating $P$ to CSP, and then doing the hiding?


\subsection{CSP Examples}

These examples are mainly to check the CSPm rendering:
\begin{code}
aThenBStar           =  pfx a $ CSPmu "P" $ pfx b $ CSPvar "P"
aThenBonBwithBthenC  =  par [b] (pfxs [a,b] Skip) (pfxs [b,c] Skip)
doExtThenInt         =  (pfx a Skip <> pfx b Skip)
                        $>
                        (pfx c Skip |~| pfx d Stop)
\end{code}


\subsection{Demonstrations and End-to-End translation}

\begin{code}
demoCSPm :: CSP -> IO ()
demoCSPm csp = putStrLn $ generateCSPm "MAIN" csp
\end{code}

\begin{code}
demoCCS2CSPm :: CCS -> IO ()
demoCCS2CSPm ccs = putStrLn $ generateCSPm "FROM_CCS" $ ccs2csp ccs
\end{code}


\begin{code}
fileDemoCCS2CSP :: String -> CCS -> IO ()
fileDemoCCS2CSP fname ccs
  = let ccs_show = show ccs
        csp = ccs2csp ccs
        csp_show = show csp
        cspm = generateCSPm "FROM_CCS" csp
    in if null fname
         then do putStrLn ccs_show
                 putStrLn csp_show
                 putStrLn cspm
         else do h <- openFile fname WriteMode
                 hPutStrLn h "{-"
                 hPutStrLn h ("  CCS: " ++ ccs_show)
                 hPutStrLn h ""
                 hPutStrLn h ("  CSP:" ++ csp_show)
                 hPutStrLn h "-}"
                 hPutStrLn h ""
                 hPutStrLn h cspm
                 hClose h
                 putStrLn ("CSPm written to "++fname++" for following CSP:")
                 putStrLn ("  "++csp_show)
\end{code}

\begin{code}
ccsM2cspM :: String -> IO ()
ccsM2cspM txt
  = case programParser txt of
      Left err  ->  putStrLn err
      Right prog -> putStrLn $ show prog
\end{code}
