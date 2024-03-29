\section{Semantics}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2020-22

LICENSE: BSD3, see file LICENSE at ccs2csp root
\end{verbatim}
\begin{code}
module Semantics where

import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad
import Control
import Syntax

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg name  = Semantics.dbg (name++" = ")
\end{code}

\subsection{CCS Semantics}

\subsubsection{Operational Semantics}


From \cite{Comm:Concur:Milner:89},p46

\begin{mathpar}
  \infer{ }{\alpha.E \trans\alpha E} \; Act
  \and
  \infer{j \in I \\ E_j \trans\alpha E'_j}
        {\Sigma_{i \in I}E_i \trans\alpha E'_j}
        \; Sum_j
  \and
  \infer{E \trans\alpha E'}{E | F \trans\alpha E'|F} \; Com_1
  \and
  \infer{F \trans\alpha F'}{E | F \trans\alpha E|F'} \; Com_2
  \and
  \infer{E \trans\ell E' \\ F \trans{\overline\ell} F'}
        {E|F \trans\tau E'|F'} \; Com_3
  \and
  \infer{\alpha,\overline\alpha \notin L \\ E \trans\alpha E'}
        {E\setminus L \trans\alpha E'\setminus L} \; Res
  \and
  \infer{E \trans\alpha E'}{E[f]\trans{f(\alpha)}E'[f]} \; Rel
  \and
  \infer{A \defeq P \\ P \trans\alpha P'}
        {A \trans\alpha P'} \; Con
\end{mathpar}

In the CCS-$\tau$ variant,
we replace $Com_3$ with
\[
  \infer{E \trans\ell E' \\ F \trans{\overline\ell} F'}
        {E|F \trans{\tau[\ell|\overline\ell]} E'|F'}
\]
For now,
we want a function ("after-tau")
that returns the set of processes that can result from a tau event.
\begin{eqnarray*}
   \circ\tau &:& CCS \fun CCS^*
\\ \circ\tau(P) &\defeq& \{ P' \mid P \trans\tau P' \}
\end{eqnarray*}

We reify this as follows:
\begin{eqnarray*}
   \circ\tau(0) &\defeq& \setof{}
\\ \circ\tau(\tau.P) &\defeq& \setof{P}
\\ \circ\tau(\tau[\ell|\overline\ell].P) &\defeq& \setof{}
\\ \circ\tau(\ell.P) &\defeq& \setof{}
\\ \circ\tau(P_1+P_2) &\defeq& \circ\tau(P_1) \cup \circ\tau(P_2)
\\ \circ\tau(P_1 | P_2) &\defeq&  \circ\tau^2(P_1,P_2)
\\ \circ\tau(P\restrict L) &\defeq& \circ\tau(P)
\\ \circ\tau(P[f]) &\defeq& \setof{ P'[f] \mid P' \in \circ\tau(P)}
\\ \circ\tau(\mu X \bullet P) &\defeq& \setof{}
\end{eqnarray*}
In the last line we assume (promptly) guarded recursion.
\begin{code}
-- isCCS
afterTau :: CCS -> [CCS]
afterTau (CCSpfx T ccs)         =  [ccs]
afterTau (CCSpfx (T' _ _) ccs)  =  [] -- not considered a tau here !
afterTau (Sum ccs1 ccs2)     =  afterTau ccs1 ++ afterTau ccs2
afterTau (Comp ccs1 ccs2)    =  parBodiesAfterTaus ccs1 ccs2
afterTau (Rstr es ccs)       =  afterTau ccs
afterTau (CCSren s2s ccs)       =  map (CCSren s2s) $ afterTau ccs
afterTau (CCSmu s ccs)         =  []
afterTau _                   =  [] -- the rest, incl CSP stuff
\end{code}

A parallel can produce a tau event in two ways:
(i) one of its processes performs a tau;
or (ii) two of its processes communicate.
If we are translating from $ccs\tau$,
then communications are ``visible'' taus,
which should not count here.
\begin{eqnarray*}
   \circ\tau^2(P_1,P_2) &\defeq& \dots
\end{eqnarray*}
\begin{code}
parBodiesAfterTaus :: CCS -> CCS -> [CCS]
parBodiesAfterTaus ccs1 ccs2
  =  parBodiesAfterOwnTaus ccs1 ccs2 -- ++ parBodiesAfterComTaus ccs1 ccs2
\end{code}

Given $P_1 | \dots | P_i | \dots | P_n$,
for each $i \in 1\dots n$, we compute $\circ\tau(P_i)$.
For each $P'_j$ in  $\circ\tau(P_i)$ we construct
$P_1 | \dots | P'_j | \dots | P_n$.
\begin{code}
parBodiesAfterOwnTaus :: CCS -> CCS -> [CCS]
parBodiesAfterOwnTaus ccs1 ccs2
  = map (Comp ccs1) ccs2s' ++ map (flip Comp ccs2) ccs1s'
  where
    ccs1s' = afterTau ccs1
    ccs2s' = afterTau ccs2
\end{code}

Given $P_1 | \dots | P_i | \dots | P_j | \dots | P_n$,
for each $i,j \in 1\dots n, i < j$ (w.l.o.g.),
we compute $(\circ\ell(P_i),\circ\bar\ell(P_i))$,
for every pair $(\ell,\bar\ell)$
where $\ell \in \Alf(P_i)$ and $\bar\ell \in \Alf(P_j)$.
For every pair $(P'_m,P'_n)$ so generated,
we construct
$P_1 | \dots | P'_m | \dots | P'_n | \dots | P_n$.
When $n=2$, we simply compute as follows:
\begin{eqnarray*}
   \alpha_{12} &\defeq& \Alf(P_1)\cap\overline{\Alf(P_2)}
\\ &=& \setof{\ell_1,\dots,\ell_k}
\\ P_1 | P_2
   &\mapsto&
   \{ \circ\ell_i(P_1) | \circ\bar\ell_i(P_2), i \in 1\dots k \}
\end{eqnarray*}
\begin{code}
parBodiesAfterComTaus :: CCS -> CCS -> [CCS]
parBodiesAfterComTaus ccs1 ccs2
  = concat $ map (afterThisCom ccs1 ccs2) ell1s
  where
    alf1 = alf ccs1
    alf2 = alf ccs2
    alf12 = alf1 `S.intersection` (S.map pfxbar alf2)
    ell1s = S.toList alf12
    afterThisCom ccs1 ccs2 ell
      = let
          ccs1s = afterEvt ell ccs1
          ccs2s = afterEvt (pfxbar ell) ccs2
        in [] -- need to re-think all of this.....
\end{code}

The above requires us to also provide a function ``after-label''
that returns a list of processes that can result from a specified label event.
\begin{eqnarray*}
   \circ\ell &:& CCS \fun CCS^*
\\ \circ\ell(P) &\defeq& \{ P' \mid P \trans\ell P' \}
\end{eqnarray*}
\begin{code}
-- isCCS
afterEvt :: Event -> CCS -> [CCS]
afterEvt pfx (CCSpfx pfx' ccs)
  | pfx == pfx'                 =  [ccs]
afterEvt pfx (Sum p1 p2)        =  concat $ map (afterEvt pfx) [p1,p2]
afterEvt pfx (Comp ccs1 ccs2)   =  parBodiesAfterEvts ccs1 ccs2
afterEvt pfx@(Lbl evt) (Rstr es ccs)
  | not (evt `elem` es)        =  afterEvt pfx ccs
afterEvt pfx (CCSren s2s ccs)     =  afterEvt pfx $ doRename (endo s2s) ccs
afterEvt pfx (CCSmu s ccs)       =  afterEvt pfx ccs
afterEvt pfx _                 =  [] -- the rest, incl CSP stuff
\end{code}

Given $P_1 | \dots | P_i | \dots | P_n$,
for each $i \in 1\dots n$, and each $\ell \in \Alf(P_i)$,
we compute $\circ\ell(P_i)$.
For each $P'_j$ in  $\circ\ell(P_i)$ we construct
$P_1 | \dots | P'_j | \dots | P_n$.
\begin{code}
parBodiesAfterEvts :: CCS -> CCS -> [CCS]
parBodiesAfterEvts ccs1 ccs2
  = map (Comp ccs1) ccs2s' ++ map (flip Comp ccs2) ccs1s'
  where
    alf1 = S.toList $ alf ccs1
    alf2 = S.toList $ alf ccs2
    ccs1s' = concat $ map ($ ccs1) (map afterEvt alf1)
    ccs2s' = concat $ map ($ ccs2) (map afterEvt alf2)
\end{code}

\subsubsection{Equational Laws}

From \cite{Comm:Concur:Milner:89},pp62--80.

Law $E_1 = E_2$ means that, for all $\alpha$,
that $E_1 \wktrans\alpha E'$ iff $E_2 \wktrans\alpha E'$.

\begin{code}
type LawFun m = CCS -> m CCS
\end{code}


\subsubsection{Monoid Laws}

Proposition 1 (\cite{Comm:Concur:Milner:89},p62).
\begin{eqnarray}
   P+Q &=& Q+P
\\ P+(Q+R) &=& (P+Q)+R
\\ P+P &=& P
\\ P+0 &=& P
\end{eqnarray}
\begin{code}
sumComm, sumAssoc, sumIdem, sumId :: MonadPlus m => LawFun m
sumComm (Sum p q) = return $ Sum q p
sumComm _ = fail "not P+Q"
sumAssoc (Sum p (Sum q r)) = return $ Sum (Sum p q) r
sumAssoc _ = fail "not P+(Q+R)"
sumIdem (Sum p q) | p==q  = return p
sumIdem _ = fail "not P+P"
sumId (Sum p Zero) = return p
sumId _ = fail "not P+0"
\end{code}
We can normalise sums by flattening and sorting:
\begin{code}
sumNorm :: MonadPlus m => LawFun m
sumNorm p = return p -- to be implemented
\end{code}

\subsubsection{$\tau$ Laws}

Proposition 2 (\cite{Comm:Concur:Milner:89},p62).
\begin{eqnarray}
   \alpha.\tau.P &=& a.P
\\ P+\tau.P &=& \tau.P
\\ \alpha.(P+\tau.Q)+\alpha.Q &=& \alpha.(P+\tau.Q)
\end{eqnarray}
\begin{code}
tauAbsorb, sumTau, sumTau2 :: MonadPlus m => LawFun m
tauAbsorb _ = fail "not a.t.P"
sumTau _ = fail "not P+t.P"
sumTau2 = fail "not a.(P+t.Q)+a.Q"
\end{code}
Corrollary 3 (\cite{Comm:Concur:Milner:89},p63)
\begin{eqnarray}
   P+\tau.(P+Q) &=& \tau.(P+Q)
\end{eqnarray}

\subsubsection{Recursion}

$X$ is sequential in $E$ if it occurs only inside \verb"Event" or Sum.

$X$ is guarded in $E$ if each occurrence inside some $\ell.F$ within $E$.

\subsubsection{Expansion Law}

[CC, p69]
\begin{eqnarray}
   P &\equiv& (P_1[f_1]|\dots|P_n[f_n])\hide L
\\ P &=& \Sigma
         \left\{
           f_i(\alpha).(P_1[f_1]|\dots|P'_i[f_i]|\dots|P_n[f_n])\hide L :
         \right. \nonumber
\\   & & \left. \qquad P_i \trans{\alpha_i} P'_i, f_i(\alpha)\neq L \cup \bar L
         \right\} \nonumber
\\   &+& \Sigma
         \left\{
           \tau.(P_1[f_1]|\dots|P'_i[f_i]|\dots|P'_j[f_j]|\dots|P_n[f_n])\hide L :
         \right. \nonumber
\\   & & \left. \qquad P_i \trans{\ell_1} P'_i,
                       P_j \trans{\ell_2} P'_j,
                       f_i(\ell_1) = \bar{f_j(\ell_2)},
                       i < j
         \right\}
\\ P &\equiv& (P_1|\dots|P_n)\hide L
\\ P &=& \Sigma
      \left\{
        f_i(\alpha).(P_1|\dots|P'_i|\dots|P_n)\hide L :
          P_i \trans{\alpha_i} P'_i, \alpha\neq L \cup \bar L
       \right\} \nonumber
\\   &+& \Sigma
      \left\{
        \tau.(P_1|\dots|P'_i|\dots|P'_j|\dots|P_n)\hide L :
      \right. \nonumber
\\   & & \left. \qquad P_i \trans{\ell} P'_i,
                    P_j \trans{\bar\ell} P'_j,
                    i < j
      \right\}
\end{eqnarray}

Corrollary 7 ([CC, p70]])
\begin{eqnarray}
   (\alpha.Q)\hide L
   &=& 0 \IF \alpha \in L\cup\bar L, \OTHERWISE \alpha.Q\hide L
\\ (\alpha.Q)[f] &= f(\alpha).Q[f]
\\ (Q+R)\hide L &=& Q\hide L + R\hide L
\\ (Q+R)[f] &=& Q[f] + R[f]
\end{eqnarray}

\subsubsection{Composition Laws}

[CC, p80]
\begin{eqnarray}
   P|Q &=& Q|P
\\ P|(Q|R) &=& (P|Q)|R
\\ P|0 &=& P
\end{eqnarray}

\subsubsection{Restriction Laws}

[CC, p80]
\begin{eqnarray}
   P\L &=& P \quad \IF \mathcal L(P) \cap (L \cup \bar L) = \emptyset
\\ P\hide K\hide L &=& P\hide(K \cup L)
\\ P[f]\hide L &=& P\hide f^{-1}(L)[f]
\\ (P|Q)\hide L &=& P\hide L | Q\hide L
  \quad \IF \mathcal L(P) \cap \bar{\mathcal L(Q)} \cap (L\cup\bar L) = \emptyset
\end{eqnarray}

\subsubsection{Relabelling Laws}

[CC, p80]
\begin{eqnarray}
   P[Id] &=& P
\\ P[f] &=& P[f'] \quad \IF f\restrict\mathcal L(P) = f'\restrict\mathcal L(P)
\\ P[f][f'] &=& P[f' \circ f]
\\ (P|Q)[f] &=& P[f] | Q[f]
   \quad \IF f\restrict(L \cup \bar L)\text{ is 1-1, where } L=\mathcal L(P|Q)
\end{eqnarray}

corollary 11 [CC, p81]
\begin{eqnarray}
   P[b/a] &=& P \quad \IF a,\bar a \notin \mathcal L(P)
\\ P\hide a &=& P[b/a]\hide b \quad \IF b,\bar b \notin \mathcal L(P)
\\ P\hide a[b/c] &=& P[b/c]\hide a \quad \IF b,c \neq a
\end{eqnarray}

\subsubsection{Non-Laws}

[CC,p64]
\begin{eqnarray*}
   \tau.P &\neq& P
\\ a.(P+Q) &\neq& a.P + a.Q
\end{eqnarray*}

\newpage
\subsubsection{Trace Semantics}

We can define traces for CCS terms,
in a number of ways.
One is simply the full set of complete traces,
some of which may be infinite.
Another has partial traces, all finite,
with a prefix-closure healthiness condition.

In the sequel, we play fast and loose,
using recursion to define functions over potentially infinite lists.
These can all be cast into an appropriate co-recursive form,
or simply interpreted as such (which is what Haskell's laziness does
by default).
We also use cons-notation for lists
($x:\sigma$ is same as $\seqof x\cat\sigma$).

Here is the full trace set version%
\footnote{
 This may omit any deadlock traces
 (see defn. of $P\setminus L$).
}
:
\begin{eqnarray*}
   trc &:& CCS \rightarrow \Set (IxLab^\omega)
\\ trc(0) &\defeq& \{\nil\}
\\ trc(\alpha.P)
   &\defeq&
   \{ \alpha:\sigma
      \mid
      \sigma \in trc(P)
   \}
\\ trc(P+Q) &\defeq& trc(P) \cup trc(Q)
\\ trc(P|Q)
   &\defeq&
   \{ t
      \mid
      t \in t_P | t_Q, t_P \in trc(P), t_Q \in trc(Q)
   \}
\\ trc(P\setminus L)
   &\defeq&
   \{ \sigma
     \mid
     \sigma \in trc(P),
     \sigma\cap L = \emptyset
   \}
\\ trc(P[f]) &\defeq& \{ f(\sigma) \mid \sigma \in trc(P) \}
\\ trc(\mu X \bullet P)
   &\defeq&
   trc(P(X \mapsto \mu X \bullet P)
\end{eqnarray*}
Here the interesting function is one on traces: $s|t$
returns all valid interleavings of $s$ and $t$.
\begin{eqnarray*}
   \_|\_ &:& (IxLab^\omega)^2 \fun \Set (IxLab^\omega)
\\ \nil|t &\defeq& \{t\}
\\ t|nil &\defeq& \{t\}
\\ (\alpha:t_1)|(\bar\alpha:t_2)
   &\defeq&
   \{ \alpha:(t_1|\bar\alpha:t_2)
   ,\quad  \tau:(t_1|t_2)
   ,\quad  \bar\alpha:(\alpha:t_1|t_2)
   \}
\\ (\alpha:t_1)|(\beta:t_2)
   &\defeq&
   \{ \alpha:(t_1|\beta:t_2)
   ,\quad  \beta:(\alpha:t_1|t_2)
   \}
\end{eqnarray*}

\textbf{Hypothesis}
\textsf{The definition given here gives the same results
as the usual derivation of $trc$ from the operational semantics.}

\newpage
\subsection{CSP Semantics}

\subsubsection{Operational Semantics}

From Schneider

\begin{mathpar}
  \infer{ }{(a \then P)\; \trans a \; P} \; Act
  \and
  \infer{ }{SKIP \; \trans\surd \; STOP} \; Term
  \and
  \infer{i \in \{1,2\} \\ P_i \trans a P'_i}
        {P_1 \Box P_2 \trans a P'_i}
        \; ExtC_1
  \and
  \infer{P_1 \trans\tau P'_1}
        {P_1 \Box P_2 \trans\tau P'_1 \Box P_2
         \\
         P_2 \Box P_1 \trans\tau P_2 \Box P'_1
        }
        \; ExtC_2
  \and
  \infer{ }
        {P_1 \sqcap P_2 \trans\tau P_1
         \\
         P_1 \sqcap P_2 \trans\tau P_2
        }
        \; IntC
  \and
  \infer{\mu \notin A^\surd \\ P_1 \trans\mu P'_1}
        {P_1 \parallel_A P_2 \trans\mu P'_1 \parallel_A P_2
         \\
         P_2 \parallel_A P_1 \trans\mu P_2 \parallel_A P'_1
        }
        \; Par_1
  \and
  \infer{\mu \in A^\surd \\ P_1 \trans\mu P'_1 \\ P_2 \trans\mu P'_2}
        {P_1 \parallel_A P_2 \trans\mu P'_1 \parallel_A P'_2} \; Par_2
  \and
  \infer{a \in A \\ P \trans a P'}
        {P \hide A \trans\tau P' \hide A} \; Hid_1
  \and
  \and
  \infer{a \notin A \\ P \trans a P'}
        {P \hide A \trans a P' \hide A} \; Hid_2
  \and
  \infer{P \trans a P'}{f(P) \trans{f(a)} f(P')} \; Ren_1
  \and
  \infer{P \trans\tau P'}{f(P) \trans\tau f(P')} \; Ren_2
  \and
  \infer{N = P \\ P \trans\mu P'}
        {N \trans\mu P'} \; CCSmu
\end{mathpar}
