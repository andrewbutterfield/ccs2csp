\section{Semantics}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2020

LICENSE: BSD3, see file LICENSE at ccs2csp root
\end{verbatim}
\begin{code}
module Semantics where

import Control.Monad
import Syntax

--import Debug.Trace
--dbg msg x = trace (msg++show x) x
\end{code}

\subsection{CCS Semantics}

\subsubsection{Operational Semantics}


From [CC],p46

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
  \infer{E \trans\alpha E'}{E[f]\trans{f(\alpha)}E'[f]} \; Ren
  \and
  \infer{A \defeq P \\ P \trans\alpha P'}
        {A \trans\alpha P'} \; Con
\end{mathpar}

From [GEN], in the CCS-$\tau$ variant,
we replace $Com_3$ with
\[
  \infer{E \trans\ell E' \\ F \trans{\overline\ell} F'}
        {E|F \trans{\tau[\ell|\overline\ell]} E'|F'}
\]


\subsubsection{Equational Laws}

From [CC],pp62--80.

Law $E_1 = E_2$ means that, for all $\alpha$,
that $E_1 \wktrans\alpha E'$ iff $E_2 \wktrans\alpha E'$.

\begin{code}
type LawFun m = Process -> m Process
\end{code}


\subsubsection{Monoid Laws}

Proposition 1 ([CC],p62).
\begin{eqnarray}
   P+Q &=& Q+P
\\ P+(Q+R) &=& (P+Q)+R
\\ P+P &=& P
\\ P+0 &=& P
\end{eqnarray}
\begin{code}
sumComm, sumAssoc, sumIdem, sumId :: MonadPlus m => LawFun m
sumComm (Sum [p,q]) = return $ Sum [q,p]
sumComm _ = fail "not P+Q"
sumAssoc (Sum [p,Sum [q,r]]) = return $ Sum [Sum [p,q],r]
sumAssoc _ = fail "not P+(Q+R)"
sumIdem (Sum [p,q]) | p==q  = return p
sumIdem _ = fail "not P+P"
sumId (Sum [p,Zero]) = return p
sumId _ = fail "not P+0"
\end{code}
We can normalise sums by flattening and sorting:
\begin{code}
sumNorm :: MonadPlus m => LawFun m
sumNorm p = return p -- to be implemented
\end{code}

\subsubsection{$\tau$ Laws}

Proposition 2 ([CC],p62).
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
Corrollary 3 ([CC],p63)
\begin{eqnarray}
   P+\tau.(P+Q) &=& \tau.(P+Q)
\end{eqnarray}

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
   trc &:& CCS \rightarrow \Set (Event^\omega)
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
   \_|\_ &:& (Event^\omega)^2 \fun \Set (Event^\omega)
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
        {N \trans\mu P'} \; Rec
\end{mathpar}
