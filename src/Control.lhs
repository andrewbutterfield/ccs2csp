\section{Control}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2020

LICENSE: BSD3, see file LICENSE at ccs2csp root
\end{verbatim}
\begin{code}
module Control where

--import Debug.Trace
--dbg msg x = trace (msg++show x) x
\end{code}


\subsection{Walk with me}

Given:
\begin{eqnarray*}
   \sigma &=& \seqof{p_1,\dots,p_i,\dots,p_n}
\\ \varsigma &=& \seqof{a_1,\dots,a_i,\dots,a_n}
\\ a_i &=& g(p_i)
\end{eqnarray*}
we want to produce:
\begin{eqnarray*}
   \rho &=&  \seqof{r_1,\dots,r_i,\dots,r_n}
\\ r_i &=& f(p_i,\seqof{a_1,\dots,a_{i-1},a_{i+1},\dots,a_n})
\end{eqnarray*}
We want to compute something for each member $p_i$ of a list,
based on itself and a specific property ($g(p_j)$)
of all the other elements in the same list.
Here the $g(p_j)$ have been pre-computed.
\begin{code}
walk :: (a -> [b] -> c) -> [a] -> [b] -> [c]
walk  f       ps     as      =  walk' f [] [] ps as
walk' f _  _  []     []      =  []
walk' f sp sa (p:ps) (a:as)  =  f p (sa++as)  : walk' f (p:sp) (a:sa) ps as
\end{code}



\subsection{Parameter Management}


\begin{code}
paramwalk :: (i -> i) -> (i -> a -> b) -> i -> [a] -> [b]
paramwalk _ _ _ [] = []
paramwalk upd f i (a:as) = f i a : paramwalk upd f (upd i) as

paramileave :: (i -> a -> (b,i)) -> i -> [a] -> ([b],i)
paramileave _ i [] = ([],i)
paramileave f i (a:as)
  = let (a',i1)   =  f i a
        (as',i')  =  paramileave f i1 as
    in (a':as',i')
\end{code}
