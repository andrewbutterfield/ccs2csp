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
