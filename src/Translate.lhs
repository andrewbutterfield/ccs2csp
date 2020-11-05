\section{Translate}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Translate where
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Syntax

--import Debug.Trace
--dbg msg x = trace (msg++show x) x
\end{code}

\subsection{Control}


This generic control code belongs in a distinct module.

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


\subsection{Pre-Indexing}

Here we attach single indices to every standard or barred event,
numbered from 0 upwards.
Currently we fail if tagged-taus are found.
\begin{code}
indexNames :: CCS -> CCS
indexNames = fst . iFrom 0

iFrom i (Pfx  pfx ccs) = (Pfx (iPfx i pfx) ccs',i')
  where (ccs',i') = iFrom (i+1) ccs
iFrom i (Sum ccss) = (Sum ccss',i')
  where (ccss',i') = paramileave iFrom i ccss
iFrom i (Par ccss) = (Par ccss',i')
  where (ccss',i') = paramileave iFrom i ccss
iFrom i (Rstr es ccs) = (Rstr es ccs',i')
  where (ccs',i') = iFrom i ccs
iFrom i (Ren pfn ccs) = (Ren pfn ccs',i')
  where (ccs',i') = iFrom i ccs
iFrom i (Rec nm ccs) = (Rec nm ccs',i')
  where (ccs',i') = iFrom i ccs
iFrom i ccs = (ccs,i)

iPfx :: Int -> Prefix -> Prefix
iPfx i T = T
iPfx i (Evt e) = Evt (ePfx i e)
iPfx i pfx@(T' _) = error ("pre-indexing CCS term with tagged-tau "++show pfx)

ePfx :: Int -> Event -> Event
ePfx i (nm,_) = (nm,One i)
\end{code}

Given a CCS term, return a mapping from events
to the set of indices associated with each event.
\begin{code}
type IxMap = Map Name (Set Index)
indexMap :: CCS -> IxMap
indexMap = iMap M.empty

iMap imap (Pfx (Evt (nm,i)) ccs)  =  iMap imap' ccs
                     where imap'  =  insMapping nm i imap
iMap imap (Pfx  _ ccs)            =  iMap imap ccs
iMap imap (Sum ccss)              =  iSeqMap imap ccss
iMap imap (Par ccss)              =  iSeqMap imap ccss
iMap imap (Rstr es ccs)           =  iMap imap ccs
iMap imap (Ren _ ccs)             =  iMap imap ccs
iMap imap (Rec nm ccs)            =  iMap imap ccs
iMap imap ccs                     =  imap

iSeqMap imap []          =  imap
iSeqMap imap (ccs:ccss)  =  let imap' = iMap imap ccs in iSeqMap imap' ccss

insMapping :: Name -> Index -> IxMap -> IxMap
insMapping nm i imap
  = M.insertWith S.union nm (S.singleton i) imap
\end{code}

\subsubsection{Using $g^*$ for Actions}

This has been revised considerably in [GEN v19 Note4].

\begin{eqnarray*}
   g^* &:& \Set(Act \times \Nat)
           \fun
           \Set(Act \times \Nat)
           \cup
           \Set(Act \times \Nat \times \Nat)
\\ g^*(S) &\defeq& A \cup \{a_{ij} \mid a_i, \bar{a}_j \in S, i < j\}
                  \cup \{a_{ji} \mid a_i, \bar{a}_j \in S, j < i\}
\\
\\ g^*(S,a_i) &\defeq& \{a_i\} \cup g\pi2(S,a_i)
\\ g\pi2(S,a_i) &\defeq&
   \{a_{ij} \mid \bar{a}_j \in S, i < j\}
                 \cup \{a_{ji} \mid \bar{a}_j \in S, j < i\}
\end{eqnarray*}
Note that $g^*(\{\},a_i) = \{a_i\}$.

\begin{code}
gsa :: Set Event -> Set Event
gsa evts = evts `S.union` (S.unions (S.map (gsa2 evts) evts))

gas1 = S.singleton

gsa2 evts evt@(a,One i) = gsa2' a i $ S.toList evts
gsa2 _ e = error ("gsa2: not a singly indexed event "++show e)

gsa2' a i [] = S.empty
gsa2' a i ((a',One j):evtl)
  |  a == bar a' && i /= j  =  S.insert (i2event a i j) $ gsa2' a i evtl
gsa2' a i (_:evtl)          =  gsa2' a i evtl
\end{code}

We assume the input events are single prefixes only.

\subsubsection{Using $g^*$ for Processes}


Based on [GEN v19 Note4] annot and [VK Note 4 Nov 2020]

The notation in [VK] Note 4 uses $P[g^*,A]$ for the application
of $g^*$ to process $P$ with ``context`` $A$.

\begin{quote}
``
Def. $P[g^*,A]$ is defined when $A \cap Ab(P) = \emptyset$
and
\begin{eqnarray*}
   0[g^*,A]  &\defeq& 0
\\ P \mid Q [g^*,A]
   &\defeq&
   P[g^*,A \uplus Ab(Q)] \mid Q [g^*,A \uplus Ab(P)]
\\ P \upharpoonright B [g^*,A]
  &\defeq&
  P[g^*,A] \upharpoonright g^*_A(B)
\end{eqnarray*}
'' [VK, Note 4]
\end{quote}

[GEN v19 Note 4] responds thus:

\begin{eqnarray*}
   g^*(S,0) &\defeq& 0
\\ g^*(S,\alpha.P) &\defeq& \Sigma_{b \in g^*(S,\alpha)} b.g^*(S,P)
\\ g^*(S,P+Q) &\defeq& g^*(S,P) + g^*(S,Q)
\\ g^*(S,P \mid_{ccs\tau} Q)
   &\defeq& g^*(S\cup\Alf Q, P) \mid_{ccs\tau} g^*(S\cup\Alf P, Q)
\\ g^*(S,P\restrict A) &\defeq& g^*(S,P)\restrict g^*(S,A)
\\ g^*(S,P \hide A) &\defeq& g^*(S,P) \hide g^*(S,A)
\\ g^*(S,\mu X.P) &\defeq& \mu X . g^*(S,P)
\\
\\ g^*(S,A) &\defeq& \{g^*(S,a) \mid a \in A \}
\end{eqnarray*}

\begin{code}
gsp :: Set Event -> CCS -> CCS
gsp _    Zero  =  Zero
gsp _    x@(PVar _)  =  x
gsp evts (Sum ccss) = Sum $ map (gsp evts) ccss
gsp evts (Rec x ccs) = Rec x $ gsp evts ccs
gsp evts (Rstr evtl ccs) = Rstr (gse evts evtl) $ gsp evts ccs
gsp evts ren@(Ren f ccs) = error ("gsp not defined for renaming: "++show ren)
gsp evts prfx@(Pfx (Evt alpha) ccs)
  = Sum $ map (mkpre (gsp evts ccs)) $ S.toList $ gsa2 evts alpha
  where mkpre p alpha = Pfx (Evt alpha) p
gsp evts (Pfx evt ccs) = error ("gsp not define for "++show evt)
gsp evts par@(Par csss) = error ("gsp NYfI: "++show par)

gsp0 = gsp S.empty

gse evts evtl = concat $ map (S.toList . gsa2 evts) evtl
\end{code}



\subsection{Translate toward CSP}

This is based on whiteboard notes by Vasileios Koutavas,
on MS Teams, on 24th Sep 2020.

We use $\Sigma_i a_i . P$ as shorthand for $\Sigma_i (a_i . p)$,
and we consider $a_{ij}$, $a_{ji}$ to be the same,
with $i\neq j$.
We also use $\alpha$ to
range over $a,b,c,\dots$ and $\bar a,\bar b, \bar c,\dots$.

\begin{eqnarray*}
   pre\!-\!g_T(P) &=& namesOf(P) \subseteq dom(T)
\\ g_T(0)
   &\defeq& 0
\\ g_T(\alpha_i.P)
   &\defeq&
   (\alpha_i + \Sigma_{j \in T(\bar \alpha)} \alpha_{ij}).g_T(P)
\\ g_T(P|Q)
   &\defeq&
   \left( g_T(P) | g_T(Q) \right)
   \setminus
   \{\alpha_{ij} \mid \alpha_i \in P, \bar\alpha_j \in Q\}
\\ g_T(P+Q)
   &\defeq&
   \left( g_T(P) + g_T(Q) \right)
\\ g_T(P\setminus L)
   &\defeq&
   g_T(P)\setminus g'_T(L) \quad \textrm{can this be the identity?}
\\ g_T(P[f])
   &\defeq&
   g_T(P)[f]
\\ g_T(X)
   &\defeq&
   X
\\ g_T(\mu X \bullet P)
   &\defeq&
   \mu X \bullet g_T(P)
\end{eqnarray*}

\begin{code}
ccs2star :: CCS -> CCS
ccs2star ccs
 = c2star imap iccs
 where iccs = indexNames ccs
       imap = indexMap iccs

c2star :: IxMap -> CCS -> CCS

c2star imap (Pfx (Evt (alfa,(One i))) ccs)
  = sumPrefixes imap alfa i $ c2star imap ccs

c2star imap (Par ccss)
  = rstr (syncPre $ map (S.toList . prefixesOf) ccss)
         $ Par $ map (c2star imap) ccss

c2star imap (Sum ccss) = Sum $ map (c2star imap) ccss

c2star imap (Rstr es ccs) = Rstr es $ c2star imap ccs -- ? f es

c2star imap (Ren f ccs) = Ren f $ c2star imap ccs

c2star imap (Rec x ccs) = Rec x $ c2star imap ccs

c2star imap ccs = ccs -- 0, X
\end{code}

\begin{eqnarray*}
\\ g_T(\alpha_i.P)
   &\defeq&
   (\alpha_i + \Sigma_{j \in T(\bar \alpha)} \alpha_{ij}).g_T(P)
\end{eqnarray*}
\begin{code}
sumPrefixes :: IxMap -> Name -> Int -> CCS -> CCS
sumPrefixes imap alfa i ccs
  = case M.lookup (bar alfa) imap of
      Nothing  ->  Pfx (Evt (alfa,One i)) ccs
      Just evts
        -> let alpha2s = map (mkSyncEvt alfa i) $ S.toList evts
           in Sum $ map (affix ccs) ((alfa,One i):alpha2s)

mkSyncEvt alfa i (One j) = i2event alfa i j
affix ccs e = Pfx (Evt e) ccs
\end{code}

\begin{eqnarray*}
   g_T(P|Q)
   &\defeq&
   \left( g_T(P) | g_T(Q) \right)
   \setminus
   \{\alpha_{ij} \mid \alpha_i \in P, \bar\alpha_j \in Q\}
\\ g_T(\Pi_p P_p)
   &\defeq&
   \left( \Pi_p g_T(P_p) \right)
   \setminus
   \{\alpha_{ij} \mid \alpha_i \in P_m, \bar\alpha_j \in P_n, m \neq n\}
\end{eqnarray*}
\begin{code}
syncPre :: [[Prefix]] -> [Event]
syncPre = concat . findSync syncPre1

--
syncPre1 :: [Prefix] -> [Prefix] -> [[Event]]
syncPre1 ps1 ps2 = map (f ps1) ps2
 where f ps1 p2 = concat $ map (syncPre2 p2) ps1
\end{code}

\begin{code}
syncPre2 :: Prefix -> Prefix -> [Event]
syncPre2 (Evt (Std m,One i)) (Evt (Bar n,One j)) | m == n  =  syncE m i j
syncPre2 (Evt (Bar m,One i)) (Evt (Std n,One j)) | m == n  =  syncE m i j
syncPre2 _                   _                             =  []

syncE s i j = [i2event (Std s) i j]
\end{code}


We need the following
\begin{code}
findSync :: (a -> a -> [b]) -> [a] -> [b]
findSync op [] = []
findSync op [_] = []
findSync op (as:ass) = concat (map (op as) ass) ++ findSync op ass
\end{code}
