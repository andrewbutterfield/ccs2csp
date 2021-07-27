ilbls\section{Translate}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2020-21

LICENSE: BSD3, see file LICENSE at ccs2csp root
\end{verbatim}
\begin{code}
module Translate where
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Control
import Syntax
import Semantics

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = Translate.dbg ("\n@"++nm++":\n") x
\end{code}

Translation workflow:
$$
\framebox{CCS}
\stackrel{c2ccs\tau}{\rightarrow}
\framebox{CCSTau}
\stackrel{ix}{\rightarrow}
\stackrel{g^*}{\rightarrow}
\stackrel{conm}{\rightarrow}
\framebox{CCSTau}
\stackrel{tl}{\rightarrow}
\framebox{CSP}
\stackrel{\hide\{tau,a_{ij}\}}{\rightarrow}
\stackrel{ai2a}{\rightarrow}
\framebox{CSP}
$$

\subsection{CCS to CCSTau}

\begin{eqnarray*}
   c2ccs\tau(P|Q)
   &\defeq&
   (c2ccs\tau(P) ~|_T~ c2ccs\tau(Q))
   \hide_T
   \{\tau[a|\bar a] \mid a \in \Alf P, \bar a \in \Alf Q\}
\\ c2ccs\tau(F(P_1,\dots,P_n))
   &\defeq&
   F(c2ccs\tau(P_1),\dots,c2ccs\tau(P_n))
\\ && F \mbox{ covers } 0, X, \restrict, \alpha., \mu X., +
\end{eqnarray*}
\begin{code}
c2ccsT :: CCS -> CCSTau
c2ccsT (Comp ccs1 ccs2)
  = visibleTaus `CCStauHide` (ccs1 `CCStauPar` ccs2)
  where
    alf1 = alf ccs1
    alf2 = alf ccs2
    commonAlf = alf1 `S.intersection` (S.map pfxbar alf2)
    visibleTaus = S.map lbl2tau commonAlf
c2ccsT ccs = ccs
\end{code}

\newpage
\subsection{Pre-Indexing}

We implement $ix$ by simply passing around a number that is incremented
every time an index is generated.
\begin{code}
ix :: CCSTau -> CCSTau
ix = fst . ixFrom 1
\end{code}

$$
ix(\tau.P) = \tau.ix(P)
\qquad
ix(a.P) = a_i.ix_{-i}(P)
$$
\begin{code}
ixFrom i (CCSpfx pfx ccs) = (CCSpfx pfx' ccs',i'')
  where
    (pfx',i') = iPfx i pfx
    (ccs',i'') = ixFrom i' ccs
\end{code}

$$ ix(P+Q) = ix_1(P) + ix_2(Q) $$
\begin{code}
ixFrom i (Sum p1 p2) = (Sum p1' p2',i')
  where ([p1',p2'],i') = paramileave ixFrom i [p1,p2]
\end{code}

$$ ix(P ~|_T~ Q) = ix_1(P) ~|_T~  ix_2(Q) $$
\begin{code}
ixFrom i (CCStauPar p1 p2) = (CCStauPar p1' p2',i')
  where ([p1',p2'],i') = paramileave ixFrom i [p1,p2]
\end{code}

$$ ix(P\restrict \{a\}) = ix(P) \restrict \{ a_i \mid a_i \in \Alf ix(P)\} $$
\begin{code}
ixFrom i (Rstr es ccs) = (Rstr es' ccs',i')
  where
    (ccs',i') = ixFrom i ccs
    es' = S.map getlbl $ S.filter (cameFromIxLab es) $ alf ccs'
\end{code}

$$
ix(P\hide_T \{a\}) = ix(P) \hide_T \{ a_i \mid a_i \in \Alf ix(P)\}
\qquad
ix(P\hide_T \{\tau[a|\bar a]\} = ix(P))
$$
\begin{code}
ixFrom i (CCStauHide pfxs ccs) = (CCStauHide pfxs' ccs',i')
  where
    (ccs',i') = ixFrom i ccs
    pfxs' = S.filter (cameFromPfx pfxs) $ alf ccs'
\end{code}

$$ ix(P[f]) = ix(f(P)) $$
\begin{code}
ixFrom i (CCSren pfn ccs) = ixFrom i (doRename (endo pfn) ccs)
\end{code}

$$ ix(\mu X \bullet P) = \mu X \bullet ix(P) $$
\begin{code}
ixFrom i (CCSmu nm ccs) = (CCSmu nm ccs',i')
  where (ccs',i') = ixFrom i ccs
\end{code}

The rest are unchanged.
\begin{code}
ixFrom i ccs = (ccs,i)
\end{code}

Helper functions for $ix$ :
\begin{code}
iPfx :: Int -> CCS_Pfx -> (CCS_Pfx, Int)
iPfx i T = (T,i)
iPfx i (T' n _)  = (T' n (Two i (i+1)),i+2)
-- ix(t[a|a-bar]) = t[a12|a12-bar]
iPfx i (Lbl e) = (Lbl (iLbl i e), i+1)

iLbl :: Int -> IxLab -> IxLab
iLbl i (nm,_) = (nm,One i)
\end{code}

Here we implement $a_i \in \Alf ix(P)$ for $a$ in restricted or hidden set.
\begin{code}
cameFromIxLab :: (Set IxLab) -> CCS_Pfx -> Bool
cameFromIxLab es (Lbl e)  =  (root . fst) e `S.member` S.map (root . fst) es
cameFromIxLab _  _        =  False

cameFromPfx :: (Set CCS_Pfx) -> CCS_Pfx -> Bool
cameFromPfx pfxs pfx  =  cameFromIxLab (S.map getlbl $ S.filter isLbl pfxs) pfx

getlbl :: CCS_Pfx -> IxLab
getlbl (Lbl lbl)  =  lbl
\end{code}


Given a CCS term, return a mapping from events
to the set of indices associated with each event.
\begin{code}
type IxMap = Map Label (Set Index)
indexMap :: CCS -> IxMap
indexMap = iMap M.empty

iMap imap (CCSpfx (Lbl (nm,i)) ccs)  =  iMap imap' ccs
                     where imap'  =  insMapping nm i imap
iMap imap (CCSpfx  _ ccs)            =  iMap imap ccs
iMap imap (Sum p1 p2)             =  iSeqMap imap [p1,p2]
iMap imap (Comp p1 p2)           =  iSeqMap imap [p1,p2]
iMap imap (Rstr es ccs)           =  iMap imap ccs
iMap imap (CCSren _ ccs)             =  iMap imap ccs
iMap imap (CCSmu nm ccs)            =  iMap imap ccs
iMap imap ccs                     =  imap

iSeqMap imap []          =  imap
iSeqMap imap (ccs:ccss)  =  let imap' = iMap imap ccs in iSeqMap imap' ccss

insMapping :: Label -> Index -> IxMap -> IxMap
insMapping nm i imap
  = M.insertWith S.union nm (S.singleton i) imap
\end{code}

\newpage
\subsection{Using $g^*$ for Actions}

Defs. 4.2, 4.1 and end of 4.3, in [GEN].

\begin{eqnarray*}
   g\pi_2 &:& \Set(Act \times \Nat)\times (Act \times \Nat)
              \fun
              \Set(Act \times \Nat \times \Nat)
\\ g\pi_2(S,a_i) &\defeq&
   \{a_{ij} \mid \bar{a}_j \in S, i < j\}
                 \cup \{a_{ji} \mid \bar{a}_j \in S, j < i\}
\end{eqnarray*}
We assume the input indexed labels have single indices only.
\begin{code}
gsa2 :: Set IxLab -> IxLab -> Set IxLab
gsa2 iCtxt (a,One i) = gsa2' a i $ S.toList iCtxt
gsa2 _ e             = S.singleton e

gsa2' a i [] = S.empty
gsa2' a i ((a',One j):iCtxt)
  |  a == bar a' && i /= j  =  S.insert (i2event a i j) $ gsa2' a i iCtxt
gsa2' a i (_:iCtxt)         =  gsa2' a i iCtxt
\end{code}

We now have a series of overloadings of $g^*$
\begin{eqnarray*}
   g^* &:& \Set(Act \times \Nat)\times (Act \times \Nat)
           \fun
           \Set(Act \times \Nat)
           \cup
           \Set(Act \times \Nat \times \Nat)
\\ g^*(S,a_i) &\defeq& \{a_i\} \cup g\pi_2(S,a_i)
\end{eqnarray*}
\begin{code}
gsa :: Set IxLab -> IxLab -> Set IxLab
gsa iCtxt a = S.singleton a `S.union` gsa2 iCtxt a
\end{code}

\begin{eqnarray*}
  g^* &:& \Set(Act \times \Nat)\times \Set(Act \times \Nat)
          \fun
          \Set(Act \times \Nat)
\\ g^*(S,B) &\defeq& \bigcup\{ g^*(S,a_i) \mid a_i \in B \}
\end{eqnarray*}
\begin{code}
gsb :: Set IxLab -> Set IxLab -> Set IxLab
gsb iCtxt ilbls = S.unions $ S.map (gsa iCtxt) ilbls
\end{code}


\begin{eqnarray*}
   g^* &:& \Set(Act \times \Nat)
           \fun
           \Set(Act \times \Nat)
           \cup
           \Set(Act \times \Nat \times \Nat)
\\ g^*(S) &\defeq& S \cup \{a_{ij} \mid a_i, \bar{a}_j \in S, i < j\}
                  \cup \{a_{ji} \mid a_i, \bar{a}_j \in S, j < i\}
\end{eqnarray*}
\begin{code}
gs :: Set IxLab -> Set IxLab
gs iCtxt = iCtxt `S.union` (S.unions (S.map (gsa2 iCtxt) iCtxt))
\end{code}


\newpage
\subsection{Using $g^*$ for Processes}

Def 4.3, pp19--20 [GEN].

We have a well-formedness criteria for restriction,
in order for $g^*$ to work properly.
\begin{eqnarray*}
   wf(P\restrict B)
   &\defeq&
   B \subseteq \Alf P
   \land
   \forall a_i \in B \bullet \{a_k \mid a_k \in \Alf P\} \subseteq B
\end{eqnarray*}
\begin{code}
wfRes :: CCS -> Bool
wfRes _ = error "wfRes NYI"
\end{code}

Type signature for process $g^*$:
\begin{eqnarray*}
   g^* &:& \Set(Act \times \Nat)\times CCS
           \fun
           CCS\\ pre\!-\!g^*(S,P) &\defeq& S \cap \Alf P = \emptyset
\end{eqnarray*}
\begin{code}
gsp :: Set IxLab -> CCS -> CCS
\end{code}

Pre-condition for process $g^*$:
\begin{eqnarray*}
   pre\!-\!g^*(S,P) &\defeq& S \cap \Alf P = \emptyset
\end{eqnarray*}
\begin{code}
pre_gsp iCtxt ccs  =  S.null (iCtxt `S.union` alf ccs)
\end{code}

Definition of process $g^*$:
\begin{eqnarray*}
   g^*(S,0) &\defeq& 0
\\ g^*(S,\alpha.P) &\defeq& \Sigma_{b \in g^*(S,\alpha)} b.g^*(S,P)
\\ g^*(S,P+Q) &\defeq& g^*(S,P) + g^*(S,Q)
\\ g^*(S,P \mid_{ccs\tau} Q)
   &\defeq& g^*(S\cup\Alf Q, P) \mid_{ccs\tau} g^*(S\cup\Alf P, Q)
\\ g^*(S,P\restrict B)
   &\defeq&
   g^*(S,P)\restrict g^*(S,B)
   % \cup
   % \{\alpha_{ij}\mid \alpha_i \in B, \bar\alpha_j \in S\}
\\ g^*(S,P[f]) &\defeq& (g^*(S,P))[f]
\\ g^*(S,X) &\defeq& X
\\ g^*(S,\mu X.P) &\defeq& \mu X . g^*(S,P)
\end{eqnarray*}

\begin{code}
gsp _    Zero                   =  Zero
gsp _    v@(CCSvar _)             =  v
gsp iCtxt (Sum ccs1 ccs2)       =  csum $ map (gsp iCtxt) [ccs1,ccs2]
gsp iCtxt (CCSmu x ccs)           =  CCSmu x $ gsp iCtxt ccs
gsp iCtxt (Rstr lbls ccs)       =  Rstr (gsb iCtxt lbls) (gsp iCtxt ccs)
gsp iCtxt (CCSren f ccs)           =  CCSren f $ gsp iCtxt ccs
gsp iCtxt (Comp ccs1 ccs2)  =  cpar $ walk (gpar iCtxt) [ccs1,ccs2]
                                        $ map getCCSLbls [ccs1,ccs2]
gsp iCtxt (CCSpfx (Lbl ilbl) ccs)  =  csum $ map (mkpfx (gsp iCtxt ccs))
                                             (S.toList $ gsa iCtxt ilbl)
gsp iCtxt (CCSpfx pfx ccs)         =  CCSpfx pfx $ gsp iCtxt ccs

-- helpers
getCCSLbls = S.map getlbl . S.filter isLbl . alf
gpar iCtxt p ilbls = gsp (S.unions $ iCtxt:ilbls) p
mkpfx p lbl = CCSpfx (Lbl lbl) p
\end{code}

At the top-level, we start with a empty indexed label context:
\begin{eqnarray*}
   g^* &:& CCS \fun CCS
\\ g^*(P) &\defeq& g^*(\emptyset,P)
\end{eqnarray*}
\begin{code}
gsp0 :: CCS -> CCS
gsp0 = gsp S.empty
\end{code}

\newpage
\subsection{Pre-Translation}


\begin{eqnarray*}
   c4star(S,P) &\defeq& g^*(S,ix(P))
\\ c2star(S,P)
   &\defeq&
   c4star(S,P)\restrict \{g\pi_2(S,a_i)\mid a_i \in \Alf ix(P)\}
\end{eqnarray*}
\begin{code}
c4star iCtxt ccs = gsp iCtxt $ ix ccs
c2star iCtxt ccs
 = let
     ccsi = ix ccs
     ccsa = getCCSLbls ccsi
     res = S.unions $ S.map (gsa2 iCtxt) ccsa
   in Rstr res $ gsp iCtxt ccsi
\end{code}

\subsection{Translate toward CSP}

Working from [GEN v19 Note5, Note6, Note6\_Update, Note7]

\begin{eqnarray*}
   conm &\defeq& \{ \tau\mapsto\tau, a\mapsto a, \bar a \mapsto a\}
\end{eqnarray*}

We partially implement this as a prefix transform $tlp$:
\begin{code}
tlp :: IxLab -> CSP_Pfx
tlp ix        =  tll ix
tll (nm,ix)   =  tln nm++tli ix
tln (Std nm)  =  nm
tln (Bar nm)  =  nm
tli None      =  ""
tli (One i)   =  "_"++show i
tli (Two i j) =  "_"++show i++"_"++show j
\end{code}


\begin{eqnarray*}
   tl(0)               &\defeq& STOP
\\ tl(\tau.P)          &\defeq& tl(P)
\\ tl(a.P)             &\defeq& tlp(a) \then tl(P)
\\ tl(P_1+P_2)         &\defeq& (tl(P_1) \Box tl(P_2))
                                \sqcap
                                \{ tl(\circ\tau(P_1)) \cup tl(\circ\tau(P_2)) \}
\\ tl(P |_{ccs\tau} Q) &\defeq& tl(P) \parallel_{\Alf tl(P)\cap{\Alf tl(Q)}} tl(Q)
\\ tl(P\restrict A)    &\defeq& tl(P) \parallel_{tlps(A)} STOP
\\ tl(X)               &\defeq& X
\\ tl(\mu X \bullet P) &\defeq& \mu X \bullet(tl(P))
\end{eqnarray*}
\textbf{Note: }
We might introduce a ``tau'' event ($tau$) to CSP
and use $tl(\tau.P)=tau.tl(P)$.

For $P$ a CCS process, recall ``after-tau'':
$
   \circ\tau(P) \defeq
     \{ P' \mid P \trans\tau P' \}
$.

We implement $conm$ within $tl$ here, by using $tlp$ above,
and dealing with the parallel sync and restriction sets explicitly below.
This covers all the places where labels occurs in CCS.
\begin{code}
tl :: CCS -> CSP
tl Zero                   =  Skip
tl (CCSpfx (Lbl il) ccs)  =  CSPpfx (tlp il) $ tl ccs
tl (CCSpfx _ ccs)         =  tl ccs
tl (CCSvar pname)         =  CSPvar pname
tl (Sum ccs1 ccs2)
  | null afters           =  ExtC csp1 csp2
  | otherwise             =  IntC (ExtC csp1 csp2) (ndc afters)
  where csp1 =  tl(ccs1)
        csp2 =  tl(ccs2)
        csps1 = map tl (afterTau ccs1)
        csps2 = map tl (afterTau ccs2)
        afters = csps1 ++ csps2
        ndc = foldl1 IntC
tl (Comp ccs1 ccs2) =  Par sync csp1 csp2
  where csp1  =  tl(ccs1)
        csp2  =  tl(ccs2)
        alf1  =  alpha csp1 -- S.map show $ alpha csp1
        alf2  =  alpha csp2 -- S.map show $ alpha csp2
        sync  =  alf1 `S.intersection` alf2
tl (Rstr ixs ccs)         =  Par (S.map tll ixs) (tl ccs) Stop
tl (CCSren rpairs ccs)    =  CSPren rpairs $ tl ccs
\end{code}


For $P$ a CCSTau process:
\begin{eqnarray*}
    t2csp(S,P) &\defeq& tl(conm(c4star(S,P)))
\end{eqnarray*}
\begin{code}
t2csp :: Set IxLab -> CCS -> CSP
t2csp iCtxt ccs = tl $ c4star iCtxt ccs
\end{code}


Top-level translation:
\begin{code}
ccs2csp :: CCS -> CSP
ccs2csp = t2csp S.empty
\end{code}

% \newpage
% \subsection{Old Stuff}
%
% \textbf{No Longer sure what the following is about}
%
% We use $\Sigma_i a_i . P$ as shorthand for $\Sigma_i (a_i . p)$,
% and we consider $a_{ij}$, $a_{ji}$ to be the same,
% with $i\neq j$.
% We also use $\alpha$ to
% range over $a,b,c,\dots$ and $\bar a,\bar b, \bar c,\dots$.
%
% \begin{eqnarray*}
%    pre\!-\!g_T(P) &=& namesOf(P) \subseteq dom(T)
% \\ g_T(0)
%    &\defeq& 0
% \\ g_T(\alpha_i.P)
%    &\defeq&
%    (\alpha_i + \Sigma_{j \in T(\bar \alpha)} \alpha_{ij}).g_T(P)
% \\ g_T(P|Q)
%    &\defeq&
%    \left( g_T(P) | g_T(Q) \right)
%    \setminus
%    \{\alpha_{ij} \mid \alpha_i \in P, \bar\alpha_j \in Q\}
% \\ g_T(P+Q)
%    &\defeq&
%    \left( g_T(P) + g_T(Q) \right)
% \\ g_T(P\setminus L)
%    &\defeq&
%    g_T(P)\setminus g'_T(L) \quad \textrm{can this be the identity?}
% \\ g_T(P[f])
%    &\defeq&
%    g_T(P)[f]
% \\ g_T(X)
%    &\defeq&
%    X
% \\ g_T(\mu X \bullet P)
%    &\defeq&
%    \mu X \bullet g_T(P)
% \end{eqnarray*}
%
% \begin{code}
% ccs2star :: CCS -> CCS
% ccs2star ccs
%  = c2star imap iccs
%  where  iccs = indexNames ccs
%         imap = indexMap iccs
%
%         c2star :: IxMap -> CCS -> CCS
%
%         c2star imap (CCSpfx (Lbl (alfa,(One i))) ccs)
%           = sumPrefixes imap alfa i $ c2star imap ccs
%
%         c2star imap (Comp ccs1 ccs2)
%           = rstr (syncPre $ map (S.toList . prefixesOf) [ccs1,ccs2])
%                  $ cpar $ map (c2star imap) [ccs1,ccs2]
%
%         c2star imap (Sum ccs1 ccs2) = csum $ map (c2star imap) [ccs1,ccs2]
%
%         c2star imap (Rstr es ccs) = Rstr es $ c2star imap ccs -- ? f es
%
%         c2star imap (CCSren f ccs) = CCSren f $ c2star imap ccs
%
%         c2star imap (CCSmu x ccs) = CCSmu x $ c2star imap ccs
%
%         c2star imap ccs = ccs -- 0, X
% \end{code}
%
% \begin{eqnarray*}
% \\ g_T(\alpha_i.P)
%    &\defeq&
%    (\alpha_i + \Sigma_{j \in T(\bar \alpha)} \alpha_{ij}).g_T(P)
% \end{eqnarray*}
% \begin{code}
% sumPrefixes :: IxMap -> Label -> Int -> CCS -> CCS
% sumPrefixes imap alfa i ccs
%   = case M.lookup (bar alfa) imap of
%       Nothing  ->  CCSpfx (Lbl (alfa,One i)) ccs
%       Just evts
%         -> let alpha2s = map (mkSyncEvt alfa i) $ S.toList evts
%            in csum $ map (affix ccs) ((alfa,One i):alpha2s)
%
% mkSyncEvt alfa i (One j) = i2event alfa i j
% affix ccs e = CCSpfx (Lbl e) ccs
% \end{code}
%
% \begin{eqnarray*}
%    g_T(P|Q)
%    &\defeq&
%    \left( g_T(P) | g_T(Q) \right)
%    \setminus
%    \{\alpha_{ij} \mid \alpha_i \in P, \bar\alpha_j \in Q\}
% \\ g_T(\Pi_p P_p)
%    &\defeq&
%    \left( \Pi_p g_T(P_p) \right)
%    \setminus
%    \{\alpha_{ij} \mid \alpha_i \in P_m, \bar\alpha_j \in P_n, m \neq n\}
% \end{eqnarray*}
% \begin{code}
% syncPre :: [[CCS_Pfx]] -> [IxLab]
% syncPre = concat . findSync syncPre1
%
% --
% syncPre1 :: [CCS_Pfx] -> [CCS_Pfx] -> [[IxLab]]
% syncPre1 ps1 ps2 = map (f ps1) ps2
%  where f ps1 p2 = concat $ map (syncPre2 p2) ps1
% \end{code}
%
% \begin{code}
% syncPre2 :: CCS_Pfx -> CCS_Pfx -> [IxLab]
% syncPre2 (Lbl (Std m,One i)) (Lbl (Bar n,One j)) | m == n  =  syncE m i j
% syncPre2 (Lbl (Bar m,One i)) (Lbl (Std n,One j)) | m == n  =  syncE m i j
% syncPre2 _                   _                             =  []
%
% syncE s i j = [i2event (Std s) i j]
% \end{code}
%
%
% We need the following
% \begin{code}
% findSync :: (a -> a -> [b]) -> [a] -> [b]
% findSync op [] = []
% findSync op [_] = []
% findSync op (as:ass) = concat (map (op as) ass) ++ findSync op ass
% \end{code}
