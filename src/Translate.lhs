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
c2ccsT (CCSpfx evt ccs)  =  CCSpfx evt $ c2ccsT ccs
c2ccsT (Sum ccs1 ccs2)   =  Sum (c2ccsT ccs1) (c2ccsT ccs2)
c2ccsT (Rstr lbls ccs)   =  Rstr lbls $ c2ccsT ccs
c2ccsT (CCSren rp ccs)   =  CCSren rp $ c2ccsT ccs
c2ccsT (CCSmu nm ccs)    =  CCSmu nm $  c2ccsT ccs
c2ccsT (Comp ccs1 ccs2)
  = visibleTaus `CCStauHide` (ccs1 `CCStauPar` ccs2)
  where
    alf1 = alf ccs1
    alf2 = alf ccs2
    commonAlf = alf1 `S.intersection` (S.map pfxbar alf2)
    visibleTaus = S.map lbl2tau commonAlf
c2ccsT ccs               =  ccs  -- Zero, CCSvar
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
iPfx :: Int -> Event -> (Event, Int)
iPfx i T = (T,i)
iPfx i (T' n _)  = (T' n (Two i (i+1)),i+2)
-- ix(t[a|a_bar]) = t[a12|a12_bar]
iPfx i (Lbl e) = (Lbl (iLbl i e), i+1)

iLbl :: Int -> IxLab -> IxLab
iLbl i (nm,_) = (nm,One i)
\end{code}

Here we implement $a_i \in \Alf ix(P)$ for $a$ in restricted or hidden set.
\begin{code}
cameFromIxLab :: (Set IxLab) -> Event -> Bool
cameFromIxLab es (Lbl e)  =  (root . fst) e `S.member` S.map (root . fst) es
cameFromIxLab _  _        =  False

cameFromPfx :: (Set Event) -> Event -> Bool
cameFromPfx pfxs pfx  =  cameFromIxLab (S.map getlbl $ S.filter isLbl pfxs) pfx

getlbl :: Event -> IxLab
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
\\ g^*(S,B) &\defeq& \bigcup\{ g^*(S-\{a_i\},a_i) \mid a_i \in B \}
\end{eqnarray*}
\begin{code}
gsb :: Set IxLab -> Set IxLab -> Set IxLab
gsb iCtxt ilbls = S.unions $ S.map (gsb' iCtxt) ilbls
gsb' iCtxt lbl = gsa (iCtxt S.\\ S.singleton lbl) lbl
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


% We have a well-formedness criteria for restriction,
% in order for $g^*$ to work properly.
% \begin{eqnarray*}
%    wf(P\restrict B)
%    &\defeq&
%    B \subseteq \Alf P
%    \land
%    \forall a_i \in B \bullet \{a_k \mid a_k \in \Alf P\} \subseteq B
% \end{eqnarray*}
% \begin{code}
% wfRes :: CCS -> Bool
% wfRes _ = error "wfRes NYI"
% \end{code}

Type signature for process $g^*$:
\begin{eqnarray*}
   g^* &:& \Set(Act \times \Nat)\times CCS
           \fun
           CCS
\end{eqnarray*}
\begin{code}
gsp :: Set IxLab -> CCS -> CCS
\end{code}

Pre-condition for process $g^*$:
\begin{eqnarray*}
   pre\!-\!g^*(S,P)
   &\defeq&
   S \cap \Alf P = \emptyset
   \mbox{ and $P$ is a result of the application of $ix$.}
\end{eqnarray*}
\begin{code}
pre_gsp iCtxt ccs  =  S.null (iCtxt `S.union` alf ccs)
\end{code}

Definition of process $g^*$:
\begin{eqnarray*}
   g^*(S,0) &\defeq& 0
\\ g^*(S,\alpha.P) &\defeq& \Sigma_{b \in g^*(S,\alpha)} b.g^*(S,P)
\\ g^*(S,P+Q) &\defeq& g^*(S,P) + g^*(S,Q)
\\ g^*(S,P \mid_T Q)
   &\defeq& g^*(S\cup\Alf Q, P) \mid_T g^*(S\cup\Alf P, Q)
\\ g^*(S,P\restrict B)
   &\defeq&
   g^*(S,P)\restrict g^*(S,B)
\\ g^*(S, P ~\hide_T~ B)
   &\defeq&
   g*(S,P) ~\hide_T~ g^*(S \cup B,B)
   % \cup
   % \{\alpha_{ij}\mid \alpha_i \in B, \bar\alpha_j \in S\}
\\ g^*(S,P[f]) &\defeq& (g^*(S,f(P)))
\\ g^*(S,X) &\defeq& X
\\ g^*(S,\mu X.P) &\defeq& \mu X . g^*(S,P)
\end{eqnarray*}

\begin{code}
gsp _    Zero                      =  Zero
gsp _    v@(CCSvar _)              =  v
gsp iCtxt (Sum ccs1 ccs2)          =  csum $ map (gsp iCtxt) [ccs1,ccs2]
gsp iCtxt (CCSmu x ccs)            =  CCSmu x $ gsp iCtxt ccs
gsp iCtxt (Rstr lbls ccs)          =  Rstr (gsb iCtxt lbls) (gsp iCtxt ccs)
gsp iCtxt (CCSren f ccs)           =  gsp iCtxt $ doRename (endo f) ccs
gsp iCtxt (CCStauHide pfxs ccs)
  =  CCStauHide (S.map Lbl $ gsb (iCtxt `S.union` b) b) $ gsp iCtxt ccs
  where b = S.map getlbl $ S.filter isLbl pfxs
gsp iCtxt (CCStauPar ccs1 ccs2)   =  ctpar $ walk (gpar iCtxt) [ccs1,ccs2]
                                        $ map getCCSLbls [ccs1,ccs2]
gsp iCtxt (CCSpfx (Lbl ilbl) ccs)  =  csum $ map (mkpfx (gsp iCtxt ccs))
                                             (S.toList $ gsa iCtxt ilbl)
gsp iCtxt (CCSpfx pfx ccs)         =  CCSpfx pfx $ gsp iCtxt ccs
gsp iCtxt (Comp _ _) = error "g*(Comp...) is invalid."

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

\subsection{Translate toward CSP}

We first modify some CCS prefixes to appear more like
their eventual CSP forms.
\begin{eqnarray*}
   conm
   &\defeq&
   \{ \tau\mapsto\tau
    , a_i\mapsto a_i
    , \bar a_i \mapsto \bar a_i
    , a_{ij} \mapsto a_{ij}
    , \bar a_{ij} \mapsto a_{ij}
    , \tau[a_{ij}|\bar a_{ij}] \mapsto a_ij
   \}
\end{eqnarray*}
Note
that only $\tau[a_{ij}|\bar a_{ij}]$ and $\bar a_{ij}$ prefixes are altered,
in each case to $a_{ij}$.
\begin{code}
conm :: Event -> Event
conm (Lbl (Bar nm,ix@(Two _ _)))  =  Lbl (Std nm,ix)
conm (T' nm ix)                   =  Lbl (Std nm,ix)
conm ccs_pfx                      =  ccs_pfx
\end{code}
There are no more explicit $\tau[\dots]$ prefixes.
We invoke $conm$ here,
(and $ai2a$, see below)
from within $tl$ as we do the translation.

\subsubsection{$tl$ --- from CCStau to CSP}

Now, the move to CSP.
\begin{code}
tauInCSP = Lbl (Std "TAU",None)
tl :: CCSTau -> CSP
\end{code}

\begin{eqnarray*}
   tl(0)               &\defeq& STOP
\\ tl(\tau.P)          &\defeq& tau \then tl(P)
\\ tl(a.P)             &\defeq& tlix(a) \then tl(P)
\\ tl(P+Q)             &\defeq& (tl(P_1) ~\Box~ tl(P_2))
\\ tl(P \hide_T B)     &\defeq& tl(P) \hide B
\\ tl(P\restrict A)    &\defeq& tl(P) \parallel_{tlps(A)} STOP
\\ tl(X)               &\defeq& X
\\ tl(\mu X \bullet P) &\defeq& \mu X \bullet(tl(P))
\\ tl(P[f])            &\defeq& tl(f(P))
\\ tl(P |_T Q)         &\defeq& tl(P) \parallel_{\Alf tl(P)\cap{\Alf tl(Q)}} tl(Q)
\end{eqnarray*}
\begin{code}
tl Zero                   =  Stop
tl (CCSpfx T ccs)         =  CSPpfx tauInCSP $ tl ccs
tl (CCSpfx pfx ccs)       =  CSPpfx (ai2a $ conm pfx) $ tl ccs
tl (CCSvar pname)         =  CSPvar pname
tl (Sum ccs1 ccs2)        =  ExtC (tl ccs1) (tl ccs2)
tl (CCStauHide es ccs)    =  Hide (S.map ai2a es) $ tl ccs
tl (Rstr ixs ccs)         =  Par (S.map (ai2a . Lbl) ixs) (tl ccs) Stop
tl (CCSren rpairs ccs)    =  tl $ doRename (endo rpairs) ccs
tl (CCStauPar ccs1 ccs2)  =  Par sync csp1 csp2
  where csp1  =  tl(ccs1)
        csp2  =  tl(ccs2)
        alf1  =  alpha csp1 -- S.map show $ alpha csp1
        alf2  =  alpha csp2 -- S.map show $ alpha csp2
        sync  =  S.map ai2a (alf1 `S.intersection` alf2)
\end{code}

For $P$ a CCSTau process:
\begin{eqnarray*}
    t2csp(P) &\defeq& (tl \circ conm \circ g^* \circ ix)(P) \hide \setof{tau}
\end{eqnarray*}
\begin{code}
t2csp :: CCSTau -> CSP
t2csp ccs = Hide (S.singleton tauInCSP) $ tl $ gsp S.empty $ ix ccs
\end{code}

The final step hides synchronisation names (doubly-indexed)
and removes indices from singly-indexed events.
\begin{eqnarray*}
   ai2a
   &\defeq& \setof{a_i \mapsto a, \bar a_i \mapsto \bar a}
\end{eqnarray*}
\begin{code}
ai2a :: Event -> Event
ai2a (Lbl (lbl,(One _)))  =  Lbl (lbl,None)
ai2a pfx                  =  pfx
\end{code}
We can apply this as translation to CSP is done.

\begin{eqnarray*}
   ccs2csp(P)
   &\defeq&
   (ai2a \circ t2csp \circ c2ccs\tau)(P)
   \hide
   \setof{a_{ij}\mid a_{ij} \in \Alf t2csp(c2ccs\tau(P))}
\end{eqnarray*}
\begin{code}
ccs2csp :: CCS -> CSP
ccs2csp ccs
  = Hide syncevts csp
  where
    csp = t2csp $ c2ccsT ccs
    syncevts = S.filter dblIndexes $ alpha csp
    dblIndexes (Lbl (_,Two _ _))  =  True
    dblIndexes _                  =  False
\end{code}
