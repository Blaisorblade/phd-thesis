% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

% \chapter{Incrementalizing programs}

% \chapter{Incrementalizing primitives}
% \section{A generalized group fold}
% \pg{Status: very tentative}
% We have discussed how groups can induce change structures in one way (with
% change type |da| equal to base type |a| and with the support of the group).%
% \footnote{Technically, to consider a group on programs, we need to use groups in
%   the syntactic category of types and programs.}

% A more general way takes a group uses a base type |a|, a group |G = (da, +, -,
% e)|, and a function |`oplus` : a -> da -> a| and defines a change structure
% where:
% \begin{itemize}
% \item the change type is constantly |da| for all elements of |a|;
% \item the associative change composition operation |`ocompose` : da -> da -> da|
%   is given by the group operation |+|;
% \item the nil change is the neutral group element |e|;
% \item change application is given by |`oplus`|.
% \end{itemize}

% In such a change structure we obtain a few peculiar extra members:
% \begin{itemize}
% \item the unary group inverse operation |-| doubles as a change negation
%   operation, such that |dx `ocompose` (- dx) = nil|.
% \end{itemize}

% We can additionally require an operation |elLift: A -> DA| lifting elements to changes.

% Given such a change structure, we can define a \emph{group fold} over a
% collection type constructor |T|: |groupFold: (Group da, ChangeStruct a da) => (a
% -> da) -> T a -> da|. Such an operation would generalize the one used by
% \citet{CaiEtAl2014ILC}, dropping the requirement that |a = da|. Thanks to change negation, a
% derivative |dgroupFold| could react to the removal of collection elements.

\chapter{Incrementalizing more programs}
\label{ch:inc-more-programs}
\pg{Only a very rough sketch for now}

In the previous chapters we have shown how to apply finite differencing to
programs with first-class functions. With finite differencing we can
incrementalize a few programs, but for others we run into problems:

\begin{enumerate}
\item The incremental computation does not have accesss to intermediate results
  from the original computation.
\item Since function changes are represented as functions, they cannot be
  inspected at runtime, preventing a few optimizations. For instance, applying a
  derivative to a nil change always produces a nil change, but we never take
  advantage of this to optimize derivatives, except sometimes at compile time.
\item Applying a derivative to a nil change always produce a nil change, but we
  never take advantage of this to optimize derivatives, except sometimes at
  compile time.
% \item No support for change composition: there is no direct way to compose a
%   sequence of changes |dx1, dx2, dx3, ...| across |x0, x1, x2, x3, ...| and
%   produce a single change, except by applying all those changes and computing a
%   difference with |x0 `oplus` dx1 `oplus` dx2 `oplus` dx3|.
\item Change structures must provide a difference operation, even though most
  often we are not supposed to use it.
\end{enumerate}
 % In fact, while a function change can replace
 %  a function with an arbitrary other function, actual changes often simply
 %  replace a closure with another closure using the same code but closing over a
 %  changed environment.

%include defunc.lhs
\chapter{Misc to integrate}
\subsection{Applying function changes to composed changes}
\pg{Move somewhere else. About lists?}
\pg{No subscript for |`ocompose`| here?}

\pg{Status: this is still text where I figure this out.}

To implement change composition |da1 `ocompose` da2|, we can represent changes
by lists of individual or \emph{atomic} changes. Change composition is then just
concatenation. We can then extend functions on atomic changes to functions on
changes. Next, we show how.

Imagine, in the setting of PLDI'14 extended with change composition, applying
one function change |df| to a composed argument change |da1 `ocompose` da2|,
where |f1 `oplus` df = f2|, |a1 `oplus` da1 = a2| and |a2 `oplus` da2 = a3|. We
want to compute incrementally the difference |db| between |f2 a3| and |f1 a1|.
The change |db1 = df a1 da1| goes from |f1 a1| to |f2 a2|. With a change |db2|
going from |f2 a2| to |f2 a3|, we can assemble the desired change as |db = db1
`ocompose` db2|.

However, to compute |db2| incrementally we cannot apply |df| to |da2|: |df a2
da2| gives the difference between |f1 a2| and |f2 a3|, but |db2| should be the
difference between |f2 a2| and |f2 a3|. Hence, we need to compute a nil change
for |f2|.

Doing that efficiently from the available elements is hard. However, with
defunctionalized changes this becomes much easier (assuming the function code
stays the same). Given the code of |f1| and |f2| we can produce a derivative for
the base function; we can then combine that derivative with an updated
environment. \pg{continue and clarify}
% Why are these methods around?
% \begin{code}
% derPreDFun1 :: (ChangeStruct a, NilChangeStruct env) => Code env a b -> env -> Dt^env -> a -> Dt^a -> Dt^b
% derPostDFun1 :: (ChangeStruct a, NilChangeStruct env) => Code env a b -> env -> Dt^env -> a -> Dt^a -> Dt^b
% \end{code}

\subsection{Replacing functions without necessarily recomputing}
If a function change replaces a base function with a different one, in general
we must simply call the new function and produce a replacement change. However,
this can be wasteful if we replace a function by a similar one.

Luckily we can add special cases to |derApplyDFun1|. To get started, suppose for
instance we replace |(+1)| by |(+2)|. Instead of replacing all the results, we
can add a specialized pattern match producing an equivalent change that however
is not a replacement one:

\begin{code}
derApplyDFun1 :: (ChangeStruct a, NilChangeStruct env) =>
  Code env a b -> env -> DCode env a b -> Dt^env -> a -> Dt^a -> Dt^b
derApplyDFun1 (P Add1 _()) (DP (Replace Add2) ()) = +1 -- As a change
...
derApplyDFun1 (P _f _env) (DP (Replace newF) newEnv) = oreplace (newF newEnv)
\end{code}

This is enabled by defunctionalizing both base functions and changes.

\section{Mapping changeable functions over sequences}

\pg{By far not done.}

In this section we demonstrate how we can incrementalize by hand |map| and
|concatMap| over collections, in a way that is compatible with and allows for
``deep'' changes to single sequence elements.

We assume from previous sections knowledge of:
\begin{itemize}
\item cache-passing style
\item defunctionalized function changes
\end{itemize}

and assume, for simplicity, the following type of sequence changes:
\pg{single or atomic?}
\begin{code}
data SeqSingleChange a
  =  Insert    { idx :: Int, x :: a }
  |  Remove    { idx :: Int }
  |  ChangeAt  { idx :: Int, dx :: Dt ^ a }
data SeqChange a = Seq (SeqSingleChange a)
type Dt (Seq a) = SeqChange a
\end{code}

Let us incrementalize |ys = map f xs : Seq b|, with |f : a -> b| and |xs : Seq
a|. We want to compute the output change |dys| when |xs| changes by |dxs| and
|f| changes by |df|.

If |df| is not a nil change we must apply it to each element of |xs| to compute
changes to each element of |ys|.\pg{Write definition using change composition.}
Since looping over |xs| would take linear time,
we want to avoid it if posssible: we need to detect whether |df| is a nil change
or not. Sometimes we can detect this statically\pg{reference to section}, but
more often we only detect this dynamically. So we assume that |Dt (a -> b)|
supports detecting nil changes via |isNil|.

Let us first assume that |df| is a nil change; let us moreover assume that |dxss
: Dt (Seq a)| contains only one simple change |dxs : SeqSingleChange a|. If
|dxs| simply adds or removes an element |x|, we can simply add or remove the
corresponding element |y = f x| from |ys|.
%
Assume now |dxs| changes an element, that is, |dxs = ChangeAt idx dx| where |idx|
is the index of the changed element |x = xs !! idx|, and |dx : Dt ^ el| is the
element change. The output change will then be |ChangeAt idx dy| where |dy = df x
dx|. Producing this change is a self-maintainable process only if |df| is itself
self-maintainable.

Since |f| might produce intermediate results that are needed by the derivative,
we should use a cache-passing version of |f|, and adapt |map| accordingly. And
|df| might not be self-maintainable, so we better make the base input available
to |dmap| by storing it in a cache for |map|. Hence we use as interface:

\begin{code}
data MapCache a b cache = ...
getFc :: MapCache a b cache -> Fun a b cache
getCaches :: MapCache a b cache -> Seq cache
mapC :: Fun a b cache -> Seq a -> (Seq b, MapCache a b cache)

dmapC ::
  DFun a b cache1 cache2 -> Dt (Seq a) ->
  MapCache a b cache -> (Dt (Seq b), MapCache a b cache)
\end{code}

So the implementation of |dmapCSingle| for an element change is:
\pg{typecheck this}
\begin{code}
dmapCSingle ::
  DFun a b cache1 cache2 -> SeqSingleChange a ->
  MapCache a b cache -> (Dt (Seq b), MapCache a b cache)
dmapCSingle dfc (ChangeAt idx dx) mapCache1 = (singleton (ChangeAt idx dy), mapCache2)
  where
    caches1 = getCaches mapCache1
    cx1 = caches1 `index` idx
    (dy, cx2) = dfc dx cx
    caches2 = update idx cx2 caches1
    mapCache2 = mapCache1 { getCaches = caches2 }
\end{code}
where we assume the following interface for operating on sequences (as supplied by |Data.Seq|):
\begin{code}
singleton :: a -> Seq a
index :: Seq a -> Int -> a
update :: Int -> a -> Seq a -> Seq a
\end{code}

\chapter{Static caching}
\label{sec:static-caching}
\pg{Write it!}

\pg{It'd be nice to type the smart approach to cache type variables. We can't
  generally. It would be good to characterize when it can be used, but we don't
  do that either. Instead, we just show examples of what would be possible.}
%
\pg{We conjecture that we can type using free type variables:
  \begin{itemize}

  \item second-class uses of higher-order functions (such as in map, flatMap, and so on)
  \item but not first-class uses
  \item we can probably thread type variables where possible and use the packing trick elsewhere.
\end{itemize}
}

\pg{In fact, assume a combinator |mapInt : (Int -> Int) -> List Int -> List
  Int|. We can't prove that |mapInt f| uses its argument as we expect, maybe it
  does nothing on the list elements, or maybe it maps |inc| on (some of) them.
  Many such behaviors are allowed by its type; but our translation turns these
  |mapInt| variants with the same type into functions with different cache
  types. Mapping different functions over different elements produces.}

\input{pldi14/sec-rw}
\chapter{Conclusions}
\pg{Plan for things that complete the original paper's story: add them by
  revising that text and in that chapter.}
