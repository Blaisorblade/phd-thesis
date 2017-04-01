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
\pg{Only a sketch for now}

While the basic framework we presented is significant, applying it in practice
to incrementalize programs is hard because of a few problems.
\begin{enumerate}
\item The incremental computation does not have accesss to intermediate results from the original computation.
\item Since function changes are represented as functions, the derivative cannot
  test if a function change is nil. In fact, while a function change can replace
  a function with an arbitrary other function, actual changes often simply
  replace a closure with another closure using the same code but closing over a
  changed environment.
\end{enumerate}

A few other annoyances include:
\begin{enumerate}
\item Applying a derivative to a nil change always produce a nil change, but we
  never take advantage of this to optimize derivatives, except sometimes at
  compile time.
\item No support change composition: there is no direct way to compose a
  sequence of changes |dx1, dx2, dx3, ...| across |x0, x1, x2, x3, ...| and
  produce a single change, except by applying all those changes and computing a
  difference with |x0 `oplus` dx1 `oplus` dx2 `oplus` dx3|.
\item Change structures must provide a difference operation, even though most
  often we are not supposed to use it.
\end{enumerate}

%include defunc.lhs
\subsection{Supporting function composition}

Imagine, in the setting of PLDI'14 extended with change composition, applying
one function change |df| to a composed argument change |da1 `ocompose` da2|,
where |f0 `oplus` df = f1|, |a0 `oplus` da1 = a1| and |a1 `oplus` da2 = a2|. We
want to compute incrementally the difference |db| between |f1 a2| and |f0 a0|.
The change |db1 = df a0 da1| goes from |f0 a0| to |f1 a1|. With a change |db2|
going from |f1 a1| to |f1 a2|, we can assemble the desired change as |db = db1
`ocompose` db2|.

However, to compute |db2| incrementally we cannot apply |df| to |da2|: |df a1
da2| gives the difference between |f0 a1| and |f1 a2|, but |db2| should be the
difference between |f1 a1| and |f1 a2|. Hence, we need to compute a nil change
for |f1|, that is, .

Doing that efficiently from the available elements is hard. However, with
defunctionalized changes this becomes much easier (assuming the function code
stays the same). Given the code of |f0| and |f1| we can produce a derivative for
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

\input{pldi14/sec-rw}
\chapter{Conclusions}
\pg{Plan for things that complete the original paper's story: add them by
  revising that text and in that chapter.}

\bibliography{Bibs/DB,Bibs/ProgLang,Bibs/SoftEng,Bibs/own}

\appendix
\chapter{More on our formalization}
\section{Mechanizing plugins modularly and limitations}
\label{sec:modularity-limits}
Next, we discuss our mechanization of language plugins in Agda, and its
limitations. For the concerned reader, we can say these limitations affect
essentially how modular our proofs are, and not their cogency.

In essence, it's not possible to express in Agda the correct interface for
language plugins, so some parts of language plugins can't be modularized as desirable.
Alternatively, we can mechanize any fixed language plugin together with
the main formalization, which is not truly modular, or mechanize a core
formulation parameterized on a language plugin, which that runs into a few
limitations, or encode plugins so they can be modularized and deal with encoding
overhead.

This section requires some Agda knowledge not provided here, but
we hope that readers familiar with both Haskell and Coq will be
able to follow along.

Our mechanization is divided into multiple Agda modules. Most
modules have definitions that depend on language plugins,
directly or indirectly. Those take definitions from language
plugins as \emph{module parameters}.

For instance, STLC object types are formalized through Agda type
|Type|, defined in module |Parametric.Syntax.Type|. The latter is
parameterized over |Base|, the type of base types.

For instance, |Base| can support a base type of integers, and a
base type of bags of elements of type |iota| (where |iota :
Base|). Simplifying a few details, our definition is equivalent
to the following Agda code:
\begin{code}
module Parametric.Syntax.Type (Base : Set) where
  data Type : Set where
    base  :  ^^(iota : Base)                   -> Type
    _=>_  :  ^^(sigma : Type)  -> (tau : Type) -> Type

-- Elsewhere, in plugin:

data Base : Set where
  baseInt  :  ^^Base
  baseBag  :  ^^(iota : Base) -> Base
-- ...
\end{code}

But with these definitions, we only have bags of elements of base type. If
|iota| is a base type, |base (baseBag iota)| is the type of bags with elements
of type |base iota|. Hence, we have bags of elements of base type. But we don't
have a way to encode |Bag tau| if |tau| is an arbitrary non-base type, such as
|base baseInt => base baseInt| (the encoding of object type |Int -> Int|).
%
Can we do better? If we ignore modularization, we can define types through the
following mutually recursive datatypes:

\begin{code}
mutual
  data Type : Set where
    base  :  ^^(iota : Base Type)              -> Type
    _=>_  :  ^^(sigma : Type)  -> (tau : Type) -> Type

  data Base : Set where
    baseInt  :  ^^Base
    baseBag  :  ^^(iota : Type) -> Base
\end{code}

So far so good, but these types have to be defined together. We
can go a step further by defining:

\begin{code}
mutual
  data Type : Set where
    base  :  ^^(iota : Base Type)              -> Type
    _=>_  :  ^^(sigma : Type)  -> (tau : Type) -> Type

  data Base (Type : Set) : Set where
    baseInt  :  ^^Base Type
    baseBag  :  ^^(iota : Type) -> Base Type
\end{code}

Here, |Base| takes the type of object types as a parameter, and
|Type| uses |Base Type| to tie the recursion. This definition
still works, but only as long as |Base| and |Type| are defined together.

If we try to separate the definitions of |Base| and |Type| into
different modules, we run into trouble.
\begin{code}
module Parametric.Syntax.Type (Base : Set -> Set) where
  data Type : Set where
    base  :  ^^(iota : Base Type)              -> Type
    _=>_  :  ^^(sigma : Type)  -> (tau : Type) -> Type

-- Elsewhere, in plugin:

data Base (Type : Set) : Set where
  baseInt  :  ^^Base Type
  baseBag  :  ^^(iota : Type) -> Base Type
\end{code}

Here, |Type| is defined for an arbitrary function on types |Base
: Set -> Set|. However, this definition is rejected by Agda's
\emph{positivity checker}. Like Coq, Agda forbids defining
datatypes that are not strictly positive, as they can introduce
inconsistencies.
\pg{Add the ``Bad'' example from Agda's wiki, with link for credit.}

The above definition of |Type| is \emph{not} strictly positive,
because we could pass to it as argument |Base = \tau -> (tau ->
tau)| so that |Base Type = Type -> Type|, making |Type| occur in
a negative position. However, the actual uses of |Base| we are
interested in are fine. The problem is that we cannot inform the
positivity checker that |Base| is supposed to be a strictly
positive type function, because Agda doesn't supply the needed
expressivity.

This problem is well-known. It could be solved if Agda function spaces supported
positivity annotations,\footnote{As discussed in
  \url{https://github.com/agda/agda/issues/570} and
  \url{https://github.com/agda/agda/issues/2411}.} or by encoding a universe of
strictly-positive type constructors. This encoding is not fully transparent and
adds hard-to-hide noise to
development~\citep{Schwaab2013modular}.\footnote{Using pattern synonyms and
  \texttt{DISPLAY} pragmas might successfully hide this noise.}
Few alternatives remain:
\begin{itemize}
\item We can forbid types from occurring in base types, as we did in our
  original paper~\citep{CaiEtAl2014ILC}. There we did not discuss at all a
  recursive definition of base types.
\item We can use the modular mechanization, disable positivity checking and risk
  introducing inconsistencies. We tried this successfully in a branch of that
  formalization. We believe we did not introduce inconsistencies in that branch
  but have no hard evidence.
\item We can simply combine the core formalization with a sample plugin. This is
  not truly modular because the core modularization can only be reused by
  copy-and-paste. Moreover, in dependently-typed languages the content of a
  definition can affect whether later definitions typecheck, so alternative
  plugins using the same interface might not typecheck.\footnote{Indeed, if
    |Base| were not strictly positive, the application |Type Base| would be
    ill-typed as it would fail positivity checking, even though |Base: Set ->
    Set| does not require |Base| to be strictly positive.}
\end{itemize}

Sadly, giving up on modularity altogether appears the more conventional choice.
Either way, as we claimed at the outset, these modularity concerns only limit
the modularity of the mechanized proofs, not their cogency.

\chapter*{Acknowledgments}
% From AOSD13
I thank Sebastian Erdweg for helpful discussions on
this project, Katharina Haselhorst for help
implementing the code generator, and the anonymous reviewers, Jacques Carette and Karl Klose
for their helpful comments on this chapter.
This work is supported in part by the European Research Council, grant \#203099 ``ScalPL''.

% From PLDI14 (?)
% From ILC17
We thank Cai Yufei, Tillmann Rendel, Lourdes Del Carmen Gonz\`alez Huesca, Yann
R\`egis-Gianas, Philipp Schuster, Sebastian Erdweg, Marc Lasson, Robert Atkey,
... for helpful discussions on this project.
