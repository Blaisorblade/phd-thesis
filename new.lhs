\documentclass{book}

\usepackage{natbib}
\usepackage{comment}
\bibliographystyle{abbrvnat}
\input{packages}
\input{macros}
\usepackage{amsthm}

%include polycode.fmt
%include forall.fmt
\begin{document}

%%%
%%% XXX Integrate properly in rest of document. Will be possible.
%%%
\chapter{Incrementalizing more programs}
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

\chapter{Defunctionalizing function changes}

If we represent function changes as functions, we can only apply them. This and
other problems are vastly simplified if we instead defunctionalize function
changes. Furthermore, assembling changes for functions becomes easier if the
functions are defunctionalized as well.

In this chapter, we show how to systematically incrementalize such
defunctionalized programs by systematic program transformation.

\subsection{Avoiding the closed-world assumption}
\pg{Move this somewhere better.}

\pg{cite Uroboro.}

Defunctionalization as usually defined can only be performed on a closed
program. Using open algebraic datatypes can lift this restriction, though
usually at the cost of exhaustiveness checking.

Representing changes as data instead of functions is not a goal per se. Rather,
our goal is defining other primitive operations on function changes beyond
application, and that is not possible if function changes are represented as
functions. However, this problem could also be solved by representing function
changes as more general \emph{codata} using copatterns. Codata generalize
functions; while functions can only be \emph{observed} by applying them to an
argument, codata can support further observations. Moreover, when defining
codata using copatterns, the codata definition fixes a set of observations,
while new generators can be defined in the entire program, similarly to how
functions can be defined in a whole programs.

Hence we could potentially represent changes as codata. We leave this for future
work.

\section{Setup}
\pg{Clarify how we use Haskell} We encode ILC by manually writing Haskell code,
containing both manually-written plugin code and systematically transformed code
that could be generated. At first we do not
implement or formalize all the transformation steps.

Even though we do not support higher-order programs directly, we still reuse or
adapt many of the ideas from ILC. \pg{Check this} And as we will see, we treat
defunctionalized functions specially.

In this chapter we will support polymorphism but avoid tackling first-class
polymorphism.
\pg{add pointer.}

Let's rememeber our basic interface to change structures:
\begin{code}
class ChangeStruct t where
  type Dt t = r | r -> t
  oplus :: t -> Dt t -> t
  -- Absorption law:
  -- x `oplus` oreplace y = y
  oreplace :: t -> Dt t

class ChangeStruct t => OnilChangeStruct t where
  -- Proxy is used to encode explicit type application.
  onil :: Proxy t -> Dt t

class ChangeStruct t => NilChangeStruct t where
  nil :: t -> Dt t
\end{code}

Crucially, changes to type |t| are represented as type |Dt t|, and this
interface does \emph{not} require that change structures support a difference
operation, or that all changes are representable.

\section{Defunctionalization}
We defunctionalize functions from |A| to |B| as pairs of a function descriptor
and a (possibly empty) environment. The function descriptor is represented using
a GADT of codes indexed by |A|, |B| and environment type. We separate the
environment because a variety of operations must manipulate it uniformly.

\pg{Add example snippets}
\begin{code}
data Code env a b where
  CPair1 :: Code a b (a, b)
  CMapPair1 :: Code [b] a [(a, b)]

data Fun1 a b = forall env . P env (Code env a b)

applyFun1 :: (Fun1 a b) -> a -> b
applyFun1 = undefined
\end{code}

ILC requires support for function changes because the environment can change.
Hence we start by representing function changes through environment changes.

\begin{code}
data DFun1 a b = forall env . DP (Dt env) (Code env a b)
\end{code}

In fact, we can also replace a function value by another one with different
code. However, for now we set aside support for this case; as we will see, for
that case we can simply support replacing a function value with a new code and
associated environment, that is, simply support a replacement change.

Next, we add support for derivatives and function changes. We can start by
simply adding a derivative for |applyFun1|:
\begin{code}
applyDFun1 :: (Fun1 a b) -> (DFun1 a b) -> a -> Dt a -> Dt b
applyDFun1 = undefined
\end{code}

However, we can also implement further accessors that inspect function changes. We can now finally detect if a change is nil:
\begin{code}
isNil :: DFun1 a b -> Boolean
\end{code}

We can then wrap a derivative to return a nil change immediately if at runtime
all input changes turn out to be nil. This was not possible in PLDI'14, because
nil function changes could not be detected at runtime, only at compile time.

\subsection{Supporting function composition}

%format f0
%format f1
%format a0
%format a1
%format a2
%format da0
%format da1
%format da2

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
% derPreDFun1 :: (ChangeStruct a, NilChangeStruct env) => Code env a b -> env -> Dt env -> a -> Dt a -> Dt b
% derPostDFun1 :: (ChangeStruct a, NilChangeStruct env) => Code env a b -> env -> Dt env -> a -> Dt a -> Dt b
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
  Code env a b -> env -> DCode env a b -> Dt env -> a -> Dt a -> Dt b
derApplyDFun1 (P Add1 _()) (DP (Replace Add2) ()) = +1 -- As a change
...
derApplyDFun1 (P _f _env) (DP (Replace newF) newEnv) = oreplace (newF newEnv)
\end{code}

This is enabled by defunctionalizing both base functions and changes.
\end{document}
