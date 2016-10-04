\documentclass{book}

\usepackage{natbib}
\usepackage{comment}
\bibliographystyle{abbrvnat}
\input{packages}
\input{macros}
\usepackage{amsthm}
\usepackage{cleveref}

\theoremstyle{definition}
% http://tex.stackexchange.com/a/67251
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{definition}[theorem]{Definition}

%include polycode.fmt
%include forall.fmt

%format Nat = "\mathbb{N}"
%format Int = "\mathbb{Z}"
%format v1
%format v2

%format `oplus` = "\oplus "
%format `ominus` = "\ominus "
%format oplus = "(\oplus)"
%format ominus = "(\ominus)"

%format `such` = "\mid"
%format ^ = " "
%format f0
%format f1
%format a0
%format a1
%format a2
%format da0
%format da1
%format da2

%format x0
%format x1
%format x2
%format x3

%format dx0
%format dx1
%format dx2
%format dx3

%format Dt = "\Delta"
%format DV = "\Delta V"
\begin{document}

\chapter{A theory of changes}

% From PLDI14 contribution.
In this chapter, we present a novel mathematical theory of changes and
derivatives, which is more general than other work in the field because changes
are first-class entities and they are distinct from base values.

\paragraph{Conventions}
Unless specified otherwise, our chapter is not concerned with the syntax of an
object language, but with simple sets of values.
%
In fact, while our discussion will be informal, our formalization of this
chapter is done using a type-theoretic metalanguage.
%
Later we will use such sets for a type-theoretic semantics of a typed,
total language, hence we in this chapter we will not account for non-termination
through domain theory or other means.
%
When defining functions we will use uniformly Haskell-style notation even for
situations where it is unusual.

\section{Generalizing the calculus of finite differences}
%format f_d = "\Delta f"
%format `dot` = "\cdot"
% Revise terminology.
Our theory generalizes the calculus of finite difference. If |f| is a real
function, one can define its \emph{finite difference}, that is a function |f_d|
such that |f_d a da = f (a + da) - f a|. The calculus of finite differences
shows defines theorems that in many cases allow computing a closed formula for
|f_d| given a closed formula for |f|. For instance, if |f x = 2 `dot` x|, one
can verify its finite difference is |f_d x dx = 2 `dot` (x + dx) - 2 `dot` x = 2
`dot` dx|.

However, this calculus is usually defined for real functions, and it is not
immediate how to generalize it beyond groups. On the other hand, many useful
types do not form a group: for instance, lists of integers don't form a group
but only a monoid. Moreover, it's hard to represent list changes simply through
a list: how do we specify which elements were inserted (and where), which were
removed and which were subjected to change themselves?

Hence, we define a more general algebraic structure, where the set of values and the set
of changes are allowed to be distinct.

\section{Change structures}

\paragraph{A first definition attempt}
To generalize the definition of a finite difference |f_d a da = f (a + da) - f
a|, we need at least two operations:
\begin{itemize}
\item one to \emph{update} a value |a| with a change |da|, which we write |a
  `oplus` da|,
\item and one to construct a change representing the \emph{difference} between
  two values |a| and |b|, which we write |b `ominus` a|.
\end{itemize}

As already discussed, we'll need to allow (in general)
distinct sets of values and changes. Hence we give the following definition.
\begin{definition}[Change structures, first version]
  \label{def:change-struct-bad-1}
  A change structure over a set |V| is a tuple |(V, DV, `oplus`, `ominus`)|
  where
  \begin{enumerate}
  \item |V| is the set of values;
  \item |DV| is the set of changes;
  \item |`oplus`| is a function of type |V -> DV -> V|;
  \item |`ominus`| is a function of type |V -> V -> V|;
  \item all |v1, v2 `elem` V| satisfy |v1 `oplus` (v2 `ominus` v1) = v2|.
    \label{def:update-diff-bad-1}
  \item all |v `elem` V, dv `elem` DV| satisfy |(v `oplus` dv) `ominus` v = dv|.
    \label{def:diff-update-bad-1}
  \end{enumerate}
\end{definition}

Each group induces a change structure where values and changes are represented
by group elements, update can be implemented by addition |+|, and difference is
implemented by subtraction |-|, that is, by |b - a = b + (- a)|, where |-|
represents the group inverse operation. Since integers form a group under
addition, we can define a change structure on integers where |V = DV = Int|,
|oplus = (+)| and |ominus = (-)|. % Add bags?

\paragraph{Trying to define a change structure for naturals}
However, \cref{def:change-struct-bad-1} is not general enough for our goals. In
many examples, we need to associate different sets of changes to each base value
|v `elem` V|. For instance, let us try to turn our change structure for integers
into a change structure for naturals, that is having |Nat| as set of base values
(|V = Nat|). We still have |v `oplus` dv = v + dv| and |v2 `ominus` v1 = v2 -
v1| To represent, for instance, |0 `ominus` 5| we still want to use |-5|, so it
seems we should keep using |Int| as set of changes |DV = Int|. But with these
definitions, updating a value |v `elem` V| with a change |dv `elem` DV| might
produce a result outside of |V|: for instance, with |v = 5, dv = -6|, we have |5
`oplus` (-6) = 5 + (-6) = -1|.

To produce a correct change structure for naturals, addressing this problem, we
can have |`oplus`| saturate on underflow, that is, produce 0 instead of a
negative number:
\begin{code}
  v `oplus` dv = if v + dv < 0 then 0 else v + dv
\end{code}
However, this definition violates \cref{def:diff-update-bad-1}, that is |(v
`oplus` dv) `ominus` v = dv|: if |v = 1| and |dv = -2|, then |(v `oplus` dv)
`ominus` v = -1 /= -2 = dv|.

In other words, it's not clear how to define an appropriate total function
|`oplus`: V -> DV -> V| for a change structure for naturals.

More in general, with this definition, we can update a value |v1| with changes
that cannot be of the form |v2 `ominus` v1| for any |v1|, and the update is
always supposed to produce a value |v2|, even for changes that are not \emph{valid}
for |v1|.
\pg{Refine reference}
%
Later chapters show that invalid changes are an especially serious problem for
changes on functions, but for now we refrain from discussing such examples in
more detail; we only point out that invalid changes have been a major problem
while developing the theory of ILC.
%
\pg{Have more examples why that's bad.} We could allow the update operation to
be partial.
%
However, partial operations would complicate algebraic
reasoning on change structures, so we choose a different solution.
% Further discussion of the issues.

\paragraph{An alternative definition}
To ensure we can make |`oplus`| and |`ominus`| total, we propose an alternative
definition, where we have not one but multiple sets of changes, one for each
base value.

\pg{Make sure that we've stated our metalanguage is type theory.}
\begin{definition}[Change structures, second version]
  \label{def:change-struct-bad-2}
  \pg{Use subdefinition to allow citations, here and before.}
  A change structure over a set |V| is a tuple |(V, Dt, `oplus`, `ominus`)|
  where
  \begin{enumerate}
  \item |V| is the set of values;
  \item |Dt| is a family of sets of changes, indexed by |V|; that is, for each
    |v `elem` V|, |Dt v| is a set, called the \emph{change set} of |v|;
  \item |`oplus`| is a function of type |(v : V) -> Dt v -> V|;
  \item |`ominus`| is a function of type |V -> (v1 : V) -> Dt v1|;
  \item all |v1, v2 `elem` V| satisfy |v1 `oplus` (v2 `ominus` v1) = v2|.
    \label{def:update-diff-bad-2}
  \item all |v `elem` V, dv `elem` Dt v| satisfy |(v `oplus` dv) `ominus` v = dv|.
    \label{def:diff-update-bad-2}
  \end{enumerate}
\end{definition}

This definition is flexible enough to allow defining a change structure for
integers; we simply set |V = Nat, Dt v = {dv `such` v + dv >= 0}, oplus =
(+), ominus = (-)|.

We could formalize an equivalent definition by having a single set |DV| and a
relation |R| between values |v `elem` V| and changes |dv `elem` DV| that are
\emph{valid} for `v`. From such a validity relation, we can define |Dt v| as |{dv `such` R(v, dv)}|.

\pg{Discuss the source and destination of a change here?}
\paragraph{Change equality}
Our new definition of change strucctures in \cref{def:change-struct-bad-2} is
still arguably too restrictive for some scenarios. The problem is that
\cref{def:diff-update-bad-2} asks for |dv| to be equal to |(v `oplus` dv)
`ominus` v|; in general we might need to allow those two changes to simply be
equivalent in a suitable sense, as we next explain.

As a motivating example, we can consider defining a change structure for
sequences. We can define a change as a sequence of atomic changes, and each
atomic change can insert an element after a given position or remove the element
at a given position.

This defition is over-simplified, but will be sufficient
for our example; we'll later see a better version of this change structure, as defined by

We can represent the set of all changes (ignoring the base value) as the
following Haskell datatype:

\begin{code}
data AtomicSeqChange a
  = Insert Int a
  | Delete Int
type SeqChange a = [AtomicSeqChange a]
\end{code}

Note that even though we use Haskell syntax, we ignore nontermination, so we
interpret the above definition as true strict algebraic datatypes, as we'd do in
a strict language, instead of allowing nonterminating values as one usually does
in a lazy language like Haskell. And we use this syntax to refer to values in
the semantics of |SeqChange a|.

We can then say that a change |dv| is valid for a base sequence |v| if applying
the atomic changes that |dv| contains never refers to an out-of-bounds index. As
explained, we can then define |Dt v| as the set of changes that are valid with
respect to |v|. We can then define a function for change application
implementing the algorithm discussed.
\pg{Write down |`oplus`|}

While we have not specified an implementation of |`ominus`|, we can see that in
many cases several return values are equally valid because several changes have
the same effect. For instance, if |v = [1, 2, 3]| both |dv1 = [Delete 0, Insert
0 1]| and |dv2 = []| are changes from |v| to |v|, that is, both satisfy |v
`oplus` dv = v|. So which should be the return value of |v `ominus` v|? Applying
\cref{def:diff-update-bad-2} gives us |dv1 = (v `oplus` dv1) `ominus` v = v
`ominus` v = (v `oplus` dv2) `ominus` v = dv2|, hence |dv1 = dv2| which is
absurd.

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
\bibliography{Bibs/DB,Bibs/ProgLang,Bibs/SoftEng,Bibs/own}
\end{document}
