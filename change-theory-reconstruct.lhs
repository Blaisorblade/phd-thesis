% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

% From PLDI14 contribution.
\pg{In this chapter, we motivate more thoroughly our mathematical theory of \emph{changes}.}
In this chapter, we present and motivate a mathematical theory of \emph{changes} and
\emph{derivatives}.
This theory is more general than other work in the field because changes
are first-class entities and they are distinct from base values.
\pg{Add motivating application.}

This theory introduces change structures as an abstraction of operations
required on changes; while we introduce this abstraction as a mathematical one,
we anticipate using this abstraction also in code. \pg{Clarify this
  thought, too philosophical as phrased.}

We introduced the first version of this theory in a previous paper
\citep{CaiEtAl2014ILC}, but in this chapter we will elaborate more on its
motivation and design. Moreover, we will present later evolutions of this
definition, which were needed in further applications.

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
  A change structure over a set |V| is a tuple |chs(V) = (V, DV, `oplus`, `ominus`)|
  where
  \begin{subdefinition}
  \item |V| is the set of values;
  \item |DV| is the set of changes;
  \item |`oplus`| is a function of type |V -> DV -> V|;
  \item |`ominus`| is a function of type |V -> V -> DV|;
  \item all |v1, v2 `elem` V| satisfy |v1 `oplus` (v2 `ominus` v1) = v2|.
    \label{def:update-diff-bad-1}
  \item all |v `elem` V, dv `elem` DV| satisfy |(v `oplus` dv) `ominus` v = dv|.
    \label{def:diff-update-bad-1}
  \end{subdefinition}
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
v1|. To represent, for instance, |0 `ominus` 5| we still want to use |-5|.

As a first attempt, it seems we should keep using |Int| as set of changes |DV =
Int|. But with these definitions, updating a value |v `elem` V| with a change
|dv `elem` DV| might produce a result outside of |V|: for instance, updating
base value |v = 5| with change |dv = -6| would give updated base value |5
`oplus` (-6) = 5 + (-6) = -1|. However, the result |-1| is not a natural, hence
not a valid base value!

As a second attempt, to address this problem and produce a correct change
structure for naturals, we can try having |`oplus`| saturate on underflow, that
is, produce 0 instead of a negative number:
\begin{code}
  v `oplus` dv = if v + dv < 0 then 0 else v + dv
\end{code}
However, this definition violates \cref{def:diff-update-bad-1}, that is |(v
`oplus` dv) `ominus` v = dv|: if |v = 1| and |dv = -2|, then |(v `oplus` dv)
`ominus` v = -1 /= -2 = dv|.
\pg{However, this axiom is now dropped! To motivate against such definitions, we
  should argue about implementations of derivatives.}

In other words, it's not clear how to define an appropriate total function
|`oplus`: V -> DV -> V| for a change structure for naturals.
More in general, with this definition, we can update a value |v1| with changes
that cannot be of the form |v2 `ominus` v1| for any |v1|, and the update is
always supposed to produce a value |v2|, even for changes that are not \emph{valid}
for |v1|.
%
\pg{Refine reference}
Later chapters show that invalid changes are an especially serious problem for
changes on functions, but for now we refrain from discussing such examples in
more detail; we only point out that invalid changes have been a major problem
while developing the theory of ILC.
%
\pg{Have more examples why that's bad.} We could allow the update operation
|`oplus`| to fail, that is be a partial function.
%
However, partial operations would complicate algebraic
reasoning on change structures, so we choose a different solution.
% Further discussion of the issues.

\paragraph{A better definition: parameterizing change sets by base values}
Instead of making change operation |`oplus`| a partial function, we can alter
the definition of change structures and restrict the domain of |`oplus`|,
excluding inputs where it would fail, making it a total function. We propose
such an alternative definition. To ensure |v `oplus` dv| succeeds, we require
|dv| to be a valid change for |v|. Different |v| in |V| are associated to
different sets of valid changes; Hence, instead of having a single set of
changes |DV|, for each value |v `elem` V| we have a set of changes |Dt ^ v|.

\pg{Make sure that we've stated our metalanguage is type theory.}
\begin{definition}[Change structures, second version]
  \label{def:change-struct-bad-2}
  A change structure over a set |V| is a tuple |chs(V) = (V, Dt, `oplus`, `ominus`)|
  where
  \begin{subdefinition}
  \item |V| is the set of values;
  \item |Dt| is a family of sets of changes, indexed by |V|; that is, for each
    |v `elem` V|, |Dt ^ v| is a set, called the \emph{change set} of |v|;
  \item |`oplus`| is a function of type |(v : V) -> Dt ^ v -> V|;
  \item |`ominus`| is a function of type |V -> (v1 : V) -> Dt ^ v1|;
  \item all |v1, v2 `elem` V| satisfy |v1 `oplus` (v2 `ominus` v1) = v2|.
    \label{def:update-diff-bad-2}
  \item all |v `elem` V, dv `elem` Dt ^ v| satisfy |(v `oplus` dv) `ominus` v = dv|.
    \label{def:diff-update-bad-2}
  \end{subdefinition}
\end{definition}

This definition is flexible enough to allow defining a change structure for
naturals; we simply set |V = Nat, Dt ^ v = {dv `such` v + dv >= 0}, oplus =
(+), ominus = (-)|.

We could formalize an equivalent definition by having a single set |DV| and a
relation |R| between values |v `elem` V| and changes |dv `elem` DV| that are
\emph{valid} for |v|. From such a validity relation, we can define |Dt ^ v| as
|{dv `such` R(v, dv)}|. \pg{We elaborate on this later.}

\paragraph{Change structures as graphs}
\pg{What's the point? Does this belong here? Show it later when we add other
  operations, so we can say that changes form a category?}

Now that change sets are parameterized over base values, we can introduce a
different perspective on changes: we can regard a change structure |(V, Dt,
`oplus`, `ominus`)| as a graph, where the set of vertices coincides with the set
of values |V|, and a change |dv `elem` Dt ^ v| correspond to an edge from |v| to
|v `oplus` dv|.

%format Dt'
%format `oplus2` = `oplus` "_{2}"
%format `ominus2` = `ominus` "_{2}"

This requires change sets to be disjoint. However, given an arbitrary change
structure |(V, Dt, `oplus`, `ominus`)|, we can always construct another change
structure with disjoint change sets |(V, Dt', `oplus2`, `ominus2`)|, where |Dt'
v = (v, Dt ^ v)|, that is, where changes contain their base value. |v `oplus2` (v,
dv) = v `oplus` dv|, |v2 `ominus2` v1 = (v1, v2 `ominus` v1)|.

\pg{Add some drawing.}

Once change sets are disjoint, we can define a combined set of changes |DV| and
operations |src, dst : DV -> V| that map a change to its \emph{source} and its
\emph{destination}: If, using the original definition, we have that |dv `elem`
Dt v|, then |dv| is also part of the combined set of changes (|dv `elem` DV|),
and its source and destination are given by |src dv = v| and |dst dv = v `oplus`
dv|.

We can also define |`oplus`| in terms of |dst|, as |v `oplus` dv = dst dv|,
hence turning |`oplus`| into a derived operation and |dst| into a primitive one.

\subsection{From change equality to change equivalence}
Our new definition of change structures in \cref{def:change-struct-bad-2} is
still arguably too restrictive for some scenarios:
\cref{def:diff-update-bad-2} asks for |dv| to be equal to |(v `oplus` dv)
`ominus` v|; in general we might need to allow those two changes to simply be
equivalent in a suitable sense, as we next explain.

As a motivating example, we can consider defining a change structure for
sequences. We can define a change as a sequence of atomic changes, and each
atomic change can insert an element after a given position or remove the element
at a given position.

This defition is over-simplified, but will be sufficient for our example; we'll
later see a better version of this change structure, as defined by
\citet{Firsov2016purely}.

We can represent the set of all changes (ignoring the base value) as the
following Haskell datatype:

\begin{code}
data  AtomicSeqChange a
  =   Insert  Int a
  |   Delete  Int
type  SeqChange a = [AtomicSeqChange a]
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

Instead of requiring changes to be equal in \cref{def:diff-update-bad-2}, we
require then changes to be simply equivalent; we define two changes to be
equivalent if they have the same source and the same destination. In other
words, if we have two changes |dv1, dv2|, valid for |v|, that is |dv1, dv2: Dt
v|, then they are equivalent |dv1 `doe` dv2| if and only if |v `oplus` dv1 = v
`oplus` dv2|.

Maybe surprisingly, if we replace change equality with change equivalence in
\cref{def:diff-update-bad-2}, we get a corollary of the rest of the definition!

Indeed, \cref{def:diff-update-bad-2} becomes |(v `oplus` dv) `ominus` v `doe`
dv|, which we can prove as follows.
\begin{lemma}
  \label{def:diff-update-lemma-bad-2}
  Given a change structure |chs(V) = (V, Dt, `oplus`, `ominus`)| satisfying definition
  \cref{def:change-struct-bad-2}, but not necessarily
  \cref{def:diff-update-bad-2}, we can prove for any base value |v `elem` V| and
  for any change |dv| cvalid for |v| (that is, |dv `elem` Dt v|) that |(v
  `oplus` dv) `ominus` v `doe` dv|.
\end{lemma}
\begin{proof}
Since both sides are changes for |v|, the thesis is equivalent to |v `oplus` ((v
`oplus` dv) `ominus` v) = v `oplus` dv|.

To prove our thesis, we remember that thanks to \cref{def:update-diff-bad-2},
for any |v1, v2 : V| we have |v1 `oplus` (v2 `ominus` v1) = v2|. We can take |v1
= v|, |v2 = v `oplus` dv| and obtain |v `oplus` ((v `oplus` dv) `ominus` v) = v
`oplus` dv|, which is exactly our thesis.
\end{proof}

Therefore we can drop \cref{def:diff-update-bad-2} from the definition, obtaining the following definitions and lemma:
\begin{definition}[Change structures]
  % -intro distinguishes this label from the one in the copy of the paper.
  \label{def:change-struct-intro}
  A change structure over a set |V| is a tuple |chs(V) = (V, Dt, `oplus`, `ominus`)|
  where
  \begin{subdefinition}
  \item |V| is the set of values;
  \item |Dt| is a family of sets of changes, indexed by |V|; that is, for each
    |v `elem` V|, |Dt v| is a set, called the \emph{change set} of |v|;
  \item |`oplus`| is a function of type |(v : V) -> Dt v -> V|;
  \item |`ominus`| is a function of type |V -> (v1 : V) -> Dt v1|;
  \item all |v1, v2 `elem` V| satisfy |v1 `oplus` (v2 `ominus` v1) = v2|.
    \label{def:update-diff-intro}
  \end{subdefinition}
\end{definition}

\begin{definition}[Change equivalence]
  Given a change structure $\ChangeStruct{V}$, a value $v \in V$, and two
  changes $\D v_1, \D v_2 \in \Change{v}$, we say that $\D v_1$ is
  \emph{change-equivalent} (or simply equivalent, when there is no ambiguity) to
  $\D v_2$, and we write $\D v_1 \Doe \D v_2$ if and only if
  $\Update{v}{\D v_1} = \Update{v}{\D v_2}$.
\end{definition}

\begin{lemma}
  \label{def:diff-update-lemma-intro}
  Given a change structure |chs(V) = (V, Dt, `oplus`, `ominus`)| satisfying definition
  \cref{def:change-struct-intro}, we can prove for any base value |v `elem` V| and
  for any change |dv| cvalid for |v| (that is, |dv `elem` Dt v|) that |(v
  `oplus` dv) `ominus` v `doe` dv|.
\end{lemma}
\begin{proof}
  The same as in \cref{def:diff-update-lemma-bad-2}.
\end{proof}

Change equivalence is very well-behaved, as shown in the following lemmas.

\begin{lemma}[Change equivalence is indeed an equivalence relation]
  For any $x \in X$ with a change structure on $X$, change equivalence is an
  equivalence relation (reflexive, symmetric, transitive) among
  elements of $\Change{x}$.
\end{lemma}

Moreover, all operations that our theory defines respect change equivalence.
\pg{Introduce derivatives}
% Once we introduce further definitions

\pg{Introduce needed notation}
\begin{lemma}[Identities using change equivalence]
  Using change equivalence we can state additional algebraic equivalences,
  that complement \cref{def:update-diff}.

\begin{align*}
\Update v \D{v} = x &\Leftrightarrow \D{v} \Doe \NilC{v}\\
\Diff v v &\Doe \NilC {v}\\
\end{align*}
\end{lemma}

\pg{We can't yet really say programs at this point!}
% That is, in all simple contexts that we can construct, two
% equivalent changes will behave indistinguishably. In fact, for programs that
% only use changes as changes (without looking at their
% implementation details), we conjecture that equivalent changes are
% observationally equivalent. However, making this conjecture
% precise and proving it are efforts left for future work.

\pg{Introduce derivatives before!}

\section{Evolving change structures}
In this section we describe variants of the basic definition of change structures.

\subsection{Relaxing the definition: removing |`ominus`|}
\pg{Maybe move to a subsequent chapter?}
It is often useful to consider variants of the original definition with fewer
operations.

\subsection{Example: monoid changes}
If we stop requiring |odiff|, then suddenly we can build the construction of
change structures out of groups to build change structures out of monoids.

\pg{Resume!}
