% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{A theory of changes}
%\section{Changes as First-Class Values}
%\section{Formalizing changes}
\label{sec:1st-order-changes}

\Cref{eq:correctness} talked informally about changes. In this
chapter we formalize this notion. Since different types call for
different changes, we specify the interface common to all
changes. We call any implementation of this interface a
\emph{change structure}. In this chapter we first define change
structures formally, then construct change structures for
functions between change structures, and finally show that
derivatives are a special case of function changes.

The first presentation of the theory of changes was published by
\citet{CaiEtAl2014ILC}. This work was a true team effort; I
started and oversaw the project, contributed the notion of change
structure and change equivalence; Yufei Cai contributed the
program transformation and came up with its first correctness
proofs. This chapter is a significantly extended and revised
version of Sec. 2 of that paper.%
\footnote{While our proof was already fully formalized at
  publication time, at the time the notion of change equivalence
  did not appear in the paper and we tried to only use equality
  of base values instead. In the camera-ready version, Lemma 2.5
  was an incorrect variant of \cref{thm:deriv-nil}, because it
  used equality rather than change equivalence.}

% \section{Development history}
% The first presentation of the theory of changes was published by
% \citet{CaiEtAl2014ILC}. This work was a true team effort; I
% started and oversaw the project, contributed the notion of change
% structure and change equivalence; Yufei Cai contributed the
% program transformation and came up with its first correctness
% proofs.\pg{This is compatible with Cai's summary, but to
%   improve.}
% %
% This chapter is a significantly extended and revised version of
% Sec. 2 of that paper. We also fix a small technical mistake:
% While our proof was already fully formalized at publication time,
% at the time the notion of change equivalence did not appear in
% the paper and we tried to only use equality of base values
% instead. In the camera-ready version, Lemma 2.5 was an incorrect
% variant of \cref{thm:deriv-nil}, because it used equality rather
% than change equivalence.


% In this section, we will not consider programs, but simply
% mathematical functions. In \cref{sec:differentiate} we will apply
% this theory to functions representing the meaning of programs,
% but we prefer to develop our theory

\section{Change structures}\label{ssec:change-structures}
Consider a set of values, for instance the set of natural numbers
|Nat|. A change |dv| for a base value |v `elem` Nat| should
describe the difference between |v| (the old value, hence also
|old(v)|) and another natural |new(v) `elem` Nat|.
We do not define changes directly, but we
specify operations which must be defined on them. They are:
\begin{itemize}
\item We can \emph{update} a base value |v1| with a
  change |dv| to obtain an updated or \emph{new} value
  |v2|. We write |v2 = v1 `oplus` dv| (or sometimes |new(v) = old(v) `oplus` dv|).
\item We can obtain a change between two arbitrary
  values |v1| and |v2| of the set we are considering.
  We write |dv = v2  `ominus` v1|.
\end{itemize}

To ensure that |`oplus`| and |`ominus`| are
always defined, we need to define their domains carefully.
%
Consider for instance natural numbers: for them it makes sense to
describe changes using standard subtraction and addition.
%
That is, for naturals we can define
|v1 `oplus` dv = v1 + dv| and |v2 `ominus` v1 = v2 - v1|.
But as set of changes we cannot pick |Nat|: it is too small, because subtraction does not always
produce a natural. We also cannot pick the set of integers |Int|: it is instead
too big, since adding a natural and an integer does not always
produce a natural. In fact, we cannot use the same set of all
changes for all naturals. Hence we must adjust the requirements:
for each base value |v1| we introduce a set |Dt ^ v1| of
changes for |v1|, and require |v2 `ominus` v1| to produce
values in |Dt ^ v1|, and |v1 `oplus` dv| to be defined
for any |dv| in |Dt ^ v1|. For natural |v1|, we set $|Dt ^ v1| =
\left\{|dv| \mid |v1 + dv >= 0| \right\}$; |`ominus`| and |`oplus`| are
then always defined.

\begin{oldSec}

\ldots, we could use \emph{functional
changes}, that is by defining changes to be functions from the
old value to the new value:
\begin{align*}
\Change{\Gt} & = \Gt \r \Gt, \\
\Apply{\D v}{\Old{v}} & = \App{\D v}{\Old{v}},\\
\Diff{\New{v}}{\Old{v}} & = \Lam{x}{\New{v}}.
\end{align*}
However,
this definition does not allow derivatives to analyze changes to
be more efficient than recomputation. To understand why, let us
consider the following example.

Let $\Old{v} = \{1, 2, \ldots, n\}$ be a bag (or multiset) of
integers, let $f$ be a function from bags to integers summing the
elements of its argument, and let $\Old{s} = \App{f}{\Old{v}}$.

Later during program execution, assume we add $n + 1$ to
$\Old{v}$ and need to update $\Old{s}$. Hence,
 $\New{v} = \{1, 2, \ldots, n, n + 1\}$, $\D v$ represent the change of $v$,
and we need to compute the result of $\New{s} = \App{f}{\New{v}}$.
%
Thanks to \cref{eq:correctness}, we can guarantee that
$\New{s} = \Apply{\App{\App{\Derive{f}}{\Old{v}}}{\D
    v}}{\Old{v}}$.

Now, if $\Derive{f}$ would know that $\D v$ only added $n + 1$ to
the bag, it could produce in $O(1)$ a change $\D s$ such that
$\Apply{\D s}{s} = n + 1 + s$. But if $\D v$ is simply a function
such that $\App{\D v}{\Old{v}} = \New{v}$, we have no way of
inspecting its intension, since in $\lambda$-calculus functions
are opaque. Instead, the difference between two bags can be
described as another bag, and $\APPLY$ for bags can be defined as
bag merge.%
\footnote{Negative multiplicities are required to represent
  removals, as we discuss in Sec.~\ref{sec:plugins}.} Similarly,
we can describe the difference between two numbers $x$ and $y$ as
their arithmetical difference $x-y$. In this case, the change
application operator $\APPLY$ would be the normal addition
operator $+$. With these definitions, thanks to the structure of
$+$, $\App{\App{\Derive{f}}{\Old{v}}}{\D v}$ can produce its
result without even using $\Old{v}$, in time $O(||\D v||)$ (we
explain later how to compute $\Derive{f}$ automatically).

For now, we simply note that we cannot fix $\Change{\Gt} = \Gt \r
\Gt$. We need a more flexible encoding of changes, which allows
inspecting their structure; moreover, this structure needs to
allow writing efficient derivatives, in particular efficient
derivatives for the primitives acting on $\Gt$.

Hence, to make our general framework
independent of such domain- and application-specific
considerations, we simply require language plugins to define not
only base types and primitives for them, but also $\Change{\tau}$
whenever $\tau$ is a base type, and operators $\APPLY_\tau$ and
$\DIFF_\tau$.
Using $\APPLY$, we can recover a function $\Gt\r\Gt$
from any $\D x$ of type $\Change{\Gt}$; it is $\Lam*x{\Apply{\D
x}{x}}$.
\end{oldSec}

\pg{We never say why we use ``structure''. On second thought,
  this might be OK since we have little space.}
The following definition sums up the discussion so far:

\begin{definition}[Change structures]
  \label{def:change-struct}
  A tuple $\chs V = |(V, Dt, `oplus`, `ominus`)|$
  is a \emph{change structure} (for |V|) if:

  \begin{subdefinition}
  \item |V| is a set, called the \emph{base set}.
    \label{def:base-set}
  \item |Dt ^ v| is a set, called the \emph{change set}, for any |v `elem` V|.
    \label{def:change-set}
  \item Value |v `oplus` dv| belongs to V for any |v `elem` V| and |dv `elem` Dt
    ^ v|. We also call |v| the \emph{base value} of the change, or its
    \emph{source}; we call |v `oplus` dv| the \emph{updated value} of the
    change, or its \emph{destination}/\emph{target}.
    \label{def:update}
  \item |`ominus`| produces changes: We have |u `ominus` v `elem` Dt ^ v| for any base values |u, v `elem` V|.
    \label{def:diff}
  \item Change cancellation holds, that is, updating with a difference gives the difference's target: We have |v `oplus` (u `ominus` v) = u| for any |u, v `elem` V|.
    \qed
    \label{def:update-diff}
  \end{subdefinition}
\end{definition}

\paragraph{Notation}
We overload operators |Dt|, |`oplus`| and |`ominus`| to refer
to the corresponding operations of different change structures;
we will subscript these symbols when needed to prevent ambiguity.
For any $\chs V$, we write |V| for its first component,
as above. We make |`oplus`| left-associative, that is,
|v `oplus` dv1 `oplus` dv2| means |(v `oplus` dv1) `oplus` dv2|.
We assign precedence to function application over
|`oplus`| and |`ominus`|, that is,
|f a `oplus` g a da| means
|(f a) `oplus` (g a da)|.

\paragraph{Changes as graph edges}
We'll also treat a change between a source and destination as an
edge between them, and use graph terminology to discuss changes.
Indeed, a change structure induces a graph with base values as
vertices and all changes as edges.

\paragraph{Change structures using dependent types}
Using dependent types, as in our mechanized proof, some points of
the definition become simpler to state. In particular, we can now
write type signatures for |`oplus`| and |`ominus`|, namely
\begin{code}
`oplus`   : ^^ (v : V)   ->  Dt ^ v    ->  V
`ominus`  : ^^ (v2 : V)  ->  (v1 : V)  -> Dt ^ v1
\end{code}

\subsection{Nil changes}
A change can have equal source and target, in which case we call
it a \emph{nil change}.
\pg{Rewrite}
\begin{definition}[Nil change]
  \label{def:nil-change-v2}
  A nil change for a value |v| is a change |dv| such that |v `oplus` dv = v|,
  for any change structure $\chs V$ and value |v `elem` V|.
\end{definition}

We use |`ominus`| to associate, to each value, a distinguished nil change.
\begin{lemma}[Behavior of $\NILC$]
  \label{thm:update-nil-v2}
  Change |v `ominus` v| is a nil change for |v| (that we write |nil(v)|), for any
  change structure $\chs V$ and value |v `elem` V|:
  \[
    |nil(v) = v `ominus` v| \qed
  \]
\end{lemma}
\begin{optionalproof}
  By the definition of nil changes (\cref{def:nil-change-v2}) we need to show
  that |v `oplus` (v `ominus` v) = v|, which follows from
  \cref{def:update-diff}.
\end{optionalproof}

\begin{examples}
We demonstrate a change structure on \emph{bags with signed
multiplicities}~\citep{Koch10IQE}.
These are
unordered collections where each element can appear an integer
number of times. 
\begin{enumerate}[(a)]
\item
Let $S$ be any set.
The base set $V=\Bag S$ is the set of bags of elements of $S$ with signed
multiplicities. The bag $\Set{1,1,\bar2}$ contains two positive
occurrences of $1$ and a negative occurrence of $2$.

\item For each bag $v\in V$, set the change set $\Change v = V$.
Every bag can be a change to any other bag. The bag
$\Set{1,1,\bar5}$ represents two insertions of $1$ and one
deletion of $5$.

\item The update operator is bag merge: $\UPDATE=\MERGE$. The
merge of two bags is the element-wise sum of multiplicities:
\[
\Merge{\Set{\bar1,2}}{\Set{1,1,\bar5}}=\Set{1,2,\bar5}.
\]

\item Let $\NEGATE$ be the negation of multiplicities:
\[
\Negate{\Set{1,1,\bar5}}=\Set{\bar1,\bar1,5}.
\]
To compute the
difference of two bags, compute the merge with a negated bag:
\[
\Diff{u}{v}=\Merge{u}{\Negate*{v}}.
\]

\item Given the above definition of $\UPDATE$ and $\DIFF$, it is
not hard to show that $\Apply{\Diff*{u}{v}}{v}$ for all bags
$u,v\in V$.
\end{enumerate}
The change structure we just described is written succinctly
\begin{alignat*}3
\ChangeStruct{\Bag S} = (
&\Bag S,
&&\Lam*{v} {\Bag S},
\\
&\MERGE,
&&\Lam*{x\; y}{\Merge{x}{\Negate*{y}}}).
\end{alignat*}

This change structure is an instance of a general construction:
we can build a change structure from an arbitrary \emph{abelian group}.
An abelian group is a tuple $(G, \boxplus,
\boxminus, e)$, where $\boxplus$ is a commutative
and associative binary operation, $e$ is its identity
element, and $\boxminus$ produces inverses of elements $g$
of $G$, such that $(\boxminus g) \boxplus g = g \boxplus
(\boxminus g) = e$. For instance, integers,
unlike naturals, form the abelian group $(\mathbb{Z}, +, -, 0)$
(where $-$ represents the unary minus). Each abelian group
$(G, \boxplus, \boxminus, e)$ induces a change structure,
namely $\left(G, \Lam{g}{G}, \boxplus, \Lam{g\; h}{g
    \boxplus (\boxminus h)}\right)$, where the change set
for any $g \in G$ is the whole $G$. Change structures
are more general, though, as the example with natural numbers illustrates.
%
If $\Empty$ represents the empty bag, then $(\Bag{S}, \MERGE,
\NEGATE, \Empty)$ is an abelian group, which induces the
change structure we have just seen.

The abelian group on integers induces also a change structure on
integers, namely $\ChangeStruct{\mathbb{Z}} = (\mathbb{Z},
\Lam*{v} {\mathbb{Z}}, +, -)$.

% Separate examples more.
We can also define change structures on sequences; here we show a simple one,
while more efficient variants appear later.

Using Haskell-like notation, we can define changes through a datatype. A change
for a sequence |s| is a sequence of single changes for |s|; each single change
either represents the insertion of a new element at some position in |s|, or the
removal of an element of |s| (identified by its position). We can represent a
datatype of changes for unspecified sequences, ignoring the requirement of
changes to be valid:%
\footnote{We use Haskell notation even though we're discussing mathematical
  entities, not programs.}

\begin{code}
data SeqSingleChange a
  =  Insert  { idx :: Int , el :: a }
  |  Remove  { idx :: Int }
data SeqChange a = Seq (SeqSingleChange a)
\end{code}
\pg{Continue/revise}
\pg{Make sure this does not overlap with other presentation of this change structure.}
%
% In Agda we can also represent changes to a specified sequence.
% I started defining this, and it's of course not immediate.
% \begin{code}
% data VecSingleChange {a : Set} {n} (v : Vec a n) : Set where
%   Insert : (idx : Fin (suc n)) -> (el : a) -> VecSingleChange v
%   Remove : (idx : Fin n) -> VecSingleChange v
%
% VecChange : forall {a : Set} {n} -> (v : Vec a n) -> Set
% VecChange v = List (VecSingleChange v)
%
% data SeqSingleChange {a : Set} (s : Vect n a) : Set where
%   Insert : (idx : Fin (suc n)) -> (el : a) -> SeqSingleChange s
%   Remove : (idx : Fin n) -> SeqSingleChange s
% SeqChange : forall {a : Set} {n} -> (s : Vect n a)
% SeqChange s = Seq (SeqSingleChange s)
% \end{code}
%
\end{examples}

\section{Change equivalence}
\label{sec:changeeeq}
Next, we formalize when two changes are ``equivalent'', and show
that any change |dv| is equivalent to the difference
|(v `oplus` dv) `ominus` dv|, even though the definition of
change structure has no such explicit requirement.

We could demand that
|(v `oplus` dv) `ominus` dv| be equal to |dv|. On naturals and
on bags, this would be true. But there are sensible examples of
change structures where |dv| and |(v `oplus` dv) `ominus` dv|
are different changes, even though both go from $v$ to |v `oplus`
dv|.

In fact, we can have multiple changes between the same source and target. For
instance, we can go from list |['a', 'b', 'c']| to list |['a', 'b', 'd']| by
first removing |'c'| and then adding |'d'|, hence through change |[Remove 2,
Insert 2 'd']|, or by inserting |'d'| and removing |'c'| through either of
|[Insert 3 'd', Remove 2]| or by |[Insert 2 'd', Remove 3]|.
We can also remove and readd all elements.

Therefore, we define an
equivalence among such changes that we call \emph{change
  equivalence}. When it is clear we are talking about changes, we
will also say that two changes are equivalent to mean that they
are change-equivalent. The definition of change equivalence is as
follows:

\begin{definition}[Change equivalence]
  Given a change structure $\chs V$, a value |v `elem` V|,
  and two changes |dv1, dv2| having |v| as source
  (|dv1, dv2 `elem` Dt ^ v|), we say that |dv1|
  is change-equivalent (or just equivalent) to |dv2|
  (written |dv1 `doe` dv2|) if and only if these changes share,
  beyond the source |v|, also their target, that is, if and only
  if |v `oplus` dv1 = v `oplus` dv2|.
\end{definition}

\begin{lemma}
  \label{def:diff-update-lemma}
  We have |(v `oplus` dv) `ominus` v `doe` dv| for any change
  structure $\chs V = |(V, Dt, `oplus`, `ominus`)|$, base value
  |v `elem` V| and change |dv| valid for |v| (that is, |dv `elem`
  Dt^v|).
\end{lemma}
\begin{optionalproof}
Since both sides are changes for |v|, the thesis is equivalent to |v `oplus` ((v
`oplus` dv) `ominus` v) = v `oplus` dv|.

To prove our thesis, we remember that thanks to \cref{def:update-diff},
for any |v1, v2 `elem` V| we have |v1 `oplus` (v2 `ominus` v1) = v2|. We can take |v1
= v|, |v2 = v `oplus` dv| and obtain |v `oplus` ((v `oplus` dv) `ominus` v) = v
`oplus` dv|, which is exactly our thesis.
\end{optionalproof}

With change equivalence we can generalize some rules from high
school algebra. There, we learn to add or subtract members from
both sides of an equation: if and only if |a = b| then |a + c = b
+ c| and |a - c = b - c|, so that |a + b = c| is equivalent to |a
= c - b|. Similarly we have:

\begin{lemma}[Equivalence cancellation]
  \label{thm:equiv-cancel}
  |v2 `ominus` v1 `doe` dv| holds if and only if |v2 = v1 `oplus`
  dv|, for any |v1, v2 `elem` V| and |dv `elem` Dt ^ v1|.
\end{lemma}
\begin{optionalproof}
  We prove both sides of the equivalence separately.
  First, if |v2 `ominus` v1 `doe` dv|, by definition |v1 `oplus` (v2
  `ominus` v1) = v1 `oplus` dv|, and canceling on the left side
  we get |v2 = v1 `oplus` dv| as desired.

  Second, if |v2 = v1 `oplus` dv|, then |v2 `ominus` v1 = (v1
  `oplus` dv) `ominus` v1 `doe` dv| (using change cancellation in
  the last step) as desired.
\end{optionalproof}

Change equivalence is indeed an equivalence relation, as stated
in the following lemma:
\begin{lemma}[Change equivalence is indeed an equivalence relation]
  For any change structure $\chs V$ and for any base value |v
  `elem` V|, change equivalence is an equivalence relation
  (reflexive, symmetric, transitive) among elements of |Dt v|.
\end{lemma}
\begin{optionalproof}
  The proofs apply the definition of change equality reduces each property to
  the same property for equality.

  Change equivalence is reflexive: |dv `doe` dv| for any |dv `elem` Dt ^ v|,
  because by reflexivity of equality |v `oplus` dv = v `oplus` dv|.

  Change equivalence is also symmetric: |dv2 `doe` dv1| iff |dv1 `doe` dv2|,
  because by symmetry of equality |v `oplus` dv2 = v `oplus` dv1| iff |v `oplus`
  dv1 = v `oplus` dv2|.

  Finally, change equivalence is transitive: |dv1 `doe` dv2| and |dv2 `doe` dv3|
  imply |dv1 `doe` dv3|, because by transitivity of equality |v `oplus` dv1 = v
  `oplus` dv2| and |v `oplus` dv2 = v `oplus` dv3| imply |v `oplus` dv1 = v
  `oplus` dv3|.
\end{optionalproof}

\begin{lemma}
  \label{thm:nil-equivs}
  Nil changes are equivalent to each other, that is, |v `oplus` dv = v| implies
  |dv `doe` nil v|, for any change structure $\chs V$ and value |v `elem` V|.
\end{lemma}
\begin{optionalproof}
  All nil changes for |v| share the same source and destination |v|, so they're
  equivalent.
\end{optionalproof}

As we will see, each valid operations in our theory (such as
derivatives) will respect change equivalence: equivalent changes
will be mapped to equivalent changes or to equal values. See in
particular \cref{thm:deriv-respect-doe,thm:change-respect-doe}.

\paragraph{Why not quotient change sets}%
\pg{Explain why we don't just take a quotient. We need to explain
  earlier what our metatheory's foundation is. Move the footnote
  on HoTT here.}

Instead of working explicitly with change sets and change equivalence, we could quotient change sets by change equivalence. \pg{In fact, here we work using setoids.} Then, whenever we define an operation on changes, we would be forced to show it respects change equivalence; here we need to state this as an additional result.
We avoid quotienting for a few reasons:
\begin{itemize}
\item The theory of changes is mechanized in Agda, which is based
  in intentional Martin-Löf type theory that does not provide
  quotient types, only setoids (essentially, what we are using),
  even though we usually hide this aspect. We could use variants
  of type theory which support quotient types (among others,
  observational type theory and homotopy type theory), but we
  decided to stick to standard type theory constructions; among
  other reasons, some formalization techniques we use (such as
  typed deBrujin indexes) do not work.%
  \pg{Revise when we describe our mechanization earlier.}
\item The goal of our theory is to support reasoning on programs,
  and in programs we do not have the option of working concretely
  with quotient types.
\item Processing two equivalent changes can have different
  performance. Take again the example above: we can go from a
  base list |v1 = ['a', 'b', 'c']| to another list |v2 = ['a',
  'b', 'd']| by a change |dv1| that just removes element |'c'|
  and adds element |'d'|, or by a change |dv2| that removes all
  elements of |v1| and then adds all elements of |v2|.
  Derivatives processing changes |dv1| or |dv2| are guaranteed to
  produce equivalent results, but inspecting |dv1| is faster than
  inspecting |dv2|, so we expect that also processing |dv1| will
  be faster than processing |dv2|.
\end{itemize}

\section{Derivatives}
After defining change structures, we can define more formally
derivatives of functions, using a variant of
\cref{eq:correctness}.

\begin{definition}[Derivatives]
  \label{def:derivatives}
  We call binary function |df : (a : A) -> (da : Dt ^ a) -> Dt (f a)|
  a \emph{derivative} of |f| if
  \[|f (a `oplus` da) = f a `oplus` df a da|\] holds for all values |a
  `elem` A| and corresponding changes |da `elem` Dt ^ a|, assuming a function |f
  `elem` A -> B| and change structures $\chs A$ and $\chs B$ on the domain and
  codomain of function |f|.\qed
\end{definition}

This definition implies that |df a da| is a change for |f a| for any suitable
base value |a| and change |da|.

Using change equivalence we immediately obtain an alternative characterization of derivatives:

\begin{lemma}[Characterization of derivatives up to change equivalence]
  \label{lem:derivatives-up-to-doe}
  A derivative |df| of function |f `elem` A -> B| can be characterized (up to
  change equivalence) by |df a da `doe` f (a `oplus` da) `ominus` f a|.
\end{lemma}
\begin{optionalproof}
  Since |df v dv| is a change for |f v|, inlining the definition of change
  equivalence in the thesis gives
  \[|f a `oplus` df a da = f a `oplus` (f (a `oplus` da) `ominus` f a)|\] Once
  we simplify the right-hand side via \cref{def:update-diff}, we're left with
  \[|f a `oplus` df a da = f (a `oplus` da)|\]
  which is the defining property of derivatives.\qed
\end{optionalproof}

It also follows that a function, in general, can have different
derivatives. Later, in \cref{thm:deriv-unique}, we show all
derivatives of the same function are ``equivalent'' in some
sense.
%
Take a function |f `elem` A -> B|, with a derivative |df1|, base
input |a `elem` A| and change |da `elem` Dt ^ a|. Let |db1| be
the result of |df1 a da|. Now |db1| is only specified up to
change equivalence, so if there is a |db2| different but
equivalent from |db1| (|db2 `doe` db1|, |db2 /= db1|), then we
can define a different derivative |df2| of |f| that is equal to
|df1| everywhere except that |df2 a da = db2|. Hence these two
derivatives are different.

\begin{examples}
Let |f: Bag S -> Bag S| be the constant function mapping
everything to the empty bag. Its derivative
|df : Bag S -> Bag S -> Bag S| has to ignore its two
arguments and produce the empty bag in all cases.

Let |id: Bag S -> Bag S| be the identity function between
bags. Its derivative |did| is defined by
|did v dv = dv|.
\end{examples}

\pg{Anticipate this point.}
Here we are defining derivatives of mathematical functions, but
we will use them to define the meaning of derivatives of
programs. Intuitively, once we define a suitable set-theoretic
denotational semantics for programs, and a program transformation
that takes a program |f| to its derivative |df|, we will ensure
that (in essence) our semantics takes a program derivative |eval(df)| to a
derivative of the semantics of the base program |eval(f)|.%
\footnote{We say ``in essence'' because of some technical complications discussed in \cref{sec:erasure,def:erasure}.}

We immediately verify that derivatives respect change equivalence, as promised
earlier in \cref{sec:changeeeq}:

\begin{lemma}[Derivatives respect change equivalence]
  \label{thm:deriv-respect-doe}
  A derivative |df| of function |f `elem` A -> B| always respects change
  equivalence, that is, if |dv1 `doe` dv2|, then |df v dv1 `doe` df v dv2|, for
  any value |v `elem` A|, change structure $\chs A$ and changes |dv1, dv2 `elem`
  Dt v|.
\end{lemma}
\begin{optionalproof}
  By hypothesis changes |dv1| and |dv2| are equivalent, that is |v `oplus` dv1 = v `oplus` dv2|. We
  prove the thesis directly by equational reasoning using \cref{lem:derivatives-up-to-doe}:
  \[|df v dv1 `doe` f (v `oplus` dv1) `ominus` f v = f (v `oplus` dv2) `ominus`
    f v `doe` df v dv2|\text{.}\qed\]
\end{optionalproof}

%
Next we can prove that derivatives take nil changes to nil
changes, \emph{up to change equivalence}. This lemma allows to
skip calling a derivative on a nil change, and produce a nil
change directly; this is an important optimization.\pg{revise and find back
  pointers to this from later.}

\begin{lemma}[Derivatives take nil changes to nil changes]
  \label{thm:deriv-nil}
  Applying a derivative to a value and its nil change gives a nil change, up to
  change equivalence; formally, we have |df a (nil a) `doe` (nil(f a))| for any
  change structures $\chs A$ and $\chs B$, function |f `elem` A -> B|, value |a
  `elem` A|, and |df| derivative of |f|.
\end{lemma}
\begin{optionalproof}
  We prove the thesis |df a (nil a) `doe` (nil(f a))| equationally:
\begin{equational}
\begin{code}
      df a (nil a)
`doe` {- by the definition of derivatives (\cref{def:derivatives}) -}
      f (a `oplus` nil a) `ominus` f a
=     {- because |nil(a)| is a nil change (\cref{thm:update-nil-v2}) -}
      f a `ominus` f a
=     {- by the definition of nil changes (\cref{def:nil-change-v2}) -}
      nil (f a)
\end{code}
\end{equational}
\end{optionalproof}

\input{pldi14/sec-function-change}
