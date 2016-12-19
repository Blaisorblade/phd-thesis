% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

%\section{Changes as First-Class Values}
\section{Formalizing changes}
\label{sec:1st-order-changes}

This section introduces a formal concept of changes; this
concept was already used informally in \cref{eq:correctness} and is central
to our approach. We first define change structures formally, then construct 
change structures for functions between change structures,
and finally show that derivatives are a special case of function changes.

% In this section, we will not consider programs, but simply
% mathematical functions. In \cref{sec:differentiate} we will apply
% this theory to functions representing the meaning of programs,
% but we prefer to develop our theory

\subsection{Change structures}\label{ssec:change-structures}
Consider a set of values, for instance the set of natural numbers
$\mathbb{N}$. A change $\D v$ for $v \in \mathbb{N}$ should
describe the difference between $v$ and another natural $\New{v}
\in \mathbb{N}$. We do not define changes directly, but we
specify operations which must be defined on them. They are:
\begin{itemize}
\item We can \emph{update} a base value $v$ with a
  change $\D v$ to obtain an updated or \emph{new} value
  $\New{v}$. We write $\New{v} = \Apply{\D v}{v}$.
\item We can compute a change between two arbitrary
  values $\Old{v}$ and $\New{v}$ of the set we are considering.
  We write $\D v = \Diff{\New{v}}{\Old{v}}$.
\end{itemize}

For naturals, it is usual to describe changes using standard
subtraction and addition. That is, for naturals we can define
$\Apply{\D v}{v} = v + \D v$ and $\Diff{\New{v}}{\Old{v}} =
\New{v} - \Old{v}$. To ensure that $\APPLY$ and $\DIFF$ are
always defined, we need to define the set of changes carefully.
$\mathbb{N}$ is too small, because subtraction does not always
produce a natural; the set of integers $\mathbb{Z}$ is instead
too big, since adding a natural and an integer does not always
produce a natural. In fact, we cannot use the same set of all
changes for all naturals. Hence we must adjust the requirements:
for each base value $v$ we introduce a set $\Change{v}$ of
changes for $v$, and require $\Diff{\New{v}}{\Old{v}}$ to produce
values in $\Change{\Old{v}}$, and $\Apply{\D v}{v}$ to be defined
for $\D v$ in $\Change{v}$. For natural $v$, we set $\Change{v} =
\left\{\D v \mid v + \D v \geq 0 \right\}$; $\DIFF$ and $\APPLY$ are
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
result without even using $\Old{v}$, in time $O(|\D v|)$ (we
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

\pg{Consider less heavyweight phrasing, such as: ``To each $v \in V$
  we associate a set of changes $\Change{v}$. But do this consistently.}
\begin{definition}[Change structures]
  \label{def:change-struct}
  A tuple $\chs V = |(V, Dt, `oplus`, `ominus`)|$
  is a \emph{change structure} (for |V|) if:

  \begin{subdefinition}
  \item |V| is a set, called the \emph{base set}.
  \item |Dt ^ v| is a set, called the \emph{change set}, for any |v `elem` V|.
  \item Value |v `oplus` dv| belongs to V for any |v `elem` V| and |dv `elem` Dt
    ^ v|. We also call $v$ the \emph{base value} of the change, or its
    \emph{source}; we call |v `oplus` dv| the \emph{updated value} of the
    change, or its \emph{destination}/\emph{target}.
    \label{def:update}
  \item We have |u `ominus` v `elem` Dt ^ v| for any base values |u, v `elem` V|.
    \label{def:diff}
  \item We have |v `oplus` (u `ominus` v) = u| for any |u, v `elem` V|.
    \qed
    \label{def:update-diff}
  \end{subdefinition}
\end{definition}

\paragraph{Notation}
We overload operators $\CHANGE$, $\DIFF$ and $\UPDATE$ to refer
to the corresponding operations of different change structures;
we will subscript these symbols when needed to prevent ambiguity.
For any $\chs V$, we write |V| for its first component,
as above. We make |`oplus`| left-associative, that is,
|v `oplus` dv1 `oplus` dv2| means |(v `oplus` dv1) `oplus` dv2|.
We assign precedence to function application over
$\UPDATE$ and $\DIFF$, that is, $\Update{\App{f}{a}}{\App{\App{g}{a}}{\D a}}$ means
$\Update{\App*{f}{a}}{\App*{\App{g}{a}}{\D a}}$.

\paragraph{Changes as graph edges}
We'll also treat a change between a source and destination as an
edge between them, and use graph terminology to discuss changes.
Indeed, a change structure induces a graph with base values as
vertices and all changes as edges.

\paragraph{Nil changes}
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
  Change |v `ominus` v| is a nil change for |v| (that we write |nil(v)|), for any
  change structure $\chs V$ and value |v `elem` V|:
  \[
    |nil(v) = v `ominus` v| \qed
  \]
  \label{thm:update-nil-v2}
\end{lemma}

\begin{proof}
  By the definition of nil changes (\cref{def:nil-change-v2}) we need to show
  that |v `oplus` (v `ominus` v) = v|, which follows from
  \cref{def:update-diff}.
\end{proof}

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

\subsection{Change equivalence}
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
  Given a change structure $\chs V = |(V, Dt, `oplus`, `ominus`)|$,
  for any base value |v `elem` V| and for any change |dv| valid
  for |v| (that is, |dv `elem` Dt^v|), we have |(v `oplus` dv)
  `ominus` v `doe` dv|.
\end{lemma}
\begin{proof}
Since both sides are changes for |v|, the thesis is equivalent to |v `oplus` ((v
`oplus` dv) `ominus` v) = v `oplus` dv|.

To prove our thesis, we remember that thanks to \cref{def:update-diff},
for any |v1, v2 `elem` V| we have |v1 `oplus` (v2 `ominus` v1) = v2|. We can take |v1
= v|, |v2 = v `oplus` dv| and obtain |v `oplus` ((v `oplus` dv) `ominus` v) = v
`oplus` dv|, which is exactly our thesis.
\end{proof}

Change equivalence is indeed an equivalence relation, as stated
in the following lemma:
\begin{lemma}[Change equivalence is indeed an equivalence relation]
  For any change structure $\chs V$ and for any base value |v
  `elem` V|, change equivalence is an equivalence relation
  (reflexive, symmetric, transitive) among elements of |Dt v|.
\end{lemma}
\begin{proof}
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
\end{proof}

\begin{lemma}
  Nil changes are equivalent to each other, that is, |v `oplus` dv = v| implies
  |dv `doe` nil(v)|, for any change structure $\chs V$ and value |v `elem` V|.
\end{lemma}
\begin{proof}
  All nil changes for |v| share the same source and destination |v|, so they're
  equivalent.
\end{proof}
As we will see, each valid operations in our theory will respect change
equivalence: equivalent changes will be mapped to equivalent changes or to equal
values.\footnote{We expect that, in homotopy type theory, we could use higher
  inductive types to make change equivalence part of the equality on changes.}

\subsection{Derivatives}
After defining change structures, we can define more formally
derivatives of functions, using a variant of
\cref{eq:correctness}.

\begin{definition}[Derivatives]
  \label{def:derivatives}
  We call binary function |f'| a \emph{derivative} of |f| if
  \[|f (a `oplus` da) = f a `oplus` f' a da|\text{.}\] holds for all values |a
  `elem` A| and corresponding changes |da `elem` Dt ^ A|, assuming a function |f
  `elem` A -> B| and change structures $\chs A$ and $\chs B$ on the domain and
  codomain of function |f|.\qed
\end{definition}

This definition implies that |f' a da| is a change for |f a| for any suitable
base value |a| and change |da|.

Using change equivalence we immediately obtain an alternative characterization of derivatives:

\begin{lemma}[Characterization of derivatives up to change equivalence]
  \label{lem:derivatives-up-to-doe}
  A derivative |f'| of function |f `elem` A -> B| can be characterized (up to
  change equivalence) by |f' a da `doe` f (a `oplus` da) `ominus` f a|.
\end{lemma}
\begin{proof}
  Since |f' v dv| is a change for |f v|, inlining the definition of change
  equivalence in the thesis gives
  \[|f a `oplus` f' a da = f a `oplus` (f (a `oplus` da) `ominus` f a)|\] Once
  we simplify the right-hand side via \cref{def:update-diff}, we're left with
  \[|f a `oplus` f' a da = f (a `oplus` da)|\]
  which is the defining property of derivatives.\qed
\end{proof}


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
that takes a program |f| to its derivative |f'|, we will ensure
that our semantics takes a program derivative |eval(f')| to a
derivative of the semantics of the base program |eval(f)|.

We immediately verify that derivatives respect change equivalence, as promised
earlier in \cref{sec:changeeeq}:

\begin{lemma}[Derivatives respect change equivalence]
  \label{thm:deriv-respect-doe}
  A derivative |f'| of function |f `elem` A -> B| always respects change
  equivalence, that is, if |dv1 `doe` dv2|, then |f' v dv1 `doe` f' v dv2|, for
  any value |v `elem` A|, change structure $\chs A$ and changes |dv1, dv2 `elem`
  Dt v|.
\end{lemma}
\begin{proof}
  By hypothesis changes |dv1| and |dv2| are equivalent, that is |v `oplus` dv1 = v `oplus` dv2|. We
  prove the thesis directly by equational reasoning using \cref{lem:derivatives-up-to-doe}:
  \[|f' v dv1 `doe` f (v `oplus` dv1) `ominus` f v = f (v `oplus` dv2) `ominus`
    f v `doe` f' v dv2|\text{.}\qed\]
\end{proof}

%
\begin{lemma}[Behavior of derivatives on |NIL|]
  \label{thm:deriv-nil}
  Applying a derivative to a value and its nil change gives a nil change, up to
  change equivalence; formally, we have |df a nil(a) `doe` nil(f a)| for any
  change structures $\chs A$ and $\chs B$, function |f `elem` A -> B|, value |a
  `elem` A|, and |df| derivative of |f|.
\end{lemma}

\input{pldi14/sec-function-change}
