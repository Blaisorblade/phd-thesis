% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

%\section{Changes as First-Class Values}
\section{A theory of changes}
\label{sec:1st-order-changes}

This section introduces a formal concept of changes; this
concept was already used informally in \cref{eq:correctness} and is central
to our approach. We first define change structures formally, then construct 
change structures for functions between change structures,
and conclude with a theorem that relates function changes to derivatives. 

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
  A tuple $\ChangeStruct{V} = (V, \CHANGE,
  \UPDATE,
  \DIFF)$ is a \emph{change structure} (for $V$) if:

  \begin{subdefinition}
  \item $V$ is a set, called the \emph{base set}.
  \item Given $v \in V$, $\Change{v}$ is a set, called the \emph{change set}.
  \item Given $v \in V$ and $\D v \in \Change{v}$,
    $\Apply{\D v}{v} \in V$. We also call $v$ the \emph{base
      value} of the change, or its \emph{source}; we call
    $\Apply{\D v}{v}$ the \emph{updated value} of the change, or
    its \emph{destination}/\emph{target}.
    \label{def:update}
  \item Given $u, v \in V$, $\Diff{u}{v} \in \Change{v}$.
    \label{def:diff}
  \item Given $u, v \in V$, $\Apply{\Diff*{u}{v}}{v}$ equals $u$.
    \qed
    \label{def:update-diff}
  \end{subdefinition}
\end{definition}

\paragraph{Notation}
We overload operators $\CHANGE$, $\DIFF$ and $\UPDATE$ to refer
to the corresponding operations of different change structures;
we will subscript these symbols when needed to prevent ambiguity.
For any $\ChangeStruct{S}$, we write $S$ for its first component,
as above. We make $\UPDATE$ left-associative, that is,
$\Update{\Update{v}{dv_1}}{dv_2}$ means $\Update{\Update*{v}{dv_1}}{dv_2}$.
We assign precedence to function application over
$\UPDATE$ and $\DIFF$, that is, $\Update{\App{f}{a}}{\App{\App{g}{a}}{\D a}}$ means
$\Update{\App*{f}{a}}{\App*{\App{g}{a}}{\D a}}$.

\paragraph{Change equivalence}
One might expect, in the definition of change structures
(\cref{def:change-struct}), the additional assumption that
$\Diff{\Apply*{\D v}{v}}{v} = \D v$. While this assumption holds
for the change structure of $\mathbb{N}$, there are sensible
examples of change structures where this assumption is not valid.
In fact, we can have multiple changes between the same source and
target. \pg{Add example on lists.} Therefore, we define an
equivalence among such changes that we call \emph{change
  equivalence}. When it is clear we are talking about changes, we
will also say that two changes are equivalent to mean that they
are change-equivalent. The definition of change equivalence is as
follows:

\begin{definition}[Change equivalence]
  Given a change structure $\ChangeStruct{V}$, a value $v \in V$,
  and two changes $\D v_1, \D v_2$ having $v$ as source, that is,
  such that $\D v_1, \D v_2\in \Change{v}$, we say that $\D v_1$
  is change-equivalent to $\D v_2$ and write
  $\D v_1 \Doe \D v_2$, if and only if these changes share,
  beyond the source $v$, also their target, that is, if and only
  if $\Update{v}{\D v_1} = \Update{v}{\D v_2}$.
\end{definition}

\begin{lemma}
  \label{def:diff-update-lemma}
  Given a change structure |chs(V) = (V, Dt, `oplus`, `ominus`)|,
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
  For any change structure |chs(V)| and for any base value |v
  `elem` V|, change equivalence is an equivalence relation
  (reflexive, symmetric, transitive) among elements of |Dt v|.
\end{lemma}

As we will see, each valid operations in our theory will respect
change equivalence: equivalent changes will be mapped to
equivalent changes or to equal values.
\pg{Add example: however, different changes might have different values.}

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
\end{examples}

\subsubsection{Derivatives}
After defining change structures, we can define more formally
derivatives of functions, using a variant of
\cref{eq:correctness}.

\begin{definition}[Derivatives]
  \label{def:derivatives}
  Given change structures $\ChangeStruct{A}$ and $\ChangeStruct{B}$ and a function $f \in A \to
  B$ on the change sets of these change structures, we call a binary function $f'$ a \emph{derivative} of $f$ if
  for all values $a \in A$ and corresponding changes $\D a \in
  \Change[A]{a}$,
  \[\App{f}{\Apply*{\D a}{a}} = \Apply{\App{\App{f'}{a}}{\D a}}{\App{f}{a}}\text{.}\qed\]
\end{definition}

Here we are defining derivatives of mathematical functions, but
we will use them to define the meaning of derivatives of
programs. Intuitively, once we define a suitable set-theoretic
denotational semantics for programs, and a program transformation
that takes a program |f| to its derivative |f'|, we will ensure
that our semantics takes a program derivative |[[f']]| to a
derivative of the semantics of the base program |[[f]]|.

\pg{Point out here that derivatives respect change equivalence.}
\subsubsection{Nil changes and derivatives}
A change can have equal source and target, in which case we call
it a \emph{nil change}. We use $\DIFF$ to associate, to each
value, a distinguished nil change.
\pg{Rewrite}
\begin{definition}[Nil change]
  \label{def:nil-change}
  Given a change structure $\ChangeStruct{V}$ and a value $v \in V$, the change
  $\Diff{v}{v}$ is the nil change for $v$.
  \[
    \NilC{v} = \Diff{v}{v} \qed
  \]
\end{definition}
A nil change for a value does indeed not change it.
\begin{lemma}[Behavior of $\NILC$]
  \label{thm:update-nil}
  Given a change structure $\ChangeStruct{V}$ and a value $v \in V$,
  $\Apply{\NilC{v}}{v} = v$.
\end{lemma}

\begin{proof}
Follows from \cref{def:update-diff,def:nil-change}.
\end{proof}

Applying a derivative to a value and its nil change gives a nil
change.
%
\begin{lemma}[Behavior of derivatives on $\NILC$]
  \label{thm:deriv-nil}
  Given change structures $\ChangeStruct{A}$ and
  $\ChangeStruct{B}$, a function $f \in A \to B$, an element $a$
  of $A$, and the derivative $f'$ of $f$, we have
  $\App{\App{f'}{a}}{\NilC{a}} \Doe \NilC{\App* f a}$.
\end{lemma}

\begin{examples}
Let $\Term{f}:\Fun{\Bag S}{\Bag S}$ be the constant function mapping
everything to the empty bag. Its derivative
$\Term{f'}:\Fun{\Bag S}{\Fun{\Bag S}{\Bag S}}$ has to ignore its two
arguments and produce the empty bag in all cases.

Let $\Term{id}:\Fun{\Bag S}{\Bag S}$ be the identity function between
bags. Its derivative $\Term{id'}$ is defined by
$\Term{id'}~v~\D v = \D v$.
\end{examples}

\input{pldi14/sec-function-change}
