% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Change structures}
\label{ch:change-theory}
In the previous chapter, we have shown that evaluating the result
of differentiation produces a valid change |dv| from the old
output |v1| to the new one |v2|.
%
To \emph{compute} |v2| from |v1| and |dv|, in this chapter we
introduce formally the operator |`oplus`| mentioned earlier.

To define differentiation on primitives, plugins need a few operations on
changes,
% Moreover, it is not yet clear concretely how plugins should
% define differentiation on primitives.
% To write derivatives on
% primitives, we will need operations on changes,
not just |`oplus`|, |`ominus`|, |`ocompose`| and |nilc|.

To formalize these operators and specify their behavior, we extend the notion of
basic change structure into the notion of \emph{change structure} in
\cref{sec:change-structures-formal}.
The change structure for function spaces is not entirely intuitive, so we
motivate it in \cref{sec:chs-funs-informal}.
Then, we show how to take change structures on |A| and |B| and
define new ones on |A -> B| in \cref{sec:chs-fun-chs}. Using
these structures, we finally show that starting from change
structures for base types, we define change structures for
all types |tau| and contexts |Gamma| in \cref{sec:chs-types-contexts},
completing the core theory of changes.

% \pg{elsewhere, where?}
% As anticipated, we use changes to generalize the calculus of finite differences
% from groups (see \cref{sec:generalize-fin-diff}). We show how change structures
% generalize groups in \cref{sec:change-structure-groups}.

% We will summarize this section in \cref{fig:change-structures};
% readers might want to jump there for the definitions. However, we
% first build up to those definitions.\pg{Correct when revising figures.}

\section{Formally defining ⊕ and change structures}
%\subsection{Updating values by changes with ⊕}
\label{sec:change-structures-formal}
\label{sec:oplus}
%\label{sec:invalid}
In this section, we define what is a \emph{change structure} on a
set |V|. A change structure |chs(V)| extends a basic change structure
|bchs(V)| with
\emph{change operators} |`oplus`|, |`ominus`|, |`ocompose`| and
|nilc|. Change structures also require change operators to
respect validity, as described below.
Key properties of change structures follow in
\cref{sec:chs-properties}.

As usual, we'll use metavariables |v, v1, v2, ...| will range over elements of
|V|, while |dv, dv1, dv2, ...| will range over elements of
|Dt^V|.

% For instance, updating a value |v1| with a valid change |fromto
% tau v1 dv v2| must produce its destination |v2| (that is, |v1
% `oplus` dv = v2|).
% and explain why the converse is not true.
\pg{Make sure we explain \emph{somewhere} why the converse is not true.}

\pg{Update earlier mention in chapter 11}
Let's first recall change operators.
Operator |`oplus`| (``oplus'') updates a value with a change: If |dv| is a
valid change from |v1| to |v2|, then |v1 `oplus` dv| (read as
``|v1| updated by |dv|'' or ``|v1| oplus |dv|'') is guaranteed to
return |v2|.
Operator |`ominus`| (``ominus'') produces a difference between two values: |v2
`ominus` v1| is a valid change from |v1| to |v2|.
Operator |nilc| (``nil'') produces nil changes: |nil v| is a nil
change for |v|.
Finally, change composition |`ocompose`| (``ocompose'') ``pastes
changes together'': if |dv1| is a valid change from |v1| to |v2|
and |dv2| is a valid change from |v2| to |v3|, then |ocompose dv1
dv2| (read ``|dv1| composed with |dv2|'') is a valid change from |v1| to |v3|.
% It's useful to
% compare the statement of this law to the transitivity of a
% relation or to the typing of function
% composition.\footnote{This analogy can be made formal by
%   saying that triples |(v1, dv, v2)| such that |fromto V v1
%   dv v2| are the arrows of a category under change
%   composition, where objects are individual values.}

We summarize these descriptions in the following definition.

\begin{definition}
  \label{def:change-structure}
  A change structure |chs(V)| over a set |V| requires:
  \begin{subdefinition}
  \item A basic change structure for |V| (hence change set |Dt^V|
    and validity |fromto V v1 dv v2|).
  \item An update operation |`oplus` : V -> Dt^V -> V| that
    \emph{updates} a value with a change. Update must agree with
    validity: for all |fromto V v1 dv v2| we require |v1 `oplus` dv = v2|.
  \item A nil change operation |nilc : V -> Dt^V|, that must
    produce nil changes: for all |v : V| we require |fromto V v (nil v) v|.
  \item a difference operation |`ominus` : V -> V -> Dt^V| that
    produces a change across two values: for all |v1, v2 : V| we require
    |fromto V v1 (v2 `ominus` v1) v2|.
  \item a change composition operation
    |`ocompose` : Dt^V -> Dt^V -> Dt^V|,
    that composes together two changes relative to a base value.
    Change composition must preserve validity:
    for all |fromto V v1 dv1 v2| and |fromto V v2 dv2 v3|
    we require |fromto V v1 (ocompose dv1 dv2) v3|.
  \end{subdefinition}
\end{definition}

\begin{notation}
Operators |`oplus`| and |`ominus`| can be subscripted to
highlight their base set, but we will usually omit such
subscripts. Moreover, |`oplus`| is left-associative, so that
|v `oplus` dv1 `oplus` dv2| means |(v `oplus` dv1) `oplus` dv2|.

Finally, whenever we have a change structure such as
|chs(A)|, |chs(B)|, |chs(V)|, and so on, we write respectively
|A|, |B|, |V| to refer to its base set.
\end{notation}

\subsection{Example: Group changes}
\label{sec:change-structure-groups}

As an example, we show next that each group induces a change structure on its
carrier. This change structure also subsumes basic change structures we saw
earlier on integers.
% To define aggregation, we will need to use a change structure on
% groups.
\begin{definition}[Change structure on groups |G|]
\label{def:chs-group}
Given any group |(G, e, +, -)| we can define a change structure
|chs(G)| on carrier set |G| as follows.
\begin{subdefinition}
\item The change set is |G|.
\item Validity is defined as |fromto G g1 dg g2| if and only if
  |g2 = g1 + dg|.
\item Change update coincides with |+|: |g1 `oplus` dg = g1 +
  dg|. Hence |`oplus`| agrees \emph{perfectly} with validity: for all |g1
  `elem` G|, all
  changes |dg| are valid from |g1| to |g1 `oplus` dg| (that is
  |fromto G g1 dg (g1 `oplus` dg)|).
\item We define difference as |g2 `ominus` g1 = (- g1) + g2|.
  Verifying |fromto G g1 (g2 `ominus` g1) g2| reduces to
  verifying |g1 + ((- g1) + g2) = g2|, which follows from group axioms.
\item The only nil change is the identity element: |nil g = e|.
  Validity |fromto G g (nil g) g| reduces to |g + e = g| which
  follows from group axioms.
\item Change composition also coincides with |+|: |ocompose dg1
  dg2 = dg1 + dg2|. Let's prove that composition respects
  validity. Our hypothesis is |fromto G g1 dg1 g2| and |fromto G
  g2 dg2 g3|.
  Because |`oplus`| agrees perfectly with validity, the
  hypothesis is equivalent to |g2 = g1 `oplus` dg1| and
  \[|g3 = g2 `oplus` dg2 = (g1 `oplus` dg1) `oplus` dg2|.\]
  Our thesis is |fromto G g1 (dg1 `ocompose` dg2) g3|, that is
  \[|g3 = g1 `oplus` (dg1 `ocompose` dg2)|.\]
  Hence the thesis reduces to
  \[|(g1 `oplus` dg1) `oplus` dg2 = g1 `oplus` (dg1 `ocompose` dg2)|,\]
  hence to |g1 + (dg1 + dg2) = (g1 + dg1) + dg2|, which is just
  the associative law for group |G|.
\end{subdefinition}
\end{definition}

As we show later\pg{where}, group change structures are useful to support
aggregation.
\subsection{Properties of change structures}
\label{sec:chs-properties}
To understand better the definition of change structures, we
present next a few lemmas following from this definition.

\begin{restatable}[|`ominus`| inverts |`oplus`|]{lemma}{oplusOminusChS}
  \label{thm:oplusOminusChS}
  |`oplus`| inverts |`ominus`|, that is
  \[|v1 `oplus` (v2 `ominus` v1) = v2|,\] for change structure
  |chs(V)| and any values |v1, v2 : V|.
\end{restatable}
\begin{proof}
  For change structures, we know |fromto V v1 (v2 `ominus` v1)
  v2|, and |v1 `oplus` (v2 `ominus` v1) = v2| follows.

  More in detail: Change |dv = v2 `ominus` v1| is a valid change
  from |v1| to |v2| (because |`ominus`| produces valid changes,
  |fromto V v1 (v2 `ominus` v1) v2|), so updating |dv|'s source
  |v1| with |dv| produces |dv|'s destination |v2| (because
  |`oplus`| agrees with validity, that is if |fromto V v1 dv v2|
  then |v1 `oplus` dv = v2|).
\end{proof}

%format v2a = "v_{2a}"
%format v2b = "v_{2b}"
\begin{lemma}[A change can't be valid for two destinations with the same source]
  Given a change |dv : Dt^V| and a source |v1 : V|, |dv| can only
  be valid with |v1| as source for a \emph{single} destination.
  That is, if |fromto V v1 dv v2a| and |fromto V v1 dv v2b| then |v2a =
  v2b|.
\end{lemma}
\begin{proof}
  The proof follows, intuitively, because |`oplus`| also maps
  change |dv| and its source |v1| to its destination, and
  |`oplus`| is a function.

  More technically, since |`oplus`| respects validity, the
  hypotheses mean that |v2a = v1 `oplus` dv = v2b| as required.
\end{proof}
Beware that, changes can be valid for multiple sources, and associate
them to different destination. For instance, integer |0| is a
valid change for all integers.\pg{For this we need to know that
  there's a change structure for integers.}

If a change |dv| has source |v|, |dv|'s destination equals |v `oplus` dv|.
So, to specify that |dv| is valid with source |v|, without mentioning |dv|'s
destination, we introduce the following definition.
\begin{definition}[One-sided validity]
  We define relation |validV(A)| as
  |{(v, dv) `elem` A `times` Dt^A `such` fromto V v dv (v `oplus` dv)}|.
\end{definition}

We use this definition right away:
\begin{lemma}[|`ocompose`| and |`oplus`| interact correctly]
  If |valid V v1 dv1| and |valid V (v1 `oplus` dv1) dv2| then
  |v1 `oplus` (ocompose dv1 dv2) = v1 `oplus` dv1 `oplus` dv2|.
\end{lemma}
\begin{proof}
  We know that |`ocompose`| preserves validity, so under the
  hypotheses |valid V v1 dv1| and |valid V (v1 `oplus` dv1) dv2|
  we get that |dv = ocompose dv1 dv2| is a valid change from
  |v1| to |v1 `oplus` dv1 `oplus` dv2|:
  \[|fromto V v1 (ocompose dv1 dv2) v1 `oplus` dv1 `oplus` dv2|.\]
  Hence, updating |dv|'s source |v1| with |dv|
  produces |dv|'s destination |v1 `oplus` dv1 `oplus` dv2|:
  \[|v1 `oplus` (ocompose dv1 dv2) = v1 `oplus` dv1 `oplus`
    dv2|.\]
\end{proof}

% \begin{lemma}[|`ocompose`| and |`oplus`| interact correctly]
%   If |fromto V v1 dv1 v2| and |fromto V v2 dv2 v3| then |v1
%   `oplus` (ocompose dv1 dv2) = v1 `oplus` dv1 `oplus` dv2|.
% \end{lemma}
% \begin{proof}
%   We know that |`ocompose`| preserves validity, so under the
%   hypotheses |fromto V v1 dv1 v2| and |fromto V v2 dv2 v3| we get
%   that |dv = ocompose dv1 dv2| is a valid change from |v1| to
%   |v3| (|fromto V v1 (ocompose dv1 dv2) v3|). Hence, updating
%   |dv|'s source |v1| with |dv| produces |dv|'s destination |v3|.
% \end{proof}

We can define |nilc| in terms of other
operations, and prove they satisfy their requirements for change
structures.

\begin{lemma}[|nilc| can be derived from |`ominus`|]
  \label{lem:nilc-derived}
  If we define |nil v = v `ominus` v|, then |nilc| produces
  valid changes as required (|fromto V v (nil v) v|), for any
  change structure |chs(V)| and value |v : V|.
\end{lemma}
\begin{proof}
  This follows from validity of |`ominus`| (|fromto V v1 (v2
  `ominus` v1) v2|) instantiated with |v1 = v| and |v2 = v|.
\end{proof}

Moreover, nil changes are a right identity element for |`oplus`|:
\begin{restatable}[Nil changes are identity elements]{corollary}{nilChangesRightId}
  \label{lem:nilChangesRightId}
  Any nil change |dv| for a value |v| is a right identity element for
  |`oplus`|, that is we have |v `oplus` dv = v| for every set |V|
  with a basic change structure, every element |v `elem` V| and
  every nil change |dv| for |v|.
\end{restatable}
\begin{proof}
  This follows from \cref{thm:valid-oplus} and the definition of
  nil changes.
\end{proof}

The converse of this theorem does not hold: there exists changes
|dv| such that |v `oplus` dv = v| yet |dv| is not a valid change
from |v| to |v|.
More in general, |v1 `oplus` dv = v2| does not imply that |dv| is a valid
change.
For instance, under earlier definitions for
changes on naturals, if we take |v = 0| and |dv = -5|, we have |v
`oplus` dv = v| even though |dv| is not valid; examples of
invalid changes on functions are discussed at \cref{sec:invalid}.
However, we prefer to define ``|dv| is a nil change'' as we do,
to imply that |dv| is valid, not just a neutral element.

\section{Operations on function changes, informally}
\label{sec:chs-funs-informal}
\subsection{Examples of nil changes}
\label{sec:nil-changes-intro}

We have not defined any change structure yet, but we can already exhibit nil
changes for some values, including a few functions.
\begin{examples}
  \begin{itemize}
  \item
An environment change for an empty environment |emptyRho :
eval(emptyCtx)| must be an environment for the empty context
|Dt^emptyCtx = emptyCtx|, so it must be the empty environment! In
other words, if and only if |fromto emptyCtx emptyRho drho
emptyRho|, then and only then |drho = emptyRho| and, in
particular, |drho| is a nil change.

\item If all values in an environment |rho| have nil changes,
the environment has a nil change |drho = nil(rho)| associating
each value to a nil change. Indeed, take a context |Gamma| and a
suitable environment |rho : eval(Gamma)|. For each typing
assumption |x : tau| in |Gamma|, assume we have a nil change |nil
v| for |v|. Then we define |nil rho : eval(Dt^Gamma)| by
structural recursion on |rho| as:
\begin{code}
  nil emptyRho = emptyRho
  nil (rho, x = v) = nil rho, x = v, dx = nil v
\end{code}
Then we can see that |nil rho| is indeed a nil change for |rho|,
that is, |fromto Gamma rho (nil rho) rho|.
\item We have seen in \cref{thm:derive-correct} that, whenever
  |Gamma /- t : tau|, |eval t| has nil change |evalInc t|.
  Moreover, if we have an appropriate nil environment change
  |fromto Gamma rho drho rho| (which we often do, as discussed
  above), then we also get a nil change |evalInc t rho drho| for
  |eval t rho|:
\[|fromto tau (eval t
  rho) (evalInc t rho drho) (eval t rho)|.\]
In particular, for all closed well-typed terms |/- t : tau| we have
\[|fromto tau (eval t
emptyRho) (evalInc t emptyRho emptyRho) (eval t emptyRho)|.\]
\end{itemize}
\end{examples}

\subsection{Nil changes on arbitrary functions}
\label{sec:nil-changes-fun-intro}

We have discussed how to find a nil change |nil f| for a function
|f| if we know the \emph{intension} of |f|, that is, its
definition. What if we have only its \emph{extension}, that is,
its behavior? Can we still find |nil f|?
That's necessary to implement |nilc| as an
object-language function |nilc| from |f| to |nil f|, since such a
function does not have access to |f|'s implementation. That's
also necessary to define |nilc| on metalanguage function spaces---and we look at this case first.

We seek a nil change |nil f| for an arbitrary
metalanguage function |f : A -> B|, where |A| and |B| are
arbitrary sets; we assume a basic change structure on |A -> B|,
and will require |A| and |B| to support a few additional
operations. We require that
\begin{equation}
  \label{eq:search-nil-fun}
  |fromto (A -> B) f (nil f) f|.
\end{equation}
Equivalently, whenever |fromto A a1 da a2| then |fromto B (f a1) (nil f a1
da) (f a2)|. By \cref{thm:valid-oplus}, it follows that
\begin{equation}
  \label{eq:search-nil-fun-oplus}
  |f a1 `oplus` nil f a1 da = f a2|,
\end{equation}
where |a1 `oplus` da = a2|.

To define |nil f| we solve \cref{eq:search-nil-fun-oplus}. To understand how, we
use an analogy.
|`oplus`| and |`ominus`| are intended to resemble |+| and |-|.
To solve |f a1 + nil f a1 da = f a2|, we subtract |f a1|
from both sides and write |nil f a1 da = f a2 - f a1|.

Similarly, here we use operator |`ominus`|: |nil f| must equal
\begin{equation}
  \label{eq:define-nil-fun}
|nil f = \a1 da -> f (a1 `oplus` da) `ominus` f a1|.
\end{equation}
Because |fromto B b1 (b2 `ominus` b1) b2| for all |b1, b2 : B|, we can verify
that |nil f| as defined by \cref{eq:define-nil-fun} satisfies our original
requirement \cref{eq:search-nil-fun}, not just its weaker consequence
\cref{eq:search-nil-fun-oplus}.

We have shown that, to define |nilc| on functions |f : A -> B|,
we can use |`ominus`| at type |B|. Without using |f|'s intension,
we are aware of no alternative. To ensure |nil f| is defined for
all |f|, we require that change structures define |`ominus`|. We
can then define |nilc| as a derived operation via |nil v = v
`ominus` v|, and verify this derived definition satisfies
requirements for |nil|.

Next, we show how to define |`ominus`| on functions. We seek a
valid function change |f2 `ominus` f1| from |f1| to |f2|. We have
just sought and found a valid change from |f| to |f|;
generalizing the reasoning we used, we obtain that whenever
|fromto A a1 da a2| then we need to have |fromto B (f1 a1) ((f2
`ominus` f1) a1 da) (f2 a2)|; since |a2 = a1 `oplus` da|, we can
define

\begin{equation}
  \label{eq:ominus-fun-1}
|f2 `ominus` f1 = \a1 da -> f2 (a1 `oplus` da) `ominus` f1 a1|.
\end{equation}

One can verify that \cref{eq:ominus-fun-1} defines |f2 `ominus`
f1| as a valid function from |f1| to |f2|, as desired.
And after defining |f2 `ominus` f1|, we need no more to define
|nil f| separately using \cref{eq:define-nil-fun}.
We can just define |nil f = f `ominus` f| simplify through the definition
of |`ominus`| in \cref{eq:ominus-fun-1}, and reobtain \cref{eq:define-nil-fun}
as a derived equation:
%
\[
  |nil f = f `ominus` f = \a1 da -> f (a1 `oplus` da) `ominus` f
  a1|,
\]

We defined |f2 `ominus` f1| on metalanguage functions. We can also internalize
change operators in our object language, that is, define for each type |tau|
object-level terms |oplusIdx(tau)|, |ominusIdx(tau)|, and so on, with the same
behavior.
We can define object-language change operators such as |`ominus`| using the same
equations. However, the produced function change |df| is slow, because it
recomputes the old output |f1 a1|, computes the new output |f2 a2| and takes the
difference.

However, we can implement |ominusIdx(sigma -> tau)| using replacement changes, if
they are supported by the change structure on type |tau|.
Let us define |ominusIdx(tau)| as |b2 `ominus` b1 = !b2| and simplify
\cref{eq:ominus-fun-1}; we obtain
\[|f2 `ominus` f1 = \a1 da -> ! (f2 (a1 `oplus` da))|.\]

We could even imagine allowing replacement changes on functions
themselves. However, here the bang operator needs to be defined
to produce a function change that can be applied, hence
\[|!f2 = \a1 da -> ! (f2 (a1 `oplus` da))|.\]

Alternatively, as we see in
\cref{ch:defunc-fun-changes}, we could represent function changes
not as functions but as data through \emph{defunctionalization},
and provide a function applying defunctionalized function changes
|df : Dt^(sigma -> tau)| to inputs |t1 : sigma| and |dt :
Dt^sigma|. In this case, |!f2| would simply be another way to
produce defunctionalized function changes.

\subsection{Constraining ⊕ on functions}
\label{sec:oplus-fun-intro}
Next, we discuss how |`oplus`| must be defined on functions, and
show informally why we must define |f1 `oplus` df = \v -> f1 x
`oplus` df v (nil v)| to prove that |`oplus`| on functions agrees
with validity (that is, \cref{thm:valid-oplus}).

We know that a valid function change |fromto (A -> B) f1 df
f2| takes valid input changes |fromto A v1 dv v2| to a valid
output change |fromto B (f1 v1) (df v1 dv) (f2 v2)|. We require
that |`oplus`| agrees with validity (\cref{thm:valid-oplus}), so
|f2 = f1 `oplus` df|, |v2 = v1 `oplus` dv| and
%
\begin{equation}
  \label{eq:fun-preserv-eq}
|f2 v2 = (f1 `oplus` df) (v1 `oplus` dv) = f1 v1 `oplus` df v1
  dv|.
\end{equation}
%
Instantiating |dv| with |nil v| gives equation
%
\[|(f1 `oplus` df) v1 = (f1 `oplus` df) (v1 `oplus` nil v) = f1 v1 `oplus` df v1 (nil v)|,\]
%
which is not only a requirement on |`oplus`| for functions but
also defines |`oplus`| effectively.

\section{Families of change structures}
\label{sec:chs-fun-chs}

In this section, we derive change structures for |A -> B| and |A `times` B| from
two change structures |chs(A)| and |chs(B)|.
The change structure on |A -> B| enables defining change structures for function
types.
Similarly, the change structure on |A `times` B| enables defining a change
structure for product types in a language plugin, as described in
\cref{ch:prod-sums}. In \cref{ch:prod-sums} we also discuss change structures
for disjoint sums.
% In \cref{sec:chs-product,sec:chs-sums} we will also define change
% structures for |A `times` B| and |A + B|, for use in language
% plugins for types |sigma `times` tau| and |sigma + tau|.

\subsection{Change structures for function spaces}
\Cref{sec:chs-funs-informal} introduces informally how to define change
operations on |A -> B|. Next, we define formally change structures on function
spaces, and then prove its operations respect their constraints.

\begin{definition}[Change structure for |A -> B|]
  \label{def:chs-fun}
  Given change structures |chs(A)| and |chs(B)| we define a change structure on
  their function space |A -> B|, written |chs(A) -> chs(B)|, where:
  \begin{subdefinition}
  \item The change set is defined as: |Dt^(A -> B) = A -> Dt^A -> Dt^B|.
  \item Validity is defined as
    \begin{multline*}
      |fromto (A -> B) f1 df f2 = forall a1 da a2 . (fromto A a1 da a2)| \\
      \text{ implies } |(fromto B (f1 a1) (df a1 da) (f2 a2))|.
    \end{multline*}
  \item We define change update by
    \[|f1 `oplus` df = \a -> f1 a `oplus` df a (nil a)|.\]
  \item We define difference by \[|f2 `ominus` f1 = \a da -> f2 (a `oplus` da)
      `ominus` f1 a|.\]
  \item We define |nilc| like in \cref{lem:nilc-derived} as \[|nil f = f
      `ominus` f|.\]
  \item We define change composition as \[|ocompose df1 df2 = \a da -> ocompose
      (df1 a (nil a)) (df2 a da)|.\]
  \end{subdefinition}
\end{definition}

\begin{lemma}
  \Cref{def:chs-fun} defines a correct change structure |chs(A) ->
  chs(B)|.
\end{lemma}
\begin{proof}

  \begin{itemize}
  \item We prove that |`oplus`| agrees with validity on |A -> B|. Consider |f1 ,
    f2: A -> B| and |fromto (A -> B) f1 df f2|; we must show that |f1 `oplus` df
    = f2|. By functional extensionality, we only need prove that |(f1 `oplus`
    df) a = f2 a|, that is that |f1 a `oplus` df a (nil a) = f2 a|. Since
    |`oplus`| agrees with validity on |B|, we just need to show that |fromto B
    (f1 a) (df a (nil a)) (f2 a)|, which follows because |nil a| is a valid
    change from |a| to |a| and because |df| is a valid change from |f1| to |f2|.
  \item We prove that |`ominus`| produces valid changes on |A -> B|. Consider
    |df = f2 `ominus` f1| for |f1, f2: A -> B|. For any valid input |fromto A a1
    da a2|, we must show that |df| produces a valid output with the correct
    vertexes, that is, that |fromto B (f1 a1) (df a1 da) (f2 a2)|. Since
    |`oplus`| agrees with validity, |a2| equals |a1 `oplus` da|. By substituting
    away |a2| and |df| the thesis becomes |fromto B (f1 a1) (f2 (a1 `oplus` da)
    `ominus` f1 a1) (f2 (a1 `oplus` da))|, which is true because |`ominus`|
    produces valid changes on |B|.
  \item |nilc| produces valid changes as proved in \cref{lem:nilc-derived}.
  \item We prove that change composition preserves validity on |A -> B|. That
    is, we must prove \[|fromto B (f1 a1) (ocompose (df1 a1 (nil a1)) (df2 a1
      da)) (f3 a2)|\] for every |f1, f2, f3, df1, df2, a1, da, a2| satifsfying
    |fromto (A -> B) f1 df1 f2|, |fromto (A -> B) f2 df2 f3| and |fromto A a1 da
    a2|.

    Because change composition preserves validity on |B|, it's enough to prove
    that (1) |fromto B (f1 a1) (df1 a1 (nil a1)) (f2 a1)| (2) |fromto B (f2 a1)
    (df2 a1 da) (f3 a2)|. That is, intuitively, we create a composite change
    using |`ocompose`|, and it goes from |f1 a1| to |f3 a2| passing through |f2
    a1|. Part (1) follows because |df1| is a valid function change from |f1| to
    |f2|, applied to a valid change |nil a1| from |a1| to |a1|.\pg{} Part (2)
    follows because |df2| is a valid function change from |f2| to |f3|, applied
    to a valid change |da| from |a1| to |a2|.
  \end{itemize}
\end{proof}
% \paragraph{Aside}\pg{mention alternative definition of change composition?}

\subsection{Change structures for products}
\label{sec:chs-product}

We can define change structures on products |A `times` B|, given
change structures on |A| and |B|: a change on pairs is just a
pair of changes; all other change structure definitions
distribute componentwise the same way, and their correctness
reduce to the correctness on components.

Change structures on $n$-ary products or records present no additional
difficulty.

\begin{definition}[Change structure for |A `times` B|]
  \label{def:chs-prod}
  Given change structures |chs(A)| and |chs(B)| we define a
  change structure |chs(A) `times` chs(B)| on product |A `times` B|.
  \begin{subdefinition}
  \item The change set is defined as: |Dt^(A `times` B) = Dt^A `times` Dt^B|.
  \item Validity is defined as
    \begin{multline*}
      |fromto (A `times` B) ((a1, b1)) ((da, db)) ((a2, b2)) =| \\
      |(fromto A a1 da a2)| \text{ and } |(fromto B b1 db b2)|.
    \end{multline*}
    %
    In other words, validity distributes componentwise: a product change
    is valid if each component is valid.
  \item We define change update by
    \[|(a1, b1) `oplus` (da , db) = (a1 `oplus` da, b1 `oplus` db)|.\]
  \item We define difference by
    \[|(a2, b2) `ominus` (a1, b1) = (a2 `ominus` a1, b2 `ominus` b1)|.\]
  \item We define |nilc| to distribute componentwise:
    \[|nil (a, b) = (nil a, nil b)|.\]
  \item We define change composition to distribute componentwise:
    \[|ocompose ((da1, db1)) ((da2, db2)) =
    (ocompose da1 da2, ocompose db1 db2)|.\]
  \end{subdefinition}
\end{definition}

\begin{lemma}
  \Cref{def:chs-prod} defines a correct change structure |chs(A) `times`
  chs(B)|.
\end{lemma}
\begin{proof}
Since all these proofs are similar and spelling out their details does not make
them clearer, we only give the first such proof in full.
  \begin{itemize}
  \item |`oplus`| agrees with validity on |A `times` B| because
    |`oplus`| agrees with validity on both |A| and |B|. For this
    property we give a full proof.

    For each |p1 , p2: A `times` B|
    and |fromto (A `times` B) p1 dp p2|, we must show that |p1
    `oplus` dp = p2|. Instead of quantifying over pairs |p : A
    `times` B|, we can quantify equivalently over components |a :
    A, b : B|.
    Hence, consider |a1, a2: A|, |b1, b2: B|, and changes |da,
    db| that are valid, that is, |fromto A a1 da a2| and |fromto
    B b1 db b2|: We must show that \[|(a1, b1) `oplus` (da, db) =
    (a2, b2)|.\] That follows from |a1 `oplus` da = a2| (which
    follows from |fromto A a1 da a2|) and |b1 `oplus` db = b2|
    (which follows from |fromto B b1 db b2|).
  \item |`ominus`| produces valid changes on |A `times` B|
    because |`ominus`| produces valid changes on both |A| and
    |B|. We omit a full proof; the key step reduces the thesis
    \[|fromto (A `times` B) ((a1, b1)) ((a2, b2) `ominus` (a1, b1))
    ((a2, b2))|\] to |fromto A a1 (a2 `ominus` a1) a2| and |fromto
    B b1 (b2 `ominus` b1) b2| (where free variables range on
    suitable domains).
  \item |nil (a, b)| is correct, that is |fromto (A `times` B)
    ((a, b)) ((nil a, nil b)) ((a, b))|, because |nilc| is
    correct on each component.
  \item Change composition is correct on |A `times` B|, that is
    \[|fromto (A `times` B) ((a1, b1)) ((ocompose da1 da2,
      ocompose db1 db2)) ((a3, b3))|\] whenever |fromto (A `times` B)
    ((a1, b1)) ((da1, db1)) ((a2, b2))| and |fromto (A `times` B)
    ((a2, b2)) ((da2, db2)) ((a3, b3))|, in essence because
    change composition is correct on both |A| and |B|. We omit details.
  \end{itemize}
\end{proof}

\section{Change structures for types and contexts}
\label{sec:chs-types-contexts}

As promised, given change structures for base types we can
provide change structures for all types:

\begin{restatable}[Change structures for base types]{requirement}{baseChs}
  For each base type |iota| we must have a change structure
  |chs(iota)| defined on base set |eval(iota)|, based on the
  basic change structures defined earlier.
\end{restatable}

\begin{definition}[Change structure for types]
  \label{def:chs-types}
  For each type |tau| we define a change structure |chs(tau)| on
  base set |eval(tau)|.
\begin{code}
  chs(iota) = ...
  chs(sigma -> tau) = chs(sigma) -> chs(tau)
\end{code}
\end{definition}
\begin{lemma}
  Change sets and validity, as defined in \cref{def:chs-types},
  give rise to the same basic change structures as the ones
  defined earlier in \cref{def:bchs-types}, and to the change operations
  described in \cref{fig:chs-types}.
\end{lemma}
\begin{proof}
  This can be verified by induction on types. For each case, it
  is sufficient to compare definitions.
\end{proof}
\begin{fullCompile}
\validOplus
\end{fullCompile}
\begin{partCompile}
  \begin{restatable*}[|`oplus`| agrees with validity]{lemma}{validOplus}
    \label{thm:valid-oplus}
    If |fromto tau v1 dv v2| then |v1 `oplus` dv = v2|.
  \end{restatable*}
\end{partCompile}
\begin{proof}
  Because |chs(tau)| is a change structure and in change structures |`oplus`|
  agrees with validity.
\end{proof}

As shortly proved in \cref{sec:correct-derive}, since |`oplus`|
agrees with validity (\cref{thm:valid-oplus}) and |derive(param)|
is correct (\cref{thm:derive-correct}) we get
\cref{thm:derive-correct-oplus}:

\begin{fullCompile}
\deriveCorrectOplus
\end{fullCompile}
\begin{partCompile}
\begin{restatable}[|derive(param)| is correct, corollary]{corollary}{deriveCorrectOplus}
  \label{thm:derive-correct-oplus}
  If |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |eval(t) rho1 `oplus` eval(derive(t)) drho = eval(t) rho2|.
\end{restatable}
\end{partCompile} 

We can also define a change structure for environments.
Recall that change structures for products define their operations to act on
each component.
Each change structure operation for environments acts ``variable-wise''. Recall
that a typing context |Gamma| is a list of variable assignment |x : tau|. For
each such entry, environments |rho| and environment changes |drho| contain a
base entry |x = v| where |v : eval(tau)|, and possibly a change |dx = dv| where
|dv : eval(Dt^tau)|.

%format drho1
%format drho2

\begin{definition}[Change structure for environments]
  \label{def:chs-envs}
  To each context |Gamma| we associate a change structure
  |chs(Gamma)|, that extends the basic change structure from \cref{def:bchs-contexts}.
  Operations are defined as shown in \cref{fig:chs-env}.
\end{definition}
Base values |v'| in environment changes are redundant with base values |v| in
base environments, because for valid changes |v = v'|.
So when consuming an environment change, we choose arbitrarily to use |v| instead
of |v'|. Alternatively, we could also use |v'| and get the same results for
valid inputs.
When producing an environment change, they are created to ensure validity of the
resulting environment change.

\begin{lemma}
  \Cref{def:chs-envs} defines a correct change structure |chs(Gamma)| for each
  context |Gamma|.
\end{lemma}
\begin{proof}
  All proofs are by structural induction on contexts.
  Most details are analogous to the ones for products and add no
  details, so we refer to our mechanization for most proofs.

  However we show by induction that |`oplus`| agrees with validity.
  For the empty context there's a single environment |emptyRho :
  eval(emptyCtx)|, so |`oplus`| returns the correct environment |emptyRho|.
  For the inductive case |Gamma', x: tau|,
  inversion on the validity judgment reduces our hypothesis to |fromto tau v1 dv
  v2| and |fromto Gamma rho1 drho rho2|, and our thesis to |(rho1, x = v1) `oplus`
  (drho, x = v1, dx = dv) = (rho2, x = v2)|, where |v1| appears both in the base
  environment and the environment change. The thesis follows because |`oplus`|
  agrees with validity on both |Gamma| and |tau|.
\end{proof}

%%%%
% What's below must be revised.
%%%%
We summarize definitions on types in \cref{fig:change-structures}.

Finally, we can lift change operators from the semantic level to the syntactic
level so that their meaning is coherent.

\begin{definition}[Term-level change operators]
  \label{def:term-change-ops}
  We define type-indexed families of change operators at the term level with the following signatures:
  %For each type |tau| we define type-indexed families  operators at the term-level
  \begin{code}
  oplusIdx(tau) : ^^ tau -> Dt^tau -> tau
  ominusIdx(tau) : ^^ tau -> tau -> Dt^tau
  nilIdx(tau, param) : ^^ tau -> Dt^tau
  ocomposeIdx(tau) : ^^ Dt^tau -> Dt^tau -> Dt^tau
\end{code}
and definitions:
\begin{code}
  tf1 (oplusIdx(sigma -> tau)) dtf = \x -> tf1 x `oplus` dtf x (nil x)
  tf2 (ominusIdx(sigma -> tau)) tf1 = \x dx -> tf2 (x `oplus` dx) `ominus` tf1 x
  nilIdx(sigma -> tau, tf) = tf (ominusIdx(sigma -> tau)) tf
  dtf1 (ocomposeIdx(sigma -> tau)) dtf2  = \x dx -> dtf1 x (nil x) `ocompose` dtf2 x dx

  tf1 (oplusIdx(iota)) dtf = ...
  tf2 (ominusIdx(iota)) tf1 = ...
  nilIdx(iota, tf) = ...
  dtf1 (ocomposeIdx(iota)) dtf2  = ...
  \end{code}
\end{definition}

\begin{lemma}[Term-level change operators agree with change structures]
  \label{lem:chops-coherent}
  The following equations hold for all types |tau|, contexts |Gamma|
  well-typed terms |Gamma /- t1, t2 : tau|, |Dt^Gamma /- dt, dt1, dt2 : Dt^tau|
  and environments |rho : eval(Gamma)| |drho : eval(Dt^Gamma)| such that all
  expressions are defined.
\begin{code}
eval (t1 (oplusIdx(tau)) dt) drho = eval t1 drho `oplus` eval dt drho
eval (t2 (ominusIdx(tau)) t1) rho = eval t2 rho `oplus` eval t1 rho
eval (nilIdx(tau, t)) rho = nil (eval t rho)
eval (dt1 (ocomposeIdx(tau)) dt2) drho = eval dt1 drho `ocompose` eval dt2 drho
\end{code}
\end{lemma}
\begin{proof}
  By induction on types and simplifying both sides of the equalities. The proofs
  for |`oplus`| and |`ominus`| must be done by simultaneous induction.
\end{proof}
\pg{Fix this?}
At the time of writing, we have not mechanized the proof for |`ocompose`|.

To define the lifting and prove it coherent on base types, we must add a further
plugin requirement.

\begin{restatable}[Term-level change operators for base types]{requirement}{baseChOps}
  For each base type |iota| we define change operators as required by \cref{def:term-change-ops}
  and satisfying requirements for \cref{lem:chops-coherent}.
\end{restatable}
% \pg{Both change structure requirements, theorems on types}
% \begin{restatable}[|`ominus`| produces valid changes]{lemma}{validOminus}
%   \label{thm:valid-ominus}
%   |`ominus`| produces valid changes, that is |fromto tau v1 (v2
%   `ominus` v1) v2| and |v1 `oplus` (v2 `ominus` v1) = v2| for any
%   type |tau| and any |v1, v2 : eval(tau)|.
% \end{restatable}
% \begin{restatable}[|`ominus`| inverts |`oplus`|]{lemma}{oplusOminus}
%   For any type |tau| and any values |v1, v2 : eval(tau)|,
%   |`oplus`| inverts |`ominus`|, that is |v1 `oplus` (v2 `ominus`
%   v1) = v2|.
% \end{restatable}
% \begin{proof}
%   From \cref{thm:valid-ominus,thm:valid-oplus}.
% \end{proof}

%% Remember that, as we proved earlier:
%% \deriveCorrectOplus*

% \nilChangesExist*
% \begin{proof}\pg{?}
% \end{proof}


% We only need |`ominus`| to be able to define nil changes on
% arbitrary functions |f : eval(sigma -> tau)|.

% However, as anticipated earlier, if |f| is the semantics of a
% well-typed term |t|, that is |f = eval(t) emptyRho|, we can
% define the nil change of |f| through its derivative.\pg{See
%   before}
% no, we need full abstraction, unless the term is closed.

% \NewDocumentCommand{\RightFramedSignatureML}{m}
% {\vbox{\hfill\fbox{\(
%         #1
% \)
%     }}}

\begin{figure}
\begin{subfigure}[c]{\textwidth}
  \RightFramedSignature{|oplusIdx(tau): eval(tau -> Dt^tau -> tau)|}
  \RightFramedSignature{|ominusIdx(tau): eval(tau -> tau -> Dt^tau)|}
  \RightFramedSignature{|nil: eval(tau -> Dt^tau)|}
  \RightFramedSignature{|ocomposeIdx(tau): eval(Dt^tau -> Dt^tau -> Dt^tau)|}
\begin{code}
  f1 (oplusIdx(sigma -> tau))      df   = \v -> f1 v `oplus` df v (nil v)
  v1 (oplusIdx iota)               dv   = ...
  f2 (ominusIdx (sigma -> tau))    f1   = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
  v2 (ominusIdx iota)              v1   = ...
  nil v                                 = v (ominusIdx(tau)) v
  dv1 (ocomposeIdx(iota))          dv2  = ...
  df1 (ocomposeIdx(sigma -> tau))  df2  = \v dv -> df1 v (nil v) `ocompose` df2 v dv
\end{code}
\caption{Change structure operations on types (see \cref{def:chs-types}).}
\label{fig:chs-types}
\end{subfigure}
\begin{subfigure}[c]{\textwidth}
  \RightFramedSignature{|oplusIdx(Gamma): eval(Gamma -> Dt^Gamma -> Gamma)|}
  \RightFramedSignature{|ominusIdx(Gamma): eval(Gamma -> Gamma -> Dt^Gamma)|}
  \RightFramedSignature{|nil: eval(Gamma -> Dt^Gamma)|}
  \RightFramedSignature{|ocomposeIdx(Gamma): eval(Dt^Gamma -> Dt^Gamma -> Dt^Gamma)|}
\begin{code}
  emptyRho `oplus` emptyRho                                                       = emptyRho
  (rho, x = v) `oplus` (drho, x = v', dx = dv)                                    = (rho `oplus` drho, x = v `oplus` dv)

  emptyRho `ominus` emptyRho                                                      = emptyRho
  (rho2, x = v2) `ominus` (rho1, x = v1)                                          = (rho2 `ominus` rho1, x = v1, dx = v2 `ominus` v1)

  nil emptyRho                                                                    = emptyRho
  nil (rho, x = v)                                                                = (nil rho, x = v, dx = nil v)

  ocompose emptyRho emptyRho                                             = emptyRho
  ocompose ((drho1, x = v1, dx = dv1)) ((drho2, x = v2, dx = dv2))  =
      (ocompose drho1 drho2, x = v1, dx = ocompose dv1 dv2)
\end{code}
  % nil emptyRho = emptyRho
  % nil (rho, x = v) = nil rho, x = v, dx = nil v
\caption{Change structure operations on environments (see \cref{def:chs-envs}).}
\label{fig:chs-env}
\end{subfigure}
\validOplus*
  \deriveCorrectOplus*

  \caption{Defining change structures.}
  \label{fig:change-structures}
\end{figure}

% \subsection{Change structures, algebraically}
% \label{sec:chs-alg}
% \pg{INCOMPLETE}
% \pg{Move to later, *if* we keep this.}
% If we ignore validity requirements, we can rephrase laws of
% change structures as algebraic equations:
% \begin{code}
%   v1 `oplus` (v2 `ominus` v1) = v2
%   v1 `oplus` (nil v1) = v1
%   v1 `oplus` (ocompose dv1 dv2) = v1 `oplus` dv1 `oplus` dv2
% \end{code}
% Later, once we define a suitable equivalence relation |`doe`| on
% changes, we'll also be able to state a few further algebraic laws:
% \begin{code}
%   nil v1 `doe` v1 `ominus` v1
%   (v1 `oplus` dv) `ominus` v1 `doe` dv
% \end{code}

% Now this equation is a bit more confusing.
%   ocompose dv1 dv2 = v1 `oplus` dv1 `oplus` dv2 `ominus` v1

% We can define
% \begin{code}
%   valid : (v : V) -> (dv : Dt V) -> Set
%   valid v dv = fromto V dv v (v `oplus` dv)
%   Dt : (v : V) -> Set
%   Dt^v = Sigma [ dv `elem` Dt V ] valid v dv
% \end{code}

% Alternatively, with two-sided validity, we could define:
% \begin{code}
%   Dt2 : (v1 v2 : V)
%   Dt2 : (v1 v2 : V) -> Set
%   Dt2 v1 v2 = Sigma [ dv `elem` Dt V ] ch dv from v1 to v2

%   oplus : (v1 : V) -> {v2 : V} -> (dv : Dt2 v1 v2) -> V
%   ominus : (v2 v1 : V) -> (Dt2 v2 v1)
%   `ocompose` : {v1 v2 v3 : V} -> (dv1 : Dt2 v1 v2) -> (dv2 : Dt2 v2 v3) -> Dt2 v1 v3
% \end{code}

\section{Development history}
\label{sec:ilc-dev-history}
The proof presented in this and the previous chapter is an
significant evolution of the original one by \citet{CaiEtAl2014ILC}.
%
While this formalization and the mechanization are both original
with this thesis, some ideas were suggested by other
(currently unpublished) developments by Yufei Cai and by Yann
Régis-Gianas. Yufei Cai gives a simpler pen-and-paper set-theoretic proof by
separating validity, while we noticed separating validity works
equally well in a mechanized type theory and simplifies the
mechanization.
The first to use a two-sided validity relation was Yann Régis-Gianas, but using
a big-step operational semantics, while we were collaborating on an ILC
correctness proof for untyped $\lambda$-calculus (as in \cref{ch:bsos}).
I gave the first complete and mechanized ILC correctness proof
using two-sided validity, again for a simply-typed
$\lambda$-calculus with a denotational semantics. Based on
two-sided validity, I also reconstructed the rest of the theory
of changes.

\section{Chapter conclusion}
In this chapter, we have seen how to define change operators, both on semantic
values nad on terms, and what are their guarantees, via the notion of change
structures. We have also defined change structures for groups, function spaces
and products. Finally, we have explained and shown
\cref{thm:derive-correct-oplus}.
We continue in next chapter by discussing how to reason syntactically about
changes, before finally showing how to define some language plugins.

% \citeauthor{CaiEtAl2014ILC}'s definition resembles our definition
% of |Dt^v = Sigma [ dv `elem` Dt V ] valid v dv| in
% \cref{sec:chs-alg}; indeed, for any natural |n : Nat| the two
% definitions of |Dt^n| are the same.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% \subsection{Derivatives are nil changes}
% \pg{This now goes earlier?}
% When we introduced derivatives, we claimed we can compute them by
% applying differentiation to function bodies.
% In fact, we can
% compute the derivative of a closed lambda abstraction by
% differentiating the whole abstraction!

% To see why, let's first consider an arbitrary closed term |t|,
% such that |/- t : tau|.

% If we differentiate a closed term |/- t : tau|, we get a change
% term |derive(t)| from |t| to itself\pg{Lexicon not introduced for
%   terms.}: |fromto tau (eval(t)
% emptyRho) (eval(derive(t)) emptyRho) (eval(t) emptyRho)|. We call such changes nil changes;
% they're important for two reasons. First, we will soon see that a
% identity element for |`oplus`| has its uses. Second, nil changes at
% function type are even more useful. A nil function change for
% function |f| takes an input |v1| and input change |dv| to a
% change from |f v1| and |f (v1 `oplus` dv)|. In other words, a nil
% function change for |f| is a \emph{derivative} for |f|!

% %\pg{steps}
% To sum up, if |f| is a closed function |derive(f)| is its
% derivative. So, if |f| is unary, \cref{eq:derivative-requirement}
% becomes in particular:
% \begin{equation}
%   \label{eq:correctness}
%   |f (a `oplus` da) `cong` (f a) `oplus` (derive(f) a da)|
% \end{equation}

\pg{move back in, readd, ...}

% \subsection{Differentiation}
% After we defined our language, its type system and its semantics, we motivate
% and sketch what differentiation does on an arbitrary well-typed term |t| such
% that |Gamma /- t : tau|. We will later make all this more formal.

% For any type |tau|, we introduce type |Dt ^ tau|, the type of changes for terms
% of type |tau|. We also have operator |oplusIdx(tau) : tau -> Dt ^ tau -> tau|;
% we typically omit its subscript. So if |x : tau| and |dx : Dt ^ tau| is a change
% for |x|, then |x `oplus` dx| is the destination of that change. We overload
% |`oplus`| also on semantic values. So if |v : eval(tau)|, and if |dv : eval(Dt ^
% tau)| is a change for |v|, then |v `oplus` dv : eval(tau)| is the destination of
% |dv|.

% We design differentiation to satisfy two (informal) invariants:
% \begin{itemize}
% \item Whenever the output of |t| depends on a base input |x : sigma|, |derive(t)| depends on
%   input |x : sigma| and a change |dx : Dt ^ sigma| for |x|.
% \item Term |derive(t)| has type |Dt ^ tau|. In particular, |derive(t)| produces
%   a change from |t| evaluated on all base inputs, to |t| evaluated on all base
%   inputs updated with the respective changes.
% \end{itemize}

% Consider |\x -> x + y|.

% Term |t| depends on values for free variables. So whenever |x : sigma| is free
% in |t|, |dx : Dt ^ sigma| should be free in |derive(t)|. To state this more
% formally we define \emph{change contexts} |Dt ^ Gamma|.\pg{Definition.}
% \begin{code}
%   Dt ^ emptyCtx = emptyCtx
%   Dt ^ (Gamma, x : tau) = Dt ^ Gamma, dx : Dt ^ tau
% \end{code}

% We can then state the static semantics of differentiation.
% \begin{typing}
% \Rule[Derive]
%   {\Typing{t}{\tau}}
%   {\Typing[\Append{\GG}{\DeltaContext{\GG}}]{\Derive{t}}{\DeltaType{\tau}}}
% \end{typing}

% Moreover, |eval(t)| takes an environment |rho : eval(Gamma)|, so
% |eval(derive(t))| must take environment |rho| and a \emph{environment change}
% |drho : eval(Dt ^ Gamma)| that is a change for |rho|.

% We also extend |`oplus`| to contexts pointwise:
% \begin{code}
%   emptyRho `oplus` emptyRho = emptyRho
%   (rho , x = v) `oplus` (drho, dx = dv) = (rho `oplus` drho, x = v `oplus` dv)
% \end{code}

% Since |derive(t)| is defined in a typing context |Gamma, Dt ^ Gamma| that merges
% |Gamma| and |Dt ^ Gamma|, |eval(derive(t))| takes an environment |rho, drho|
% that similarly merges |rho| and |drho|.
% \begin{code}
%   eval(t) rho `oplus` eval(derive(t)) (rho, drho) = eval(t) (rho `oplus` drho)
% \end{code}

% To exemplify the above invariants, take a term |t| with one free variable: |x :
% sigma /- t : tau|. Values of free variables are inputs to terms just like
% function arguments. So take an input |v `elem` eval(sigma)| and change |dv| for
% |v|. Then we can state the correctness condition as follows:
% \begin{code}
%   eval(t) (emptyRho, x = v) `oplus` eval(derive(t)) (emptyRho, x = v, dx = dv) =
%   eval(t) (emptyRho, x = v `oplus` dv)
% \end{code}

% Earlier we looked at derivatives of functions.
% Let |t| is a unary closed
% function: | /- t : sigma -> tau|. Take an input |v `elem` eval(sigma)| and
% change |dv| for |v|. Then |emptyCtx /- derive(t) : sigma -> Dt ^ sigma -> Dt ^
% tau| and
% \begin{code}
%   eval(t) emptyRho v `oplus` eval(derive(t)) emptyRho v dv = eval(t) emptyRho (v `oplus` dv)
% \end{code}

% Next, we look at differentiating a function. Take again a term |t| such that |x
% : sigma /- t : tau|, and consider term |t1 = \x : sigma . t| (which is
% well-typed: | /- \x : sigma -> t : sigma -> tau|).
% From requirements above, we want |emptyCtx /- derive(\x : sigma . t) : Dt ^
% (sigma -> tau)|.

% Consider a few examples:

% \begin{itemize}
% \item
% \item
%   Let |t| be a unary closed function: | /- t : sigma -> tau|. Take an input |v `elem` eval(sigma)| and
%   change |dv| for |v|. Then |emptyCtx /- derive(t) : sigma -> Dt ^ sigma -> Dt ^ tau| and
% \begin{code}
%   eval(t) emptyRho v `oplus` eval(derive(t)) emptyRho v dv = eval(t) emptyRho (v `oplus` dv)
% \end{code}
% %
% \item Take a binary closed function |t| : | /- t : sigma1 -> sigma2 -> tau|, inputs |v `elem` eval(sigma1)|, |u `elem` eval(sigma2)|, and changes |dv| for |v| and |du| for |u|.
%   Then |emptyCtx /- derive(t) : sigma1 -> Dt ^ sigma1 -> sigma2 -> Dt ^ sigma2 -> Dt ^ tau|.
% \begin{code}
%   eval(t) emptyRho v u `oplus` eval(derive(t)) emptyRho v dv u du =
%   eval(t) emptyRho (v `oplus` dv) (u `oplus` du)
% \end{code}
% %
% \end{itemize}

% As we see, we want |derive(t)| to handle changes to both values of free
% variables and function arguments. We define

% To handle changes to free variables, we define changes contexts |Dt ^ Gamma|


% To better understand what are the appropriate inputs to consider,
% let's recall what are the inputs to the semantics of |t|.
% Semantics |eval(t)| takes an environment |rho1 : eval(Gamma)| to an output |v1|.
% If |tau| is a function type |sigma1 -> tau1|, output |v1| is in turn a function
% |f1|, and applying this function to a further input |a1 : eval(sigma1)| will
% produce an output |u1 `elem` eval(tau1)|. In turn, |tau1| can be a function type,
% so that |u1| takes another argument\ldots
% Overall we can apply |eval(t)| to an appropriate environment |rho1| and as
% many inputs as called for by |tau| to get, in the end, a result of base type.
% Similarly, we can evaluate |t| with updated input |rho2| getting output |v2|. If
% |tau| is a function type, |v2| is a function |f2| that takes further input |a2|
% to output |u2 `elem` eval(tau1)|, and soon.

% We design differentiation so that the semantics of the derivative of |t|,
% |eval(derive(t))|, takes inputs and changes for all those inputs. So
% |eval(derive(t))| takes a base environment |rho1| and a environment change
% |drho| from |rho1| to |rho2| and produces a change |dv| from |v1| to |v2|. If
% |tau| is a function type, |dv| is a \emph{function change} |df| from |f1| to
% |f2|. that in turn takes base input |a1| and an input change |da| from |a1| to
% |a2|, and evaluate to an output change |du| from |u1| to |u2|.

% \begin{code}
%   derive(\x -> t) = \x dx -> derive(t)
%   derive(s t) = derive(s) t (derive(t))
%   derive(x) = dx
% \end{code}
% % Inputs to |t| include the environment it is
% % evaluated in, while the output of |t| might be a function. Since a function takes in
% % turn further inputs, we want a function change to
% % change, in turn, takes further inputs

% % To refine this definition we must consider however \emph{all}
% % inputs: this includes both the environment in which we evaluate |t|, as well as
% % any function arguments it takes (if |t| evaluates to a function). In fact, |t| might be a function change itself
% % Hence we say that

% % \begin{itemize}
% % \item function |eval(derive(t)| is a for function |eval(t)|
% % \item a function change for |f| takes a
% %   , that is, a change from |eval(t)| to |eval(t)|
% %  )
% % \item the derivative of a function takes
% %   evaluating with |eval(-)| the derivative
% %   |eval(derive(t))|
% %   |t| might be in general an open term in context |Gamma|, that must be evaluated in an environment |rho1| that matches |Gamma|; we define the evaluation . Then evaluating |eval(Derive(t))|
% % \item
% % a change to a function |f : A -> B| is a function |df| that takes a base input
% % \end{itemize}
% % As we hinted, derivative computes the

% % More in general, we extend differentiation on arbitrary terms.
% % The derivative of a term |t| is a new term |Derive(t)| in
% % the same language, that accepts changes to all inputs of |t| (call them |x1, x2,
% % ..., xn| of |t| and evaluates to the change of |t|)


% \begin{code}
%   t ::= t1 t2 | \x -> t | x | c
% \end{code}

% \section{A program transformation}
% To support automatic incrementalization, in the next chapters we
% introduce the \ILC\ (incrementalizing $\Gl$-calculi) framework.
% We define an automatic program transformation $\DERIVE$ that
% \emph{differentiates} programs, that is, computes their total
% derivatives with respect to all inputs.

% $\DERIVE$ guarantees that
% \begin{equation}
%   \label{eq:correctness}
%   |f (a `oplus` da) `cong` (f a) `oplus` (derive(f) a da)|
% \end{equation}
% where
% $\cong$ is denotational equality,
% |da| is a change on |a| and |a `oplus` da| denotes |a|
% updated with change |da|, that is, the updated input of |f|.
% Hence, when the derivative is faster than
% recomputation, we can optimize programs by replacing the
% left-hand side, which recomputes the output from scratch, with
% the right-hand side, which computes the output incrementally
% using derivatives, while preserving the program result.

% To understand this equation we must also formalize changes for
% functions. That's because \ILC\ applies to higher-order
% languages, where functions can be inputs or outputs. This makes
% \cref{eq:correctness} less trivial to state and prove.

% To simplify the formalization we consider, beyond derivatives of
% programs, also derivatives of pure mathematical functions
% (\cref{sec:1st-order-changes}). We distinguish programs and
% mathematical functions as in denotational semantics. We avoid
% however using domain theory. To this end, we restrict attention
% in our theory to strongly normalizing calculi.
% %
% We define those with an analogue of
% \cref{eq:correctness}: function |df| is a derivative of |f| if
% and only if
% \begin{equation}
%   \label{eq:correctness-math-funs}
%   |f (a `oplus` da) = (f a) `oplus` (df a da)|
% \end{equation}
% Once we establish a theory of changes and derivatives for
% mathematical functions, we will be able to lift that to programs:
% intuitively, a program function |df| is a derivative of |f| if
% the semantics of |df|, that is |eval(df)|, is the derivative of
% the semantics of |f|, giving us \cref{eq:correctness} from
% \cref{eq:correctness-math-funs}.\footnote{A few technical details
%   complicate the picture, but we'll discuss them later.}

% \section{Based changes}
% \pg{We can study }

