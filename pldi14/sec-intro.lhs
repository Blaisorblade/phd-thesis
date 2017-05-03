% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Change theory}
\label{ch:change-theory}
In the previous chapter, we have shown that evaluating the result
of differentiation produces a valid change |dv| from the old
output |v1| to the new one |v2|. We also want a way to
\emph{compute} |v2| from |v1| and |dv|, that is, we want to
\emph{define} the operator |`oplus`| that we have talked so much
about.

Moreover, it is not yet clear concretely how plugins should
define differentiation on primitives. To write derivatives on
primitives, we will need operations on changes, such as
|`oplus`|, |`ominus`|, |`ocompose`| and |nilc|, and
guarantees on their behavior. Guarantees on the behavior of
change operations will be needed to prove that programs using
change operations behave as specified. In particular, such
guarantees are required to prove that the derivatives of some
primitives are correct.

Hence, we continue exploring how changes behave, and introduce
operations (including |`oplus`|) that manipulate them. We will
define these operations both at the semantic level to operate on
change values, and on the syntactic level to use in object
programs, such as derivatives of primitives. While often the same
definitions are applicable, additional performance concerns apply
to object-level implementations.

We will summarize this section in \cref{fig:change-structures};
readers might want to jump there for the definitions. However, we
first build up to those definitions.

\section{Basic change structures}
First, we generalize the concept of changes. For each type |tau|
we have defined notions of change type and of valid changes; but
these notions can be defined for arbitrary sets.

\begin{definition}
  \label{def:bchs}
  A basic change structure for set |V| is given by defining:
  \begin{subdefinition}
  \item a change set |Dt^V|
  \item a ternary relation called validity among |V|, |Dt^V| and
    |V|. If |v1, v2 `elem` V| and |dv `elem` DV|, and this relation holds, we write
    |fromto V v1 dv v2| and say that |dv| is a valid change from |v1| to |v2|.
  \end{subdefinition}
\end{definition}

We have already given the ingredients to define two families of basic change structures,
a family for types and one for contexts:
\begin{definition}
  \label{def:bchs-types}
  To each type |tau| we associate a basic change structure for
  set |eval(tau)|; we do so by taking |eval(Dt^tau)| as change
  set and by reusing validity as previously defined. We keep
  writing |fromto tau v1 dv v2| rather than |fromto (eval(tau)) v1 dv v2|.
\end{definition}
\begin{definition}
  \label{def:bchs-contexts}
  To each environment |Gamma| we associate a basic change
  structure for set |eval(Gamma)|; we do so by taking
  |eval(Dt^Gamma)| as change set and by reusing validity as
  previously defined. We keep writing |fromto Gamma rho1 drho rho2|
  rather than |fromto (eval(Gamma)) rho1 drho rho2|.
\end{definition}
Moreover, we required that language plugins must define change
types and validity for base types
(\cref{req:base-change-types,req:base-validity}). Equivalently we
can require that plugins define basic change structures on all
base types:
\begin{restatable}[Basic change structures on base
  types]{requirement}{baseBasicChangeStructures}
  \label{req:base-basic-change-structures}
  To each base type |iota| is associated a basic change structure
  for |eval(iota)|.
\end{restatable}

Basic change structures generalize validity and change sets, so
we can talk about a change set |Dt^V| for an arbitrary set |V|,
not just for the semantics of a type (|V = eval(tau)|) or the
semantics of a context (|V = eval(Gamma)|).
%
In particular, we can define a basic change structure for any
function space |A -> B| as long as we have basic change
structures for |A| and |B|.
\begin{definition}
  \label{def:basic-change-structure-funs}
  We define a basic change structure on |A -> B| whenever |A, B|
  are sets and we have a basic change structure for each of them.
  \begin{subdefinition}
  \item we define the change set |Dt^(A -> B)| as |A -> Dt^A -> Dt^B|.
  \item we define that |df| is a valid function change from |f1|
    to |f2| (that is, |fromto (A -> B) f1 df f2|) if and only if,
    for any inputs |a1, a2 : A|, input change |da : Dt^a| that is
    valid from |a1| to |a2| (|fromto A a1 da a2|), we have
    |fromto B (f1 a1) (df a1 da) (f2 a2)|.
  \end{subdefinition}
\end{definition}

In particular, we obtain a basic change structure on |eval(Gamma)
-> eval(tau)| for any |Gamma, tau|. After a new definition, we
can restate correctness of differentiation using this new basic
change structure.

\begin{definition}[Incremental semantics]
  \label{def:inc-semantics}
  We define the \emph{incremental semantics} of a well-typed term
  |Gamma /- t : tau| in terms of differentiation as:
  \[|evalInc t = (\rho1 drho -> eval(derive t) drho) : eval(Gamma)
    -> eval(Dt^Gamma) -> eval(Dt^tau)|.\]
\end{definition}

The incremental semantics of a term |evalInc t| is a function
change for |eval t|.
The definition of incremental semantics might seem surprising,
because function change |\rho1 drho -> eval(derive(t)) drho|
appears to ignore the argument for |rho1|. But this is just an
artifact: If you take a valid change |drho| from |rho1| to
|rho2|, then |drho| extends |rho1|, so we can safely ignore
|rho1|.

\begin{theorem}[|evalInc t| is a valid change from |eval t| to |eval t|]
  \label{thm:derive-correct-2}
  If |Gamma /- t : tau|, then |evalInc(t)| is a valid change from
  |eval t| to |eval t|:
  \[
    |fromto (eval Gamma -> eval tau) (eval t) (evalInc t) (eval t)|
  \]
\end{theorem}

\begin{proof}
  By expanding \cref{def:basic-change-structure-funs,def:inc-semantics}
  one can verify this is just a restatement of \cref{thm:derive-correct}.
\end{proof}

The notion of basic change structure is somewhat weak, since we
place no constraints on validity, but we are going to build on it
a more interesting notion of \emph{change structure}, which adds
operations including |`oplus`| and requirements on them.

As anticipated, we use changes to generalize the calculus of
finite differences from groups (see
\cref{sec:generalize-fin-diff}). We'll later see how change
structures generalize groups.

Moreover, now that we defined basic change structures, we can
already talk about a set |S| with different basic change
structures defined on it, and about ways to create basic change
structures.

For instance, for any set |V| we can talk about \emph{replacement
  changes} on |V|: a replacement change |dv = !u| for a value |v
: V| simply specifies directly a new value |u : V|, so that
|fromto V v (! u) u|. We read |!| as the ``bang'' operator. A
basic change structure can decide to use only replacement changes
(which might be appropriate for primitive types with values of
constant size), or to make |Dt^V| a sum type allowing both
replacement changes and other ways to describe a change (as long
as we're using a language plugin that adds sum types).

But before defining |`oplus`|, we need to introduce a few more
concepts, as we do next.

% including |`oplus`|
% but also |nilc| and |`ominus`| and

\section{Change structures, informally}
\subsection{Nil changes}
\label{sec:nil-changes-intro}
Some valid changes have the same value |v| both as source and as
destination. They are \emph{nil changes}:
\begin{definition}[Nil changes]
  A change |dv : Dt^V| is a \emph{nil change} for a value |v : V|
  if it is a valid change from |v| to itself: |fromto V v dv v|.
\end{definition}

For instance, |0| is a nil change for any integer number |n|.
However, in general a change might be nil for an element but not
for another. For instance, the replacement change |!6| is a nil
change on |6| but not on |5|.

When we define change structures, each element is going to be
associated to at least one nil change, as we're going to show later:
\begin{restatable}[Existence of nil changes]{lemma}{nilChangesExist}
  \label{lem:nilChangesExist}
  Given a change structure for |V|, to each element |v
  `elem` V| is associated a distinguished nil change that we
  denote by |nil v|.
\end{restatable}

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
from |v| to |v|. For instance, under earlier definitions for
changes on naturals, if we take |v = 0| and |dv = -5|, we have |v
`oplus` dv = v| even though |dv| is not valid; examples of
invalid changes on functions are discussed at \cref{sec:invalid}.
However, we prefer to define ``|dv| is a nil change'' as we do,
to imply that |dv| is valid, not just a neutral element.

We can already show some values have nil changes even though we
haven't proved \cref{lem:nilChangesExist}.
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
\item We have seen in \cref{thm:derive-correct-2} that, whenever
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
That is, whenever |fromto A a1 da a2| then |fromto B (f1 a1) (nil f a1
da) (f2 a2)|. By \cref{thm:valid-oplus}, this implies that
\begin{equation}
  \label{eq:search-nil-fun-oplus}
  |f1 a1 `oplus` nil f a1 da = f2 a2|,
\end{equation}
where |a1 `oplus` da = a2|. To solve this equation, we
\emph{introduce operator |`ominus`|}, such that |a2 `ominus` a1|
produces a valid change from |a1| to |a2|, and see that |nil f|
must be

\begin{equation}
  \label{eq:define-nil-fun}
|nil f = \a1 da -> f (a1 `oplus` da) `ominus` f a1|.
\end{equation}

We can verify, in particular, that this definition for |nil f|
solves not just \cref{eq:search-nil-fun-oplus} but also
\cref{eq:search-nil-fun}.

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
f1| as a valid function from |f1| to |f2|, as desired. What's
more, our earlier specialized definition of |nil f| in
\cref{eq:define-nil-fun} becomes now redundant. We can just use
general definition |nil f = f `ominus` f|, simplify through the definition
of |`ominus`| in \cref{eq:ominus-fun-1}, and obtain
%
\[
  |nil f = f `ominus` f = \a1 da -> f (a1 `oplus` da) `ominus` f
  a1|,
\]
which is the same definition as
\cref{eq:define-nil-fun}.

We have made this definition at the meta-level. We can also use
the same definition in object programs, but there we face
additional concerns. The produced function change is rather slow,
because it recomputes the old output |f1 a1|, while also computes
the new output |f2 a2| and taking the difference.

However, we can implement |`ominus`| using replacement changes, if
they are supported on the relevant types. If we define |`ominus`|
on set |B| as |b2 `ominus` b1 = !b2| and simplify \cref{eq:ominus-fun-1},
we obtain
\[|f2 `ominus` f1 = \a1 da -> ! (f2 (a1 `oplus` da))|.\]

We could even imagine allowing replacement changes on functions
themselves. However, here the bang operator needs to be defined
to produce a function change that can be applied, hence
\[|!f2 = \a1 da -> ! (f2 (a1 `oplus` da))|.\]

Alternatively, as we'll see later in
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

% Take functions
% |f1 `oplus` df|
% Take a value |v|.
% Assume there exists a valid nil change for |v|, and
% write it |nil v| (see \cref{lem:nilChangesExist}).

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

\section{Formally defining ⊕ and change structures}
%\subsection{Updating values by changes with ⊕}
\label{sec:change-structures-formal}
\label{sec:oplus}
\label{sec:invalid}
Next, we will formally introduce \emph{change operators} |`oplus`|, |`ominus`|
and |nilc| and relate them to validity. In particular, we will
prove that |fromto tau v1 dv v2| implies |v1 `oplus` dv = v2|.
% and explain why the converse is not true.
\pg{Make sure we explain \emph{somewhere} why the converse is not true.}

To introduce these operators, we first define the notion of
\emph{change structure} on a set |V| by taking a basic change
structure on |V| and adding requirements. Then, to understand
their definition better, we prove a few corollaries of their
definition in \cref{sec:chs-properties,sec:chs-derivable-ops}.
Then, we show how to take change structures on |A| and |B| and
define new ones on |A -> B| in \cref{sec:chs-fun-chs}. Using
these structures, we finally show that starting from change
structures for base types, we can define change structures for
all types |tau| and contexts |Gamma|.

But first, we give the definition of change structures:
\begin{definition}
  \label{def:change-structure}
  A change structure |chs(V)| over a set |V| is given by:
  \begin{subdefinition}
  \item a basic change structure for |V| (hence change set |Dt^V| and validity |fromto V v1 dv v2|);
  \item an update operation \[|`oplus` : V -> Dt^V -> V|\] that
    \emph{updates} a value with a change;
  \item proof that |`oplus`| agrees with validity: if |fromto V v1 dv
    v2| then |v1 `oplus` dv = v2|;
  \item a nil change operation \[|nilc : V -> Dt^V|;\]
  \item proof that for every |v : V|, change |nil v| is a valid
    nil change for |v|, that is, |fromto V v (nil v) v|;
  \item a difference operation |`ominus` : V -> V -> Dt^V| that
    produces a change across two values;
  \item proof that |`ominus`| produces valid changes: for all |v1, v2 :
    V| we have
    \[|fromto V v1 (v2 `ominus` v1) v2|;\]
  \item a change composition operation \[|`ocompose` : Dt^V -> V -> Dt^V
      -> Dt^V|,\]
    that composes together two changes relative to a base value.
  \item proof that |`ocompose`| preserves validity: if |fromto V
    v1 dv1 v2| and |fromto V v2 dv2 v3| then
    \[|fromto V v1 (ocompose dv1 v1 dv2) v3|.\] It's useful to
    compare the statement of this law to the transitivity of a
    relation or to the typing of function
    composition.\footnote{This analogy can be made formal by
      saying that triples |(v1, dv, v2)| such that |fromto V v1
      dv v2| are the arrows of a category under change
      composition, where objects are individual values.}
  \end{subdefinition}
\end{definition}

\paragraph{Notation}
Operators |`oplus`| and |`ominus`| can be subscripted to
highlight their base set, but we will usually omit such
subscripts. Moreover, |`oplus`| is left-associative, so that
|v `oplus` dv1 `oplus` dv2| means |(v `oplus` dv1) `oplus` dv2|.

Finally, whenever we have a change structure such as
|chs(A)|, |chs(B)|, |chs(V)|, and so on, we write respectively
|A|, |B|, |V| to refer to its base set.
%$\ocompose$

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

Sometimes it's useful to specify that a change |dv| is valid for
a source |v| without naming |dv|'s destination, which is just |v
`oplus` dv|. So we give the following
\begin{definition}[One-sided validity]
We define relation |valid V v dv| as an abbreviation for
|fromto V v dv (v `oplus` dv)|.
\end{definition}

We use this definition right away:
\begin{lemma}[|`ocompose`| and |`oplus`| interact correctly]
  If |valid V v1 dv1| and |valid V (v1 `oplus` dv1) dv2| then
  |v1 `oplus` (ocompose dv1 v1 dv2) = v1 `oplus` dv1 `oplus` dv2|.
\end{lemma}
\begin{proof}
  We know that |`ocompose`| preserves validity, so under the
  hypotheses |valid V v1 dv1| and |valid V (v1 `oplus` dv1) dv2|
  we get that |dv = ocompose dv1 v1 dv2| is a valid change from
  |v1| to |v1 `oplus` dv1 `oplus` dv2|:
  \[|fromto V v1 (ocompose dv1
    v1 dv2) v1 `oplus` dv1 `oplus` dv2|.\]
  Hence, updating |dv|'s source |v1| with |dv|
  produces |dv|'s destination |v1 `oplus` dv1 `oplus` dv2|:
  \[|v1 `oplus` (ocompose dv1 v1 dv2) = v1 `oplus` dv1 `oplus`
    dv2|.\]
\end{proof}

% \begin{lemma}[|`ocompose`| and |`oplus`| interact correctly]
%   If |fromto V v1 dv1 v2| and |fromto V v2 dv2 v3| then |v1
%   `oplus` (ocompose dv1 v1 dv2) = v1 `oplus` dv1 `oplus` dv2|.
% \end{lemma}
% \begin{proof}
%   We know that |`ocompose`| preserves validity, so under the
%   hypotheses |fromto V v1 dv1 v2| and |fromto V v2 dv2 v3| we get
%   that |dv = ocompose dv1 v1 dv2| is a valid change from |v1| to
%   |v3| (|fromto V v1 (ocompose dv1 v1 dv2) v3|). Hence, updating
%   |dv|'s source |v1| with |dv| produces |dv|'s destination |v3|.
% \end{proof}

\subsection{Derivable operations}
\label{sec:chs-derivable-ops}
We can define |nilc| and |`ocompose`| in terms of other
operations, and prove they satisfy their requirements for change
structures.

\begin{code}
  nil v = v `ominus` v
  ocompose dv1 v1 dv2 = v1 `oplus` dv1 `oplus` dv2 `ominus` v1
\end{code}
\begin{lemma}
  If we define |nil v = v `ominus` v|, then |nilc| produces
  valid changes as required (|fromto V v (nil v) v|), for any
  change structure |chs(V)| and value |v : V|.
\end{lemma}
\begin{proof}
  This follows from validity of |`ominus`| (|fromto V v1 (v2
  `ominus` v1) v2|) instantiated with |v1 = v| and |v2 = v|.
\end{proof}
\begin{lemma}
  If we define |ocompose dv1 v1 dv2 = v1 `oplus` dv1 `oplus` dv2
  `ominus` v1|, then |`ocompose`| preserves validity as required,
  that is, if |fromto V v1 dv1 v2| and |fromto V v2 dv2 v3|
  then |fromto V v1 (ocompose dv1 v1 dv2) v3|.
\end{lemma}
\begin{proof}
  We need to show that |`ocompose`| preserves validity. So we can
  assume hypotheses |fromto V v1 dv1 v2| and |fromto V v2 dv2
  v3|. Since |`oplus`| agrees with validity, we have |v2 = v1 `oplus`
  dv1|, and |v3 = v2 `oplus` dv2 = v1 `oplus` dv1 `oplus` dv2|.

  Inlining |`ocompose`|'s definition and substituting |v3|, the
  thesis becomes that if then |fromto V v1 (v1 `oplus` dv1
  `oplus` dv2 `ominus` v1) (v1 `oplus` dv1 `oplus` dv2)|, which
  is true because |`ominus`| produces valid changes.
\end{proof}
\subsection{Defining new change structures from existing ones}
\label{sec:chs-fun-chs}

In this section, we derive a change structure for |A -> B| from
two change structures |chs(A)| and |chs(B)|. The change structure
for |A -> B| will enable defining a change structure for type
|sigma -> tau| in terms of change structures for |sigma| and
|tau|.

In \cref{sec:chs-product,sec:chs-sums} we will also define change
structures for |A `times` B| and |A + B|, for use in language
plugins for types |sigma `times` tau| and |sigma + tau|.

\begin{definition}[Change structure for |A -> B|]
  Given change structures |chs(A)| and |chs(B)| we define a
  change structure on their function space |A -> B|, written |chs(A) -> chs(B)|,
  where:
  \begin{subdefinition}
  \item The change set is defined as: |Dt^(A -> B) = A -> Dt^A -> Dt^B|.
  \item Validity is defined as
    \begin{multline*}
      |fromto (A -> B) f1 df f2 = forall a1 da a2 . (fromto A a1 da a2)| \\
      \text{ implies } |(fromto B (f1 a1) (df a1 da) (f2 a2))|.
    \end{multline*}
  \item We define change update by
    \[|f1 `oplus` df = \a -> f1 a `oplus` df a (nil a)|.\]
  \item We prove that |`oplus`| agrees with validity on |A -> B|.
    Consider |f1 , f2: A -> B| and |fromto (A -> B) f1 df f2|; we
    must show that |f1 `oplus` df = f2|. By functional
    extensionality, we only need prove that |(f1 `oplus` df) a =
    f2 a|, that is that |f1 a `oplus` df a (nil a) = f2 a|. Since
    |`oplus`| agrees with validity on |B|, we just need to show that
    |fromto B (f1 a) (df a (nil a)) (f2 a)|, which
    follows because |nil a| is a valid change from |a| to
    |a| and because |df| is a valid change from |f1| to |f2|.
  \item We define difference by \[|f2 `ominus` f1 = \a da -> f2 (a `oplus` da) `ominus` f1 a|.\]
  \item We prove that |`ominus`| produces valid changes on |A -> B|. Consider
    |df = f2 `ominus` f1| for |f1, f2: A -> B|. For any valid
    input |fromto A a1 da a2|, we must show that |df| produces a
    valid output with the correct vertexes, that is, that |fromto
    B (f1 a1) (df a1 da) (f2 a2)|. Since |`oplus`| agrees with
    validity, |a2| equals |a1 `oplus` da|. By substituting away
    |a2| and |df| the thesis becomes |fromto B (f1 a1) (f2 (a1
    `oplus` da) `ominus` f1 a1) (f2 (a1 `oplus` da))|, which is
    true because |`ominus`| produces valid changes on |B|.
  \item We define |nilc| through \[|nil f = f `ominus` f|,\] like in
    \cref{sec:chs-derivable-ops}, and reuse its generic
    correctness proof.
  \item We define change composition as \[|ocompose df1 f1 df2 =
    \a da -> ocompose (df1 a (nil a)) (f1 a) (df2 a da)|.\]
  \item We prove that change composition preserves validity on |A
    -> B|. That is, we must prove \[|fromto B (f1 a1) (ocompose
    (df1 a1 (nil a1)) (f1 a1) (df2 a1 da)) (f3 a2)|\] for every |f1,
    f2, f3, df1, df2, a1, da, a2| satifsfying |fromto (A -> B) f1
    df1 f2|, |fromto (A -> B) f2 df2 f3| and |fromto A a1 da a2|.

    Because change composition preserves validity on |B|, it's
    enough to prove that (1) |fromto B (f1 a1) (df1 a1 (nil a1))
    (f2 a1)| (2) |fromto B (f2 a1) (df2 a1 da) (f3 a2)|. That is,
    intuitively, we create a composite change using |`ocompose`|,
    and it goes from |f1 a1| to |f3 a2| passing through |f2 a1|.
    Part (1) follows because |df1| is a valid function change
    from |f1| to |f2|, applied to a valid change |nil a1| from
    |a1| to |a1|.\pg{}
    Part (2) follows because |df2| is a valid function change
    from |f2| to |f3|, applied to a valid change |da| from
    |a1| to |a2|.
  \end{subdefinition}
\end{definition}
%\paragraph{Aside}\pg{mention alternative definition of change composition?}

\subsection{Change structures for types and contexts}

As promised, given change structures for base types we can
provide change structures for all types:

\begin{restatable}[Change structures for base types]{requirement}{baseChs}
  For each base type |iota| we must have a change structure
  |chs(iota)| defined on base set |eval(iota)|, based on the
  basic change structures defined earlier.\pg{?}
  % including
  % |oplusIdx(iota) : iota -> Dt^iota -> iota|?
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
  defined earlier in \cref{def:bchs-types}.
\end{lemma}
\begin{proof}
  This can be verified by induction on types. For each case, it
  is sufficient to compare definitions.
\end{proof}
\validOplus
\begin{proof}
  This is required by the requirements of change structures on
  |chs(tau)|.
\end{proof}

As shortly proved in \cref{sec:correct-derive}, since |`oplus`|
agrees with validity (\cref{thm:valid-oplus}) and |derive(param)|
is correct (\cref{thm:derive-correct}) we get
\cref{thm:derive-correct-oplus}:

\deriveCorrectOplus

We can also define a change structure for environments. Each
change structure operation for environments acts
``variable-wise''. Recall that a typing context |Gamma| is a list
of variable assignment |x : tau|. For each such entry,
environments |rho| and environment changes |drho| contain a base
entry |x = v| where |v : eval(tau)|, and possibly a change |dx =
dv| where |dv : eval(Dt^tau)|.

% Each operation is defined componentwise

%format drho1
%format drho2

\pg{Some comment on how things are defined.}
\begin{definition}[Change structure for environments]
  \label{def:chs-envs}
  To each environment |Gamma| we associate a change structure
  |chs(Gamma)|, that extends the basic change structure from \cref{def:bchs-contexts}.
  Operations are defined as follows.
\begin{code}
  emptyRho `oplus` emptyRho                                                       = emptyRho
  (rho, x = v) `oplus` (drho, x = v', dx = dv)                                    = (rho `oplus` drho, x = v `oplus` dv)

  emptyRho `ominus` emptyRho                                                      = emptyRho
  (rho2, x = v2) `ominus` (rho1, x = v1)                                          = (rho2 `ominus` rho1, x = v1, dx = v2 `ominus` v1)

  nil emptyRho                                                                    = emptyRho
  nil (rho, x = v)                                                                = (nil rho, x = v, dx = nil v)

  ocompose emptyRho emptyRho emptyRho                                             = emptyRho
  ocompose ((drho1, x = v1, dx = dv1)) (rho, x = v1) ((drho2, x = v2, dx = dv2))  =
      (ocompose drho1 rho drho2, x = v1, dx = ocompose dv1 v1 dv2)
\end{code}
\end{definition}

Base values in environment changes are redundant. When consuming
an environment change, they are never consumed. When producing an
environment change, they are created to ensure validity of the
resulting environment change.

The needed proofs can be done component-wise. We omit them here
because they are very tedious to read. We will show similar
proofs when introducing change structures for product types |A
`times` B| in \cref{def:chs-prod}.

%%%%
% What's below must be revised.
%%%%

% To prove that |`oplus`| agrees with validity in general
% (\cref{thm:valid-oplus}), we must require definitions from
% plugins to satisfy this theorem on base types:
% \begin{restatable}[|`oplus`| agrees with validity on base types]{requirement}{baseValidOplus}
%   \label{req:base-valid-oplus}
%   If\\ |fromto iota v1 dv v2| then |v1 `oplus` dv = v2|.
% \end{restatable}

% \begin{definition}
%   For each type |tau| we define operators |oplusIdx(tau) : tau ->
%   Dt^tau -> tau|, |ominusIdx(tau) : tau -> tau -> Dt^tau|.
% \end{definition}

% We define then |`oplus`|, |nilc| and |`ominus`| on function spaces:
% \begin{code}
%   nil v = v `ominus` v
%   f1 (oplusIdx(A -> B)) df = \v -> f1 v `oplus` df v (nil v)
%   f2 (ominusIdx(A -> B)) f1 = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
% \end{code}

% In particular, when |A -> B = eval(sigma) -> eval(tau)|, it follows that
% \begin{code}
%   f1 (oplusIdx(sigma -> tau)) df = \v -> f1 v `oplus` df v (nil v)
%   f2 (ominusIdx(sigma -> tau)) f1 = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
% \end{code}

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


We only need |`ominus`| to be able to define nil changes on
arbitrary functions |f : eval(sigma -> tau)|.

However, as anticipated earlier, if |f| is the semantics of a
well-typed term |t|, that is |f = eval(t) emptyRho|, we can
define the nil change of |f| through its derivative.\pg{See
  before}
% no, we need full abstraction, unless the term is closed.

\pg{figure}
% \NewDocumentCommand{\RightFramedSignatureML}{m}
% {\vbox{\hfill\fbox{\(
%         #1
% \)
%     }}}

As a summary of definitions on types, we show that:
\begin{figure}
  \pg{change structures}
  \[|nil v = v `ominus` v |\]
\begin{subfigure}[c]{0.6\textwidth}
  \RightFramedSignature{|oplusIdx(A): A -> Dt^A -> A|}
  \RightFramedSignature{|ominusIdx(A): A -> A -> Dt^A|}
\begin{code}
  f1 (oplusIdx(A -> B)) df = \v -> f1 v `oplus` df v (nil v)
  f2 (ominusIdx(A -> B)) f1 = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
\end{code}
\caption{Change structures for function spaces}
\end{subfigure}
\begin{subfigure}[c]{0.6\textwidth}
  \RightFramedSignature{|oplusIdx(tau): eval(tau -> Dt^tau -> tau)|}
  \RightFramedSignature{|ominusIdx(tau): eval(tau -> tau -> Dt^tau)|}
\begin{code}
  f1 (oplusIdx(sigma -> tau))   df = \v -> f1 v `oplus` df v (nil v)
  v1 (oplusIdx iota)            dv = ...
  f2 (ominusIdx(sigma -> tau))  f1 = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
  v2 (ominusIdx iota)           v1 = ...
\end{code}
\caption{|`oplus`| and |`ominus`| on semantic domains}
\end{subfigure}
\begin{subfigure}[c]{0.7\textwidth}
  \RightFramedSignature{|oplusIdx(Gamma): eval(Gamma -> Dt^Gamma -> Gamma)|}
  \RightFramedSignature{|ominusIdx(Gamma): eval(Gamma -> Gamma -> Dt^Gamma)|}
\begin{code}
  emptyRho `oplus` emptyRho                    = emptyRho
  (rho, x = v) `oplus` (drho, x = v, dx = dv)  = (rho `oplus` drho, x = v `oplus` dv)
  emptyRho `ominus` emptyRho                   = emptyRho
  (rho2, x = v2) `ominus` (rho1, x = v1)       = (rho2 `ominus` rho1, x = v1, dx = v2 `ominus` v1)
\end{code}
  % nil emptyRho = emptyRho
  % nil (rho, x = v) = nil rho, x = v, dx = nil v
\caption{|`oplus`| and |`ominus`| on environments}
\end{subfigure}
\validOplus*
  \deriveCorrectOplus*
  \nilChangesExist*

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
%   v1 `oplus` (ocompose dv1 v1 dv2) = v1 `oplus` dv1 `oplus` dv2
% \end{code}
% Later, once we define a suitable equivalence relation |`doe`| on
% changes, we'll also be able to state a few further algebraic laws:
% \begin{code}
%   nil v1 `doe` v1 `ominus` v1
%   (v1 `oplus` dv) `ominus` v1 `doe` dv
%   ocompose dv1 v1 dv2 = v1 `oplus` dv1 `oplus` dv2 `ominus` v1
% \end{code}

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
%   `ocompose` : (v1 : V) -> {v2 v3 : V} -> (dv1 : Dt2 v1 v2) -> (dv2 : Dt2 v2 v3) -> Dt2 v1 v3
% \end{code}

\subsection{Equivalent definitions of change validity}
\pg{Correct the claim of equivalence, that's not quite true I
  think.}

In this section we compare our \emph{new-style} formalization
with the one we and others used in our \emph{old-style}
formalization, that is, our first formalization of change
theory~\citep{CaiEtAl2014ILC}. In particular, we focus on change
validity for function spaces, and its role in the overall proof
of |derive(param)|'s correctness. Specifically, we compare
new-style valid function changes to old-style ones, and sketch in
which sense they are equivalent.

Let's assume |fromto (A -> B) f1 df f2| and |fromto A a1 da
a2|. We know that then |fromto B (f1 a1) (df a1 da) (f2
a2)|.

We have seen in \cref{eq:fun-preserv-eq} that |f2 a2 = f1 a1
`oplus` df a1 da|, and we have defined |(f1 `oplus` df) a1 = f1
a1 `oplus` df a1 (nil a)|.

Combining these two equations, it follows that
\[
  |f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da) = f1
  (a1 `oplus` da) `oplus` df (a1 `oplus` da) (nil (a1 `oplus`
  da))|.\]
%
This equation is one requirement that old-style function changes
had to satisfy. What we have seen is that the new-style
definition of validity, although different (and we believe
simpler), implies the same equation.

Old-style valid function changes also had to map a valid change
|da| with source |a1| to a valid change |df a1 da| with source
|f1 a1|. New-style function changes also satisfy this
requirement.

This suggests the two definitions should be equivalent. However,
new-style function changes are also defined on invalid input
changes, unlike old-style valid function changes.
However, we can
fix this issue by restricting the input domain of function
changes to valid changes. Indeed, we believe that sets of valid
new-style function changes, restricted this way, are isomorphic
to sets of old-style function changes, but only as long as we
stick to the on-paper old-style formalization, presented in set
theory.

However, the actual mechanized proofs use type theory, where
proofs have first-class status. Old-style changes embed proofs of
their own validity, while new-style changes don't. Moreover, a
change |dv| for source |v| has type |Dt^v|, which can only be
expressed using dependent types.
%
While that formulation has lots of conceptual elegance, programs
produced by |derive(param)| are expressed in STLC, which does not
support dependent types and cannot express proofs; hence
|derive(param)| cannot produce changes that are valid according
to \citeauthor{CaiEtAl2014ILC}. Instead,
\citeauthor{CaiEtAl2014ILC} need to give a separate semantics
mapping terms to their validity-embedding changes, and then
relate validity-embedding changes to the ``erased changes''
produced by |derive(param)|.\footnote{While we didn't realize
  back then, we could have probably reused the theory of
  realizability to perform erasure and extract the computational
  content from validity-embedding changes.} While this additional
step is not conceptually hard, mechanizing it took significant
work; moreover, dealing with both validity-embedding changes and
erased changes introduced significant inelegant noise in quite a
few definitions and theorem statements.

Using our formalization, we have also defined a type of
validity-embedding changes |Dt^v|, with elements that pair a
change and its validity proof:
\[|Dt^v = Sigma [ dv `elem` Dt^V ] valid v dv|.\]

However, such new-style validity-embedding changes are not
equivalent to old-style changes on function spaces, even if we
restrict our attention to valid inputs; we need one last step to
relate them together. Take an arbitrary function |f1 : A -> B|.
For \citeauthor{CaiEtAl2014ILC}, |df' : Dt^f1| means that |df'|
maps validity-embedding changes to validity-embedding changes;
for us, |df' : Dt^f1| means that |df'| contains (1) a map |df|
from changes to changes and (2) a proof that |df| preserves
validity: in a sense, new-style changes split what was a map of
validity-embedding changes into its action on changes and its
action on validity proofs. This ``splitting'' becomes trickier
for higher-order function types, such as |(A -> B) -> (C -> D)|,
so it must be defined by induction on types; essentially, we need
to adapt \citeauthor{CaiEtAl2014ILC}'s erasure.

We have not attempted a mechanization of the full equivalence,
but we have been satisfied with mechanizing several fragments
without further issues.

\paragraph{Mechanization overhead}
The formalization presented in this thesis appears simpler and
smaller than the original one, because we avoid needing erasure,
but also for other smaller simplifications.

Most importantly, our fundamental relation is ``two-sided''
(|fromto V v1 dv v2|) rather than ``one-sided'' (|valid V v dv|);
that is, validity specifies both the source and the destination
explicitly. This is easier now that validity proofs are separate
from changes. While this might seem trivial, it's somewhat
significant for functions.
%
Indeed, new-style validity allows stating that |df : Dt^(A -> B)|
is a change from |f1| to |f2|, instead of stating that |df| is a
change from |f1| to |f1 `oplus` df = \a -> f1 a `oplus` df a (nil
a)|. What's more, assume |fromto A a1 da a2|: according to
new-style validity preservation, change |df a1 da| has
destination |f2 a2|. Instead, according to old-style validity
preservation, change |df a1 da| has destination |(f1 `oplus` df)
(a1 `oplus` da)|, that is |f1 (a1 `oplus` da) `oplus` df (a1
`oplus` da) (nil (a1 `oplus` da))|, which adds significant noise
to mechanized proving with old-style definitions.

\paragraph{Credits and related work}
The proof presented in this chapter is an evolution of the
original one by \citet{CaiEtAl2014ILC}.
%
While this formalization and the mechanization are both original
with this thesis, some ideas were suggested by other
(currently-unpublished) developments by Yufei Cai and by Yann
Régis-Gianas. Yufei Cai showed a simpler set-theoretic proof by
separating validity, while we noticed separating validity works
equally well in a mechanized type theory and simplifies the
mechanization. Yann Régis-Gianas has an almost complete proof
using a two-sided validity relation that simplified the proof
significantly. Since his proof was about an untyped
$\lambda$-calculus, the proof uses a step-indexed logical
relation to define validity, a necessary choice which however
adds nontrivial overhead. That proof also uses step-indexed
big-step semantics; because of this choice, mechanizing the proof
would be harder in Agda, since Agda has limited support for proof
automation compared to Coq.
%
I gave the first complete and mechanized ILC correctness proof
using two-sided validity, again for a simply-typed
$\lambda$-calculus with a denotational semantics. Based on
two-sided validity, I also reconstructed the rest of the theory
of changes.

% For \citeauthor{CaiEtAl2014ILC}, function changes map
% validity-embedding changes to validity-embedding changes: a
% function change |df' : Dt^f| has type |(a : A) -> (da : Dt^a) ->
% Dt^(f1 a)|.

% Instead, with our definition, if |df' : Dt^f1| then |df'| pairs a
% function change |df : Dt^(A -> B)| (that is, |A -> Dt^A -> Dt^B|)
% and a proof of validity preservation, that
% |(a1 a2 : A) -> (da : Dt^A) -> fromto A a1 da a2 -> fromto B (f1 a1) (df a1 da) (f2 a2)| (with |f2 = f1 `oplus` df|).
% This is equivalent to
% |(a : A) -> (da : Dt^A) -> valid A a da -> valid B (f1 a) (df a da)|.


% when they write |df a1 da|, change |da| is in fact a pair of an
% ``actual change'' and its validity proof. Similarly, |df a1 da|
% is also a pair of an ``actual change'' and a validity proof. For
% that reason, to relate valid changes with

% %
% We defined |evalInc t = (\rho1 drho -> eval(derive t) drho)|
% essentially as the semantics of |derive(t)|; function
% |evalInc(t)| is only a valid function change in our
% formalization, but not in \citeauthor{CaiEtAl2014ILC}'s. More in
% general, in that earlier formalization the semantics of a lambda
% term is almost never be a valid change.
% There, one must define a
% separate incremental semantics that is a valid function change
% and that \emph{erases} to |eval(derive t)|. That's because in
% \citeauthor{CaiEtAl2014ILC} the input to function changes embeds
% validity proofs, while for us it doesn't.

% While this difference is conceptually innocuous, it
% makes the earlier proof trickier than ours.

% In our mechanization, we treat changes |dv : Dt^V| and their
% proofs of validity |dvv : valid V v dv| as two separate objects,
% while \citeauthor{CaiEtAl2014ILC} combine them. For
% \citeauthor{CaiEtAl2014ILC}, instead, changes belong to change
% sets |Dt^v| indexed by the source |v|, and each change in |Dt^v|
% contains a proof that it's valid for |v|.

% \citeauthor{CaiEtAl2014ILC}'s definition resembles our definition
% of |Dt^v = Sigma [ dv `elem` Dt V ] valid v dv| in
% \cref{sec:chs-alg}; indeed, for any natural |n : Nat| the two
% definitions of |Dt^n| are the same.

% But on function spaces the two definitions diverge.
% Take |f1 : A -> B|.

% For us, |Dt^f| pairs a ``raw'' function change with a proof of
% its validity: |Dt^f = Sigma [ df `elem` Dt^(A -> B) ] valid (A ->
% B) f df|, where |valid (A -> B) f df| means that |df| preserves
% validity, taking a valid change |da| (|fromto A a1 da a2|) to a
% valid change |df a1 da| (|fromto B (f1 a1) (df a1 da) ((f1
% `oplus` df) a2)|).
%

% % Instead, for \citeauthor{CaiEtAl2014ILC}, function changes map
% % validity-embedding changes to validity-embedding changes: a
% % function change |df : Dt^f| has type |(a1 : A) -> (da : Dt^a1) ->
% % Dt^(f a1)|.

% % when they write |df a1 da|, change |da| is in fact a pair of an
% % ``actual change'' and its validity proof. Similarly, |df a1 da|
% % is also a pair of an ``actual change'' and a validity proof. For
% % that reason, to relate valid changes with

% Remember |valid (A -> B) f df = fromto (A -> B) f df (f `oplus` df) = forall |
% that is:
% \[|Dt^f = Sigma [ df `elem` A -> Dt^A -> Dt^B ] (forall (a1 : A) ())|\]

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
% |eval(derive(t))| must take environment |rho| and a \emph{change environment}
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
% |eval(derive(t))| takes a base environment |rho1| and a change environment
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

\section{Based changes}
\pg{We can study }

\section{Change equivalence}
\label{sec:change-equivalence}
\pg{We can use based changes.}

Next, we define an equivalence relation on changes, that
describes when two changes |dv1, dv2| can be substituted for one
another.

\begin{definition}[Change equivalence]
  Two changes |dv1|, |dv2| are equivalent if and only if there
  exists |v1, v2| such that both |dv1| and |dv2| are valid from
  |v1| to |v2|.
\end{definition}

Change equivalence is respected by all validity-preserving
operations, such as valid function changes |df|.

Viceversa, two function changes that map equivalent sources to
equivalent destinations are also equivalent.

\pg{Hm. Do the theorems we want work with this definition?}

Earlier we have sometimes written that two changes are equal.
However, that's often too restrictive.

\section{The relation with parametricity and the abstraction theorem}

In this section we discuss similarities between correctness of |derive(param)|
(\cref{thm:derive-correct}) and the fundamental theorem of logical relations,
for the case of binary logical relations. This section is intended for logical
relation experts, and we keep it rather informal.

%format p(t) = "\mathcal{P}(" t ")"

Most studies of logical relations mention no term transformation that relates to
|derive(param)|; one exception is given by \citet{Bernardy2011realizability}.
They study relational parametricity, a particular binary logical relation, where
the fundamental theorem of logical relations becomes the abstraction theorem. To
prove the abstraction theorem, \citeauthor{Bernardy2011realizability} present a
term transformation |p(param)|; we'll show the analogy between this term
transformation and
|derive(param)|.%
%
\footnote{\citeauthor{Bernardy2011realizability} were not the first to introduce
  such a transformation, but we base our comparison off their presentation and
  avoid discussing their related work.}

Transformation |p(t)| takes a term |t| to a proof term |p(t)| in a suitable
object logic (related to the one of |t|), that proves that |t| maps logically
related inputs to logically related outputs. For binary logical relations and
simply-typed $\lambda$-calculus, we can specialize their definition to the
following:

%format (idx1 (t)) = "\mathcal{S}_1(" t ")"
%format (idx2 (t)) = "\mathcal{S}_2(" t ")"

\begin{code}
  (t1, t2) `elem` r(sigma -> tau) =
    forall x1 x2 : sigma, px : (x1, x2) `elem` r(sigma). (t1 x1, t2 x2) `elem` r(tau)
  p(x) =
      px
  p(\(x : sigma) -> t) =
    \(x1 x2 : sigma) (px : (x1, x2) `elem` r(sigma)) -> p(t)
  p(s t) =
    p(s) (idx1 s) (idx2 s) p(t)
\end{code}

where |idx1 s| and |idx2 s| subscript variables in terms with 1 and 2:
\begin{code}
  idx1(x) = x1
  idx1(\(x : sigma) -> t) = \(x1 : sigma) -> idx1 t
  idx1(s t) = (idx1 s) (idx1 t)

  idx2(x) = x2
  idx2(\(x : sigma) -> t) = \(x2 : sigma) -> idx2 t
  idx2(s t) = (idx2 s) (idx2 t)
\end{code}

To see the analogy, let's show a variant of differentiation. This time,
|derive(\x -> t) = \x1 x2 dx -> derive(t)| is a function that binds not just the
source of |dx|, but also its target, and the additional symmetry simplifies its
theoretical study.

\begin{code}
  Dt2 : (v1 v2 : V)
  Dt2 : (v1 v2 : V) -> Set
  Dt2 v1 v2 = Sigma [ dv `elem` Dt^V ] (fromto sigma v1 dv v2)
  (f1, df, f2) `elem` r(sigma -> tau) =
    forall x1, dx, x2 : sigma, dxx : r(sigma) . (f1 x1, df x1 x2 dx, f2 x2) `elem` r(tau)

  derive(x) = dx
  derive(\(x : sigma) -> t) = \x1 x2 (dx : Dt2 x1 x2) -> derive(t)
  derive(s t) = derive(s) (idx1 s) (idx2 s) (derive t)

  derive(\(x : sigma) -> t) = \x1 x2 (fromto sigma x1 dx x2) -> derive(t)
\end{code}

\pg{connection}
For readers familiar with staging,
we explain how \citeauthor{Bernardy2011realizability}'s
transformation relates to standard proofs of the abstraction theorem.
In short, (a) the usual proof of the abstraction theorem
can be regarded as an \emph{interpreter} from object-level terms to metalevel
proofs; (b) standard interpreters can be turned into compilers by staging, so
that they evaluate object-level code for a function instead of the function
itself at the metalevel; (c) an ``interpreter'' that produces a metalevel proof
can be staged into a ``compiler'' (or term transformation) into an object-level
proof term in a suitable logic; (d) the above definition of |p(t)| corresponds
(informally) to staging the proof of the abstraction theorem.
\begin{enumerate}
\item Recall that the abstraction theorem is proven by
induction on terms.\footnote{Or on typing derivations, but as discussed we
  regard the two as isomorphic, since typing is syntax-directed.} Let's write
|P(t)| to say that term |t| satisfies the abstraction theorem; then the theorem
statement is |forall t. P(t)| in the metalevel logic. The proof is constructive,
so we can regard it (informally) under the lens of the Curry-Howard isomorphism.
Under this lens, a metalevel proof of |forall t. P (t)| is a function from terms
|t| to a metalevel proof of |P(t)|; a proof by induction is a structurally
recursive function from terms to metalevel proofs, just like an interpreter is a
structural recursive function from terms to metalevel functions. Hence, we
regard the proof of the abstraction theorem as an interpreter.
\item Staging an interpreter produces a compiler, which evaluates
  not to a value |v| but to code that will later evaluate to
  value |v|; this code will already be specialized for the input
  term.
\item Similarly, by staging an interpreter that produces proofs,
  we produce a compiler from term to proofs.
\end{enumerate}

% Most other proofs,
% instead of creating a proof term, but simply produce a similar proof in the meta
% logic by induction on terms. The two proof strategies are related by an analogue
% of staging.


% Here we discuss the relation with parametricity, the abstraction theorem, and
% the fundamental theorem of logical relations, for readers familiar with these
% topics. Parametricity is typically studied for type systems containing System F,
% but \citet{Bernardy2011realizability} generalize it to arbitrary PTSs.



% Correctness of |derive(param)| (\cref{thm:derive-correct}) relates to binary
% parametricity. However, usual statements of binary parametricity mention no
% analog of changes or |derive(param)|. One defines a relational interpretation of
% terms, mapping input relations to output relations, and shows this maps


\chapter{Language plugins for products and sums}
\label{ch:prod-sums}

In this section, we show language plugins for sum and product
types.

\pg{Extend by showing the base semantics of these plugins.}
We give ways to give change structures for products and sums.
As primitives, we use the introduction and elimination forms for
these types. Then, we show how to obtain derivatives for these
primitives.

\pg{Consider recursive types, and recursion?}
\section{A change structure for products}
\label{sec:chs-product}
We can define change structures on products |A `times` B|, given
change structures on |A| and |B|: a change on pairs is just a
pair of changes; all other change structure definitions
distribute componentwise the same way, and their correctness
reduce to the correctness on components. Since all these proofs
are similar, spelling out their details does not make them
clearer, we only give the first such proof in full.

\begin{definition}[Change structure for |A `times` B|]
  \label{def:chs-prod}
  Given change structures |chs(A)| and |chs(B)| we define a
  change structure on their product |chs(A `times` B)|, that we
  also write |chs(A) `times` chs(B)|.
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
  \item We define difference by
    \[|(a2, b2) `ominus` (a1, b1) = (a2 `ominus` a1, b2 `ominus` b1)|.\]
  \item |`ominus`| produces valid changes on |A `times` B|
    because |`ominus`| produces valid changes on both |A| and
    |B|. We omit a full proof; the key step reduces the thesis
    \[|fromto (A `times` B) ((a1, b1)) ((a2, b2) `ominus` (a1, b1))
    ((a2, b2))|\] to |fromto A a1 (a2 `ominus` a1) a2| and |fromto
    B b1 (b2 `ominus` b1) b2| (where free variables range on
    suitable domains).
  \item We define |nilc| to distribute componentwise:
    \[|nil (a, b) = (nil a, nil b)|.\]
  \item |nil (a, b)| is correct, that is |fromto (A `times` B)
    ((a, b)) ((nil a, nil b)) ((a, b))|, because |nilc| is
    correct on each component.
  \item We define change composition to distribute componentwise:
    \[|ocompose ((da1, db1)) ((a1, b1)) ((da2, db2)) =
    (ocompose da1 a1 da2, ocompose db1 b1 db2)|.\]
  \item Change composition is correct on |A `times` B|, that is
    \[|fromto (A `times` B) ((a1, b1)) ((ocompose da1 a1 da2,
      ocompose db1 b1 db2)) ((a3, b3))|\] if |fromto (A `times` B)
    ((a1, b1)) ((da1, db1)) ((a2, b2))| and |fromto (A `times` B)
    ((a2, b2)) ((da2, db2)) ((a3, b3))|, because change composition is correct on
    both |A| and |B|.
  \end{subdefinition}
\end{definition}

\section{A change structure for sums}
\label{sec:chs-sums}
We can define change structures on products |A + B|, given change
structures on |A| and |B|.
\pg{resume.}


% Missing sections from chap-intro-incr.lhs.

\chapter{Misc}

\section{A higher-order example}
\label{sec:differentiation-fold-example}
\pg{write}
% Referenced later in sec-performance.tex by saying:
% % We have seen in \cref{ssec:differentiation} that $\Derivative$
% % needlessly recomputes $\Merge\Xs\Ys$. However, the result is a
% % base input to $\FOLD'$.

\section{Nontermination}
\label{sec:non-termination}
\pg{write, and put somewhere}
