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
  \label{thm:correct-derive-2}
  If |Gamma /- t : tau|, then |evalInc(t)| is a valid change from
  |eval t| to |eval t|:
  \[
    |fromto (eval Gamma -> eval tau) (eval t) (evalInc t) (eval t)|
  \]
\end{theorem}

\begin{proof}
  By expanding \cref{def:basic-change-structure-funs,def:inc-semantics}
  one can verify this is just a restatement of \cref{thm:correct-derive}.
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
\item We have seen in \cref{thm:correct-derive-2} that, whenever
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
Next, we will introduce formally operators |`oplus`|, |`ominus`|
and |nilc| and relate them to validity. In particular, we will
prove that |fromto tau v1 dv v2| implies |v1 `oplus` dv = v2|,
and explain why the converse is not true.

\pg{resume, turn into figure}
\begin{restatable}[Base definitions of |`oplus`|]{requirement}{baseOplus}
  \label{req:base-oplus}
  For each base type |iota| we have a definition of
  |oplusIdx(iota) : iota -> Dt^iota -> iota|.
\end{restatable}

To prove that |`oplus`| agrees with validity in general
(\cref{thm:valid-oplus}), we must require definitions from
plugins to satisfy this theorem on base types:
\begin{restatable}[|`oplus`| agrees with validity on base types]{requirement}{baseValidOplus}
  \label{req:base-valid-oplus}
  If\\ |fromto iota v1 dv v2| then |v1 `oplus` dv = v2|.
\end{restatable}

\begin{definition}
  For each type |tau| we define operators |oplusIdx(tau) : tau ->
  Dt^tau -> tau|, |ominusIdx(tau) : tau -> tau -> Dt^tau|.
\end{definition}

We define then |`oplus`|, |nilc| and |`ominus`| on function spaces:
\begin{code}
  nil v = v `ominus` v
  f1 (oplusIdx(A -> B)) df = \v -> f1 v `oplus` df v (nil v)
  f2 (ominusIdx(A -> B)) f1 = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
\end{code}

In particular, when |A -> B = eval(sigma) -> eval(tau)|, it follows that
\begin{code}
  f1 (oplusIdx(sigma -> tau)) df = \v -> f1 v `oplus` df v (nil v)
  f2 (ominusIdx(sigma -> tau)) f1 = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
\end{code}

\pg{Both change structure requirements, theorems on types}
\begin{restatable}[|`ominus`| produces valid changes]{lemma}{validOminus}
  \label{thm:valid-ominus}
  |`ominus`| produces valid changes, that is |fromto tau v1 (v2
  `ominus` v1) v2| and |v1 `oplus` (v2 `ominus` v1) = v2| for any
  type |tau| and any |v1, v2 : eval(tau)|.
\end{restatable}
\validOplus*
\begin{proof}\pg{?}
\end{proof}
\begin{restatable}[|`ominus`| inverts |`oplus`|]{lemma}{oplusOminus}
  For any type |tau| and any values |v1, v2 : eval(tau)|,
  |`oplus`| inverts |`ominus`|, that is |v1 `oplus` (v2 `ominus`
  v1) = v2|.
\end{restatable}
\begin{proof}
  From \cref{thm:valid-ominus,thm:valid-oplus}.
\end{proof}
\deriveCorrectOplus*
The proof came earlier.
\nilChangesExist*
\begin{proof}\pg{?}
\end{proof}


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
