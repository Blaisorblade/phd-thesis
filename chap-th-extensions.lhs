% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Extensions and theoretical discussion}
\label{ch:misc-extensions}
In this \lcnamecref{ch:misc-extensions} we collect discussion of a few
additional topics related to ILC that do not suffice for standalone chapters.
We
show how to differentiation general recursion~\cref{sec:general-recursion}, we
exhibit a function change that is not valid for any function
(\cref{sec:very-invalid}), we contrast our representation of function changes
with \emph{pointwise} function changes (\cref{ssec:pointwise-changes}), and we
compare our formalization with the one presented in \citep{CaiEtAl2014ILC}
(\cref{sec:alt-change-validity}).

\section{General recursion}
\label{sec:general-recursion}
This section discusses informally how to differentiate terms
using general recursion and what is the behavior of the resulting terms.

\subsection{Differentiating general recursion}
%format letrec = "\mathbf{letrec}"
%format fix = "\mathbf{fix}"

Earlier we gave a rule for differentiating (non-recursive) |lett|:
\begin{code}
derive(lett x = t1 in t2)   =  lett  x   = t1
                                     dx  = derive(t1)
                               in    derive(t2)
\end{code}
% derive(lett x = t1 in t2) =
%   lett  x = t1
%         dx = derive(t1)
%   in    derive(t2)
It turns out that we can use the same rule also for recursive
|lett|-bindings, which we write here (and only here) |letrec| for emphasis:
\begin{code}
derive(letrec x = t1 in t2)   =  letrec  x   = t1
                                         dx  = derive(t1)
                                 in      derive(t2)
\end{code}
% derive(letrec x = t1 in t2) =
%   letrec  x = t1
%           dx = derive(t1)
%   in      derive(t2)

\pg{Far from perfect. Better reorganize. This order makes little sense.}
\begin{example}
  In \cref{ex:syn-changes-map} we presented a derivative |dmap| for
  |map|. By using rules for differentiating recursive functions, we obtain
  |dmap| as presented from |map|:
% \begin{code}
% map f = fix go
%   where
%     go self Nil = Nil
%     go self (Cons x xs) = Cons (f x) (self xs)
% \end{code}

% Applying the derivation rules, we get that
% |dmap f df = fix ((derive go) (fix go))|,
% and since |fix go = map f| we can write:
% \begin{code}
% dmap f df = fix (dgo (map f))
%   where
%     dgo self dself Nil Nil = Nil
%     dgo self dself (Cons x xs) (Cons dx dxs) =
%       Cons (df x dx) (dself xs dxs)
% \end{code}
\begin{code}
dmap f df Nil Nil = Nil
dmap f df (Cons x xs) (Cons dx dxs) =
  Cons (df x dx) (dmap f df xs dxs)
\end{code}
\end{example}

However, derivative |dmap| is not asymptotically faster than |map|. Even when we
consider less trivial change structures, derivatives of recursive functions
produced using this rule are often not asymptotically faster.
Deriving |letrec x = t1 in t2| can still be useful if |derive t1|
and/or |derive t2| is faster than its base term, but during our work we focus
mostly on using structural recursion. Alternatively, in \cref{ch:diff-examples}
and \cref{sec:plugin-design} we have shown how to incrementalize functions
(including recursive ones) using equational reasoning.

In general, when we invoke |dmap| on a change |dxs| from |xs1| to |xs2|, it is
important that |xs1| and |xs2| are similar enough that enough computation can be
reused. Say that |xs1 = Cons 2 (Cons 3 (Cons 4 Nil))| and |xs2 = Cons 1 (Cons 2
(Cons 3 (Cons 4 Nil)))|: in this case, a change modifying each element of |xs1|,
and then replacing |Nil| by |Cons 4 Nil|, would be inefficient to process, and
naive incrementalization would produce this scenario. In this case, it is clear
that a preferable change should simply insert |1| at the beginning of the list,
as illustrated in \cref{sec:incr-fold} (though we have omitted the
straightforward definition of |dmap| for such a change structure).
In approaches like self-adjusting computation, this is ensured by using
memoization. In our approach, instead, we rely on changes that are nil or small
to detect when a derivative can reuse input computation.

The same problem affects naive attempts to incrementalize, for instance, a
simple factorial function; we omit details. Because of these issues, we focus on
incrementalization of structurally recursive functions, and on incrementalizing
generally recursive primitives using equational reasoning.
We return to this issue in \cref{ch:incr-conclusion-futwork}.

\subsection{Justification}
Here, we justify informally the rule for differentiating recursive functions
using fixpoint operators.

Let's consider STLC extended with a family of standard fixpoint
combinators $\Varid{fix}_{|tau|}|: (tau -> tau) -> tau|$, with
|fix|-reduction defined by equation |fix f -> f (fix f)|; we
search for a definition of |derive (fix f)|.

Using informal equational reasoning, if a correct definition of
|derive (fix f)| exists, it must satisfy
\begin{code}
  derive (fix f) `cong` fix ((derive f (fix f)))
\end{code}

We can proceed as follows:
% We recall that the derivative of a closed term is its nil change.
\begin{equational}
\begin{code}
   derive (fix f)
=  {- imposing that |derive| respects |fix|-reduction here -}
   derive (f (fix f))
=  {- using rules for |derive| on application -}
   (derive f) (fix f) (derive (fix f))
\end{code}
\end{equational}

This is a recursive equation in |derive (fix f)|, so we can try
to solve it using |fix| itself:
\begin{code}
  derive (fix f) = fix (\dfixf -> (derive f (fix f) dfixf))
\end{code}

Indeed, this rule gives a correct derivative.
Formalizing our reasoning using denotational semantics would presumably require
the use of domain theory.
Instead, we prove correct a variant of |fix| in \cref{ch:bsos}, but using
operational semantics.

% In particular
% \begin{code}
%    derive (fix (\ff -> t))
% =
%    fix (\dff -> (derive (\ff -> t) (fix (\ff -> t)) dff))
% =
%    fix (\dff -> derive t [ff := fix (\ff -> t)])
% \end{code}

% % |let ffact = fix (\ffact n -> n * ffact (n - 1)) in t2 =
% % letrec ffact = \n -> n * ffact (n - 1) in t2|
% % |
% % This rule is equivalent

% We can also derive the rule for |letrec|, based on this rewrite rule:
% |let ff = fix (\ff -> t) in t2 = letrec ff = t in t2|.
% We proceed as follows:
% \begin{equational}
% \begin{code}
%    derive(letrec ff = t in t2)
% =  {- -}
%    derive(lett ff = fix (\ff -> t) in t2)
% =  {- deriving |let| -}
%    let
%      ff   = fix (\ff -> t)
%      dff  = derive (fix (\ff -> t))
%    in derive t2
% =  {- deriving |fix| -}
%    let
%      ff   = fix (\ff -> t)
%      dff  = fix (\dff -> derive t [ff := (fix (\ff -> t))])
%    in derive t2
% =  {- deinline binding of |ff| -}
%    let
%      ff   = fix (\ff -> t)
%      dff  = fix (\dff -> derive t)
%    in derive t2
% =  {- |let| to |letrec| -}
%    letrec
%      ff   = t
%    in let
%      dff  = fix (\dff -> derive t)
%    in derive t2
% =  {- |let| to |letrec| -}
%    letrec
%      ff   = t
%      dff  = derive t
%    in derive t2
% \end{code}
% \end{equational}

\section{Completely invalid changes}
\label{sec:very-invalid}
\pg{Not sure that the reference to sec;invalid should go here. Ok, probably not.}
In some change sets, some changes might not be valid relative to
any source. In particular, we can construct examples in |Dt^(Int
-> Int)|.

To understand why this is plausible, we recall that as described
in \cref{ssec:pointwise-changes}, |df| can be decomposed into a
derivative, and a pointwise function change that is independent
of |da|. While pointwise changes can be defined arbitrarily, the
behavior of the derivative of |f| on changes is determined by the
behavior of |f|.

\begin{example}
  We search for a function change |df : Dt^(Int -> Int)| such
that there exist no |f1, f2: Int -> Int| for which
|fromto (Int -> Int) f1 df f2|. To find |df|, we assume that there are |f1, f2| such that |fromto
(Int -> Int) f1 df f2|, prove a few consequences, and construct
|df| that cannot satisfy them. Alternatively, we could pick the
desired definition for |df| right away, and prove by
contradiction that there exist no |f1, f2| such that |fromto (Int -> Int) f1 df
f2|.

Recall that on integers |a1 `oplus` da = a1 + da|, and that
|fromto Int a1 da a2| means |a2 = a1 `oplus` da = a1 + da|.
So, for any numbers |a1, da, a2| such that |a1 + da = a2|, validity of |df| implies that
\[|f2 (a1 + da) = f1 a1 + df a1 da|.\]

For any two numbers |b1, db| such that |b1 + db = a1 + da|,
we have that
\[|f1 a1 + df a1 da = f2 (a1 + da) = f2 (b1 + db) = f1 b1 + df b1 db|.\]

Rearranging terms, we have
\[|df a1 da - df b1 db = f1 b1 - f1 a1|,\]
that is, |df a1 da - df b1 db| does not depend on |da| and |db|.

For concreteness, let us fix |a1 = 0|, |b1 = 1|, and |a1 + da = b1 + db = s|. We have then that
\[|df 0 s - df 1 (s - 1) = f1 1 - f1 0|,\]
Once we set |h = f1 1 - f1 0|, we have |df 0 s - df 1 (s - 1) =
h|.
Because |s| is just the sum of two arbitrary numbers, while |h|
only depends on |f1|, this equation must hold for a fixed |h| and
for all integers |s|.

To sum up, we assumed for a given |df| there exists |f1, f2| such
that |fromto (Int -> Int) f1 df f2|, and concluded that there
exists |h = f1 1 - f1 0| such that for all |s|
\[|df 0 s - df 1 (s - 1) = h|.\]

At this point, we can try concrete families of functions |df| to
obtain a contradiction. Substituting a linear polynomial $|df a
da| = c_1 \cdot a + c_2 \cdot |da|$ fails to obtain a
contradiction: in fact, we can construct various |f1, f2| such
that |fromto (Int -> Int) f1 df f2|. So we try quadratic
polynomials: Substituting $|df a da| = c \cdot |da|^2$ succeeds:
we have that there is |h| such that for all integers |s|
\[c \cdot \left(s^2 - (s - 1)^2\right) = h.\]

However, $c \cdot \left(s^2 - (s - 1)^2\right) = 2 \cdot c \cdot
s - c$ which isn't constant, so there can be no such |h|.
\end{example}

\section{Pointwise function changes}
\label{ssec:pointwise-changes}
% We can also describe the difference from function |f| to function
% |f `oplus` df| as |nabla^f = \x -> f2 x `ominus` f1 x|.
\pg{Our definition of function change might seem to defy intuitions. In
  particular, pointwise changes might appear more intuitive. We discuss them
  later, too.}

We can also decompose function changes into orthogonal (and
possibly easier to understand) concepts.

Consider two functions |f1, f2 : A -> B| and two inputs |a1, a2: A|.
The difference between |f2 a2| and |f1 a1| is due to changes to
both the function and its argument. We can compute the whole
change at once via a function change |df| as |df a1 da|. Or we
can compute separately the effects of the function change and of
the argument change. We can account for changes from |f1 a1| to |f2 a2|
using |f1'|, a derivative of |f1|: |f1' a1 da = f1 a2 `ominus` f1 a2 = f1 (a1
`oplus` da) `ominus` f a1|.%
%
\footnote{For simplicity, we use equality on changes, even though equality is
  too restrictive. Later (in \cref{sec:change-equivalence}) we'll define an
  equivalence relation on changes, called change equivalence and written
  |`doe`|, and use it systematically to relate changes in place of equality. For
  instance, we'll write that |f1' a1 da `doe` f1 (a1 `oplus` da) `ominus` f1 a1|.
  But for the present discussion, equality will do.}

We can account for changes from |f1| to |f2| using the
\emph{pointwise difference} of two functions, |nabla ^ f1 = \(a : A) ->
f2 a `ominus` f1 a|; in particular, |f2 (a1 `oplus` da) `ominus`
f1 (a1 `oplus` da) = nabla ^ f (a1 `oplus` da)|. Hence, a
function change simply \emph{combines} a derivative with a
pointwise change using change composition:
%
%To account for changes to $a$, we can use
%$f'$, the derivative of $f$. To account for changes to $f$, we
%can use the \emph{pointwise difference} of two functions, $\nabla
%f = \Lam{a}{\App{\New{f}}{a} \DIFF \App{\Old{f}}{a}}$.
%
% Now,
%assuming for the moment the incrementalization theorem, we can
%show the meaning of a function change $df$ in terms of
%derivatives and pointwise changes:
%
\begin{equation}
\begin{aligned}
\label{eq:pointwise-rewrite}
|df a1 da| & = |f2 a2 `ominus` f1 a1|\\
           & = |ocompose ((f1 a2 `ominus` f1 a1)) ((f2 a2 `ominus` f1 a2))|\\
           & = |ocompose (f1' a1 da) (nabla ^ f (a1 `oplus` da))|
\end{aligned}
\end{equation}
One can also compute a pointwise change from a function change:
\begin{code}
  nabla f a = df a (nil a)
\end{code}

While some might find pointwise changes a more natural concept,
we find it easier to use our definitions of function changes,
which combines both pointwise changes and derivatives into a
single concept.
Some related works explore the use of pointwise changes; we discuss them in
\cref{sec:rw-partial-differentials}.

\section{Modeling only valid changes}
\label{sec:alt-change-validity}
\newcommand{\ilcA}{ILC'14}
\newcommand{\ilcB}{ILC'17}

In this section, we contrast briefly the formalization of ILC in this thesis (for short
\ilcB) with the one we used in our first formalization~\citep{CaiEtAl2014ILC}
(for short \ilcA). We keep the discussion somewhat informal; we have sketched
proofs of our claims and mechanized some, but we omit all proofs here.
We discuss both formalizations using our current notation and terminology,
except for concepts that are not present here.

Both formalizations model function changes semantically, but the two models we
present are different. Overall, \ilcB{} uses simpler machinery and seems easier
to extend to more general base languages, and its mechanization of \ilcB{}
appears simpler and smaller.
Instead, \ilcA{} studies additional entities but better behaved entities.

In \ilcB{}, input and output domains of function changes contain
\emph{invalid} changes, while in \ilcA{} these domains are restricted to valid
changes via dependent types; \ilcA{} also considers the denotation of |derive t|,
whose domains include invalid changes, but such denotations are studied only indirectly.
In both cases, function changes must map valid
changes to valid changes. But \ilcA{}, application |df v1 dv| is only well-typed
is |dv| is a change valid from |v1|, hence we can simply say that |df v1| respects
change equivalence. As discussed in \cref{sec:change-equivalence}, in \ilcB{}
the analogous property has a trickier statement: we can write |df v1| and apply
it to arbitrary equivalent changes |dv1 `doe` dv2|, even if their source is not
|v1|, but such change equivalences are not preserved.

We can relate the two models by defining a logical relation called
\emph{erasure} (similar to the one described by \citeauthor{CaiEtAl2014ILC}): an
\ilcA{} function change |df| erases to an \ilcB{} function change |df'| relative
to source |f : A -> B| if, given any change |da| that erases
to |da'| relative to source |a1 : A|, output change |df a1 da| erases to |df' a1
da'| relative to source |f a1|.
For base types, erasure simply connects corresponding |da| (with source) with
|da'| in a manner dependent from the base type (often, just throwing away any
embedded proofs of validity).
In all cases, one can show that if and only if |dv| erases to |dv'| with source
|v1|, then |v1 `oplus` dv = v2 `oplus` dv'| (for suitable variants of |`oplus`|):
in other words, |dv| and |dv'| share source and destination (technically,
\ilcB{} changes have no fixed source, so we say that they are changes from |v1|
to |v2| for some |v2|).

In \ilcA{} there is a different incremental semantics |evalInc t| for terms |t|,
but it is still a valid \ilcA{} change. One can show that |evalInc t| (as
defined in \ilcA{}) erases to |evalInc (derive t)| (as defined in \ilcB{}) relative to
source |eval t|; in fact, the needed proof is sketched by
\citeauthor{CaiEtAl2014ILC}, through in disguise.

It seems clear there is no isomorphism between \ilcA{} changes and \ilcB{} changes.
An \ilcB{} function change also accepts invalid changes, and the behavior on
those changes can't be preserved by an isomorphism.
Worse, it seems hard to define a non-isomorphic mapping:
to map an \ilcA{} change |df| to an an \ilcB{} change |erase df|, we have to
define behavior for |(erase df) a da| even when |da| is invalid.
As long as we work in a constructive setting,
we cannot decide whether |da| is valid in general, because |da| can be a
function change with infinite domain.

We can give however a definition that does not need to detect such invalid
changes: Just extract source and destination from a function change using valid
change |nil v|, and take difference of source and destination using |`ominus`|
in the target system.
\begin{code}
  unerase (sigma -> tau) df' = let f = \v -> df' v (nil v) in (f `oplus` df') `ominus` f
  unerase _ dv' = ...

  erase (sigma -> tau) df = let f = \v -> df v (nil v) in (f `oplus` df) `ominus` f
  erase _ dv = ...
\end{code}
We define these function by induction on types (for elements of |Dt^tau|, not
arbitrary change structures), and we overload |`ominus`| for \ilcA{} and
\ilcB{}.
We conjecture that for all types |tau| and for all \ilcB{} changes |dv'| (of the
right type),
|unerase tau dv'| erases to |dv'|, and for all \ilcA{} changes |dv|, |dv| erases
to |erase tau dv'|.

Erasure is a well-behaved logical relation, similar to the ones relating source
and destination language of a compiler and to partial equivalence relations. In
particular, it also induces partial equivalence relations (PER) (see
\cref{sec:doe-per}), both on \ilcA{} changes and on \ilcB{} changes: two \ilcA{}
changes are equivalent if they erase to the same \ilcB{} change, and two \ilcB{}
changes are equivalent if the same \ilcA{} change erases to both. Both relations
are partial equivalence relations (and total on valid changes). Because changes
that erase to each other share source and destination, these induced
equivalences coincide again with change equivalence. That both relations are
PERs also means that erasure is a so-called \emph{quasi-PER}~\citep{Krishnaswami2013internalizing}.
Quasi-PERs are a natural (though not obvious) generalization of PERs for
relations among different sets $R \subseteq S_1 \times S_2$: such relations cannot
be either symmetric or transitive. However, we make no use of additional
properties of quasi-PERs, hence we don't discuss them in further detail.

\subsection{One-sided vs two-sided validity}
There are also further superficial differences among the two definitions.
In \ilcA{}, changes valid with soure |a| have dependent type |Dt^a|. This
dependent type is indexed by the source but not by the destination. Dependent
function changes with source |f: A -> B| have type |(a : A) -> Dt^a -> Dt^(f
a)|, relating the behavior of function change |df| with the behavior of |f| on
original inputs. But this is half of function validity: to relate the behavior of |df|
with the behavior of |df| on updated inputs,
in \ilcA{} valid function changes have to satisfy an additional
equation called \emph{preservation of future}:\footnote{Name suggested by Yufei Cai.}
  \[|f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da)|.\]
This equation appears inelegant, and mechanized proofs were often complicated by the
need to perform rewritings using it. Worse, to show that a function change is
valid, we have to use different approaches to prove it has the correct source
and the correct destination.

This difference is however superficial.
If we replace |f1 `oplus` df| with |f2| and |a1 `oplus` da| with |a2|, this
equation becomes |f1 a1 `oplus` df a1 da = f2 a2|, a consequence of |fromto f1
df f2|. So one might suspect that \ilcB{} valid function changes also satisfy this
equation. This is indeed the case:

% This equation is one requirement that old-style function changes
% had to satisfy. What we have seen is that the new-style
% definition of validity, although different (and we believe
% simpler), implies the same equation.
% First, we show that our valid function changes satisfy
\begin{lemma}
  A valid function change |fromto (A -> B) f1 df f2| satisfies equation
  \[|f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da)|\]
  on any valid input |fromto (A -> B) a1 da a2|.
\end{lemma}
% \begin{proof}
% Assume |fromto (A -> B) f1 df f2| and |fromto A a1 da
% a2|.
% We have to show |f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da)|.

% From the hypotheses one can briefly show that |fromto B (f1 a1) (df a1 da) (f2
% a2)|, that |f2 = f1 `oplus` df| and that |a2 = a1 `oplus` da|.
% We have seen in \cref{eq:fun-preserv-eq} that |f2 a2 = f1 a1
% `oplus` df a1 da|.
% Combining these equations, it follows as desired that
% \begin{equational}
%   \begin{code}
%   f1 a1 `oplus` df a1 da
% =
%   f2 a2
% =
%   (f1 `oplus` df) (a1 `oplus` da)
%   \end{code}
% \end{equational}
% % \[
% %   |f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da) = f1
% %   (a1 `oplus` da) `oplus` df (a1 `oplus` da) (nil (a1 `oplus`
% %   da))|.\]
% \end{proof}

Conversely, one can also show that \ilcA{} function changes also satisfy
two-sided validity as defined in \ilcB{}. Hence, the only true difference
between \ilcA{} and \ilcB{} models is the one we discussed earlier, namely
whether function changes can be applied to invalid inputs or not.

We believe it could be possible to formalize the \ilcA{} model using two-sided
validity, by defining a dependent type of valid changes:
|Dt2 (A -> B) f1 f2 = (a1 a2 : A) -> Dt2 A a1 a2 -> Dt2 B (f1 a1) (f2 a2)|.
We provide more details on such a transformation in
\cref{ch:diff-parametricity-system-f}.

Models restricted to valid changes (like \ilcA{}) are related to models based on
directed graphs and reflexive graphs, where values are graphs vertexes, changes
are edges between change source and change destination (as hinted earlier). In
graph language, validity preservation means that function changes are graph
homomorphisms.

Based on similar insights, \citet{Atkey2015ILC} suggests modeling ILC using
reflexive graphs, which have been used to construct parametric models for System
F and extensions, and calls for research on the relation between ILC and
parametricity. As follow-up work, \citet{CaiPhD} studies models of ILC based on
directed and reflexive graphs.

% Because of |fromto (Int -> Int) f1 df f2| and because |`oplus`|
% respects validity we can show that, for any valid input |fromto
% Int a1 da a2|, we have
% \begin{equation}
%   \label{eq:ex-invalid-int-int}
%   |f2 a2 = f1 a1 `oplus` df a1 da|.
% \end{equation}

% Recall that on integers |a1 `oplus` da = a1 + da|, and that
% |fromto Int a1 da a2| means |a2 = a1 `oplus` da = a1 + da|. So
% \cref{eq:ex-invalid-int-int} becomes
% \begin{equation}
%   %\label{eq:ex-invalid-int-int}
%   |f2 (a1 + da) = f1 a1 + df a1 da|.
% \end{equation}
