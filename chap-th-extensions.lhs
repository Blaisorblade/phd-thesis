% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Extensions and theoretical discussion}
\label{ch:misc-extensions}
In this chapter we collect discussion of a few additional topics related to ILC.

\section{A change structure for sums}
\label{sec:chs-sums}
We can define change structures on disjoint sums |A + B|, given
change structures on |A| and |B|.
\pg{resume.}

\section{Language plugins for products and sums}
\label{ch:prod-sums}

In this section, we show language plugins for sum and product
types.

\pg{Extend by showing the base semantics of these plugins.}
We give ways to give change structures for products and sums.
As primitives, we use the introduction and elimination forms for
these types. Then, we show how to obtain derivatives for these
primitives.

\pg{Consider recursive types, and recursion?}



\section{General recursion}
\label{sec:general-recursion}
\pg{write, and put somewhere. Use the example with |map| on lists.}

This section discusses informally how to differentiate terms
using general recursion and what is the behavior of the resulting terms.

\subsection{Differentiating general recursion}
%format letrec = "\mathbf{letrec}"
%format fix = "\mathbf{fix}"

Earlier we gave a rule for deriving (non-recursive) |lett|:
\begin{code}
derive(lett x = t1 in t2) =
  lett  x = t1
        dx = derive(t1)
  in    derive(t2)
\end{code}
It turns out that we can use the same rule also for recursive
|lett|-bindings, which we write here |letrec| for clarity:
\begin{code}
derive(letrec x = t1 in t2) =
  lett  x = t1
        dx = derive(t1)
  in    derive(t2)
\end{code}

\pg{Reorganize. This order makes no sense.}
\begin{example}
  In \cref{ex:syn-changes-map} we presented a derivative for
  |map|.
  We now rewrite |map| using fixpoint combinators and derive the
  |dmap| applying the rule for deriving |fix|.
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
We can finally show that
\begin{code}
dmap f df Nil Nil = Nil
dmap f df (Cons x xs) (Cons dx dxs) =
  Cons (df x dx) (dmap f df xs dxs)
\end{code}
\end{example}

\subsection{Justification}
However, we justify this rule using fixpoint operators.

Let's consider STLC extended with a family of standard fixpoint
combinators $\Varid{fix}_{|tau|}|: (tau -> tau) -> tau|$, with
|fix|-reduction defined by equation |fix f -> f (fix f)|; we
search for a definition of |derive (fix f)|.

Using informal equational reasoning, if a correct definition of
|derive (fix f)| exists, it must be
\begin{code}
  derive (fix f) = fix ((derive f (fix f)))
\end{code}
\pg{use |`cong`|?}

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
Formalizing our reasoning using denotational semantics would
presumably require the use of domain theory. We leave
such a formalization for future work.
However, we do prove correct a variant of |fix| in
\cref{ch:bsos}, but using operational semantics.

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
relations among different sets $R \subset S_1 \times S_2$: such relations cannot
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
