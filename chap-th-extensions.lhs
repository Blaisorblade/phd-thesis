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

\section{Towards differentiation for System F}
\label{sec:diff-parametricity-system-f}
Various authors noticed that differentiation appears related to (binary)
parametricity (including \citet{Atkey2015ILC}).
In particular, it resembles a transformation presented by
\citet{Bernardy2011realizability} for arbitrary PTSs.
We show a variant of
differentiation (that we still write |derive t|) that is closer to their
transformation for parametricity (which they write |eval t|).

% The syntax we use
% for change types suggests that

% then extend differentiation to System F.

%{
%format ptsRel = "\mathcal{R}"
%format (idx1 (t)) = "\mathcal{S}_1 \llbracket" t "\rrbracket"
%format (idx2 (t)) = "\mathcal{S}_2 \llbracket" t "\rrbracket"
%format star = "\star"
%format cstar = "\lceil \star \rceil"

%format (ppp(t)) = "\mathcal{P}\llbracket" t "\rrbracket"
%format pElemDt1 (tau) (t1) (t2) = "(" t1, t2 ")\in \mathcal{P}\llbracket" tau "\rrbracket"

%format elemDt2 (tau) (t1) (t2) = "(" t1, t2 ")\in \Delta_2\llbracket" tau "\rrbracket"
%format pElemDt2 (tau) (t1) (dt) (t2) = "(" t1, dt, t2 ")\in \Delta\mathcal{V}\llbracket" tau "\rrbracket"
%format (deriveP(t)) = "\mathcal{DP}\llbracket" t "\rrbracket"

%format stlc = "\lambda_{\to}"
%format stlc2 = "\lambda^2_{\to}"

%format rAlpha = "\mathcal{R}_" alpha
%format alpha1
%format alpha2
\paragraph{The parametricity transformation}
First, we show a variant of their parametricity transformation, adapted to STLC
(ignoring base types). Their transformation is based on the presentation of STLC
as calculus |stlc|, a \emph{Pure Type System} (PTS)~\citep{Barendregt1992lambda}.

In PTSs, terms and types form a single syntactic category, but are distinguished
through an extended typing judgement (written |Gamma /- t : t|) using additional
terms called \emph{sorts}. Function types |sigma -> tau| are generalized by
|Pi|-type |PPi (x : s). t|, where |x| can in general appear free in |t|,
a generalization of |Pi|-types in dependently-typed languages, but also of
universal types |forall X. T| in the System F family; if |x| does not appear
free in |t|, we write |s -> t|.
Typing restricts whether terms of some sort |s1| can abstract over terms of sort
|s2|; different PTSs allow different combinations of sorts |s1| and |s2|
(specified by \emph{relations} |ptsRel|), but
lots of metatheory for PTSs is parameterized over the choice of combinations.
In STLC presented as a PTS, there is an additional
sort |star|; those terms |tau| such that |/- tau : star| are types. We do not
intend to give a full introduction to PTSs, only to introduce what's strictly
needed for our presentation.

\citeauthor{Bernardy2011realizability}'s transformation produces terms in a PTS |stlc2|
that extends STLC with a separate sort |cstar| of propositions, together with
enough abstraction power to abstract propositions over values.
Instead of base types, |stlc| and |stlc2| use uninterpreted type variables |alpha|, but
do not allow terms to bind them. Nevertheless, we can write open terms, free in
type variables for, say, naturals, and term variables for operations on
naturals. STLC restricts |Pi|-types to the usual arrow types through |ptsRel|.
Presenting |stlc| using type variables will help when we come back to System F.

Here, |pElemDt1 tau t1 t2| is an proposition (hence, living in |cstar|),
witnessing that |t1| and |t2| are related;
we write |dxx| for a proof that |x1| and |x2| are related. For type variables |alpha|,
transformed terms abstract over an arbitrary relation |rAlpha| between |alpha1| and
|alpha2|. When |alpha| is instantiated by |tau|, |rAlpha| \emph{can} (but does
not have to) be instantiated with relation |pElemDt1 tau|; this is the essence
of Girard's idea of reducibility candidates~\citep{girard1989proofs}.

A transformed term |ppp(t)| relates two executions of terms |t| in different
environments: it can be read as a proof that term |t| maps related inputs to
related outputs. The proof strategy they
use is the standard one for proving fundamental properties of logical relations;
but instead of doing a proof in the metalevel logic (by induction on terms and
typing derivations), here we define an object-level logic and generate proof
terms in this logic by recursion on terms.
\begin{code}
  pElemDt1 (sigma -> tau) f1 f2 = PPi ((x1 : idx1 sigma)) (x2 : idx2 sigma) (dxx : pElemDt1 sigma x1 x2).
    pElemDt1 tau (f1 x1) (f2 x2)
  pElemDt1 alpha x1 x2 = rAlpha x1 x2

  ppp(x) = dxx
  ppp(\(x : sigma) -> t) =
    \(x1 : idx1 sigma) (x2 : idx2 sigma) (dxx : pElemDt1 sigma x1 x2) ->
      ppp(t)
  ppp(s t) = ppp(s) (idx1 s) (idx2 s) (ppp t)

  ppp(emptyCtx) = emptyCtx
  ppp(Gamma, x : tau) = ppp(Gamma), x1 : idx1(tau), x2 : idx2(tau), dxx : pElemDt1 tau x1 x2
  ppp(Gamma, alpha : star) = ppp(Gamma), alpha1 : star, alpha2 : star, rAlpha : alpha1 -> alpha2 -> cstar
\end{code}

In the above, |idx1 s| and |idx2 s| simply subscript all (term and type) variables in
their arguments with ${}_1$ and ${}_2$, to make them refer to the first or
second computation. To wit, the straightforward definitions are:
\begin{code}
  idx1(x) = x1
  idx1(\(x : sigma) -> t) = \(x1 : sigma) -> idx1 t
  idx1(s t) = (idx1 s) (idx1 t)
  idx1(sigma -> tau) = idx1(sigma) -> idx1(tau)
  idx1(alpha) = alpha1

  idx2(x) = x2
  idx2(\(x : sigma) -> t) = \(x2 : sigma) -> idx2 t
  idx2(s t) = (idx2 s) (idx2 t)
  idx2(sigma -> tau) = idx2(sigma) -> idx2(tau)
  idx2(alpha) = alpha2
\end{code}

It might be unclear how the proof |ppp t| references the original term |t|.
Indeed, it does not do so explicitly. But since in PTS $\beta$-equivalent types
have the same members, we can construct typing judgement that mention |t|. This
is best shown on a small example.

Take for instance an identity function |id = \(x: alpha) -> x|, which is typed
in an open context (that is, |alpha : star /- \(x : alpha) -> x|).
The transformation gives us
\[|pid = ppp id = \(x1 : alpha1) (x2 : alpha2) (dxx : pElemDt1 alpha x1 x2) ->
  dxx|,\]
which simply returns the proofs that inputs are related:
\begin{multline*}
|alpha1 : star, alpha2 : star, rAlpha : alpha1 -> alpha2 -> cstar /-| \\
  |pid : PPi ((x1 : alpha1)) (x2 : alpha2). pElemDt1 alpha x1 x2 -> pElemDt1 alpha
  x1 x2|.
\end{multline*}

This typing judgement does not mention |id|. But since |x1 `betaeq` id x1| and
|x2 `betaeq` id x2|, we can also show that
\begin{multline*}
|alpha1 : star, alpha2 : star, rAlpha : alpha1 -> alpha2 -> cstar /-| \\
  |pid : PPi ((x1 : alpha1)) (x2 : alpha2). pElemDt1 alpha x1 x2 -> pElemDt1 alpha
  (id x1) (id x2)|,
\end{multline*}
or more concisely that
\[
|alpha1 : star, alpha2 : star, rAlpha : alpha1 -> alpha2 -> cstar /-
pid : pElemDt1 (alpha -> alpha) id id|.
\]

\citeauthor{Bernardy2011realizability} prove that this works in general: if
|Gamma /- s : t| then |ppp(Gamma) /- ppp(s): pElemDt1 t (idx1 s) (idx2 s)| (as a
special case of their Theorem 3).

\paragraph{Differentiation and parametricity}
We reobtain a close variant of differentiation by altering the parametricity transform.
Instead of only having proofs that values are related, we can modify |pElemDt1 (tau)
t1 t2| to be a type of values---more precisely, a dependent type |elemDt2 tau t1
t2| of valid changes, indexed by source |t1 : idx1(tau)| and destination |t2 :
idx2(tau)|. Similarly, |rAlpha| is a type of changes, not propositions.
For type variables |alpha|, we specialize the transformation further, ensuring
that |alpha1 = alpha2| (and adapting |idx1, idx2| accordingly). Without this
specialization, we get to deal with changes across different types, which we
don't do just yet.

\begin{code}
  elemDt2 (sigma -> tau) f1 f2 = PPi ((x1 x2 : sigma)) (dx : elemDt2 sigma x1 x2) .
    elemDt2 tau (f1 x1) (f2 x2)
  elemDt2 alpha x1 x2 = rAlpha x1 x2

  derive(x) = dx
  derive(\(x : sigma) -> t) = \(x1 x2 : sigma) (dx : elemDt2 sigma x1 x2) -> derive(t)
  derive(s t) = derive(s) (idx1 s) (idx2 s) (derive t)

  derive(emptyCtx) = emptyCtx
  derive(Gamma, x : tau) = derive(Gamma), x1 : tau, x2 : tau, dx : elemDt2 tau x1 x2
  derive(Gamma, alpha : star) = derive(Gamma), alpha : star, rAlpha : alpha -> alpha -> cstar
\end{code}
Unlike standard differentiation, we pass around both source and
destination of changes. In fact, in general it might also be useful to put in
context, next to type variables |alpha|, also change structures for |alpha|, to
allow terms to use change operations. Since the differentiation output does not
use change operations here (unlike derivatives) we omit change structures for now.

This transformation is not incremental,
as it recomputes both source and destination for each application,
but we could fix this by replacing |idx2 s| with |idx1 s `oplus` derive s| (and
passing change structures to make |`oplus`| available to terms). We ignore such complications.

Along similar lines, we believe we can also generate from |t| a proof in |stlc2|
that |derive t| is correct, that is, that |pElemDt2 tau (idx1 t) (idx2
t) (derive t)|, and that this can be done through the following transformation:
\begin{code}
  pElemDt2 (sigma -> tau) f1 f2 df =
    PPi ((x1 x2 : sigma)) (dx : elemDt2 sigma x1 x2) (dxx : pElemDt2 sigma x1 x2 dx).
      pElemDt2 tau (f1 x1) (f2 x2) (df x1 x2 dx)
  pElemDt2 alpha x1 x2 dx = rAlpha x1 x2 dx
  deriveP(x) = dxx
  deriveP(\(x : sigma) -> t) =
    \(x1 x2 : sigma) (dx : elemDt2 sigma x1 x2) (dxx : pElemDt2 sigma x1 dx x2) ->
      deriveP(t)
  deriveP(s t) = deriveP(s) (idx1 s) (idx2 s) (derive t) (deriveP t)

  deriveP(emptyCtx) = emptyCtx
  deriveP(Gamma, x : tau) = deriveP(Gamma), x1 : tau, x2 : tau,
    dx : elemDt2 tau x1 x2, dxx : pElemDt2 tau x1 dx x2
  deriveP(Gamma, alpha : star) = deriveP(Gamma), alpha : star,
    rAlpha : PPi ((x1 : alpha)) (x2 : alpha) -> PPi ((dx : elemDt2 tau x1 x2)) -> cstar
\end{code}
This term produces a proof object in |stlc2|, whose informal proof content follows
the proof of |derive|'s correctness (\cref{thm:derive-correct}):
For a variable |x|, we just use the assumption |dxx| that
|pElemDt2 tau x1 dx x2|, that we have in context.
For abstractions |\x -> t|, we have to show that |derive t| is correct for all
valid input changes |x1|, |x2|, |dx| and for all proofs |dxx : pElemDt2 sigma x1
dx x2| that |dx| is indeed a valid input change, so we bind
all those variables in context, including proof |dxx|, and use |deriveP t|
recursively to prove that |derive t| is correct in the extended context.
For applications |s t|, we use the proof that |derive s| is correct (obtained
recursively via |deriveP s|). To show that |(derive s) (derive t)|, that is
|derive(s) (idx1 s) (idx2 s) (derive t)|, we simply show that |derive s| is
being applied to valid inputs, using the proof that |derive t| is correct
(obtained recursively via |deriveP t|).

\subsection{Changes across types}

%format ChangeStruct2
%format NilChangeStruct2
%format `bplus` = "\boxplus"
%format bplus = "(" `bplus` ")"
%instance bnilc = "\mathbf{0}_2"
Earlier, we restricted our transformation so that there can be a change
|dt| from |t1| to |t2| only if |t1| and if |t2| have the same type. In this
section we lift this restriction and define \emph{polymorphic change
  structures}. To do so, we sketch how to extend core change-structure
operations to this scenario.
We describe change operations for generalized change structures via a Haskell
typeclass.
\pg{Add such a typeclass earlier.}
\begin{code}
  class ChangeStruct2 tau1 tau2 where
    type Dt2 tau1 tau2
    bplus :: tau1 -> Dt2 tau1 tau2 -> tau2
  class ChangeStruct2 tau tau => NilChangeStruct2 tau where
    bnilc :: tau -> Dt2 tau tau
  \end{code}
We can still adapt all existing change structures |ChangeStruct tau| into
|ChangeStruct2 tau tau|.
\begin{code}
instance ChangeStruct tau => ChangeStruct2 tau tau where
  type Dt2 tau tau = Dt tau
  x1 `bplus` dx = x1 `oplus` dx
\end{code}
We can also have change structures across different types.
Replacement changes are possible:
\begin{code}
  instance ChangeStruct2 tau1 tau2 where
    type Dt2 tau1 tau2 = tau2
    x1 `bplus` x2 = x2
  \end{code}
But replacement changes are not the only option. For product types, or for any
form of nested data, we can apply changes to
the different components, changing the type of some components:
  \begin{code}
  instance (ChangeStruct sigma1 sigma2, ChangeStruct tau1 tau2) =>
      ChangeStruct (sigma1, tau1) (sigma2 , tau2) where
    type Dt2 (sigma1, tau1) (sigma2 , tau2) = (Dt2 sigma1 sigma2, Dt2 tau1 tau2)
    (a1 , b1) `bplus` (da, db) = (a1 `bplus` da, b1 `bplus` db)
\end{code}
The ability to modify a field to one of a different type is also known as
in the Haskell community as \emph{polymorphic record update}, a feature that has
proven desirable in the context of lens
libraries~\citep{OConnor2012polymorphic,Kmett2012mirrored}.

We can also generalize the transformation:
\begin{code}
  elemDt2 (sigma -> tau) f1 f2 = PPi ((x1 : idx1 sigma)) (x2 : idx2 sigma) (dx : elemDt2 sigma x1 x2) .
    elemDt2 tau (f1 x1) (f2 x2)
  elemDt2 alpha x1 x2 = rAlpha x1 x2

  derive(x) = dx
  derive(\(x : sigma) -> t) = \(x1 : idx1 sigma) (x2 : idx2 sigma) (dx : elemDt2 sigma x1 x2) -> derive(t)
  derive(s t) = derive(s) (idx1 s) (idx2 s) (derive t)

  derive(emptyCtx) = emptyCtx
  derive(Gamma, x : tau) = derive(Gamma), x1 : idx1(tau), x2 : idx2(tau), dx : elemDt2 tau x1 x2
  derive(Gamma, alpha : star) = derive(Gamma), alpha1 : star, alpha2 : star, rAlpha : alpha1 -> alpha2 -> cstar
\end{code}

%format dalpha = "d" alpha
At this point, we are also ready to extend the transformation to System F.
\begin{code}
  elemDt2 (forall alpha . T) f1 f2 =
    PPi ((alpha1 : *)) (alpha2 : *) (rAlpha : alpha1 -> alpha2 -> star). elemDt2 T (f1 [alpha1]) (f2 [alpha2])
  derive(PLambda alpha . t) =
    \(alpha1 alpha2: star) (rAlpha : alpha1 -> alpha2 -> star) -> derive(t)
  derive(t (tau)) = derive t (idx1 tau) (idx2 tau) (elemDt2 tau)
\end{code}

  % elemDt2 (forall X . T) f1 f2 = PPi ((X1 : *)) (X2 : *) (DX : *). elemDt2 T (f1 [X1]) (f2 [X2])
  % derive(Lambda X . t) = Lambda X1 X2 DX. derive(t)
  % derive(t [T]) = derive t [idx1 T] [idx2 T] [elemDt2 T]
%}
