% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

%{
%format ptsRel = "\mathcal{R}"
%format (idx1 (t)) = "\mathcal{S}_1 \mean{" t "}"
%format (idx2 (t)) = "\mathcal{S}_2 \mean{" t "}"
%format (idxi (t)) = "\mathcal{S}_i \mean{" t "}"
%format star = "\star"
%format cstar = "\lceil \star \rceil"
%format box = "\Box"

%format (ppp(t)) = "\mathcal{P}\mean{" t "}"
%format pElemDt1 (tau) (t1) (t2) = "(" t1, t2 ")\in \mathcal{P}\mean{" tau "}"

%format elemDt2 (tau) (t1) (t2) = "(" t1, t2 ")\in \Delta_2\mean{" tau "}"
%format pElemDt2 (tau) (t1) (dt) (t2) = "(" t1, dt, t2 ")\in \Delta\mathcal{V}\mean{" tau "}"
%format (deriveP(t)) = "\mathcal{DP}\mean{" t "}"

%format stlc = "\lambda_{\to}"
%format stlc2 = stlc "^2"
%  "\lambda^2_{\to}"
%format lamp = "\lambda_P"
%format lamp2 = lamp "^2"
%format lap2 = "\lambda_{P2}"
%format lap22 = lap2 "^2"
%format sysf = "\lambda_{2}"
%format sysf2 = sysf "^2"
%format rAlpha = "\mathcal{R}^" alpha

%if style /= newcode

\chapter{Towards differentiation for System F}
\label{ch:diff-parametricity-system-f}
Differentiation is closely related to both logical relations and parametricity,
as noticed by various authors in discussions of differentiation. \Cref{ch:bsos}
presents novel proofs of ILC correctness by adapting some logical relation techniques.
As a demonstration, we
define in this chapter differentiation for System F, by adapting results about parametricity.
%
We stop short of a full proof that this generalization is correct, but we have
implemented and tested it on a mature implementation of a System F typechecker;
we believe the proof will mostly be a straightforward adaptation of existing ones about
parametricity, but we leave verification for future work.
A key open issue is discussed in \cref{rem:validity-oplus-system-f-not-really}.

% define a form of differentiation to System F that arises as
% an immediate generalization.
% conjecture

% In this chapter, we show how differentiation and the core of its correctness proof
% appear to generalize naturally to System F. We define a transformation
% We stop short of giving a full formal proof,
% but we conjecture our results follow as variations of existing proofs.

% To gain
% initial evidence, we have implemented the transformations described here on top
% of an existing PTS implementation.

% We show a variant of differentiation (that we still write |derive t|) that is
% closer to their transformation for parametricity (which they write |eval t|).

\paragraph{History and motivation}
Various authors noticed that differentiation appears related to (binary)
parametricity (including \citet{Atkey2015ILC}).
In particular, it resembles a transformation presented by
\citet{Bernardy2011realizability} for arbitrary PTSs.%
\footnote{\citeauthor{Bernardy2011realizability} were not the first to introduce
  such a transformation. But most earlier work
focuses on System F, and our presentation follows theirs and uses their added
generality. We refer for details to existing discussions of related
work~\citep{Wadler2007girardreynolds,Bernardy2011realizability}.}
By analogy with unary parametricity, Yufei Cai sketched an extension of
differentiation for arbitrary PTSs, but many questions remained open, and at the
time our correctness proof for ILC was significantly more involved and trickier
to extend to System F, since it was defined in terms of denotational equivalence.
Later, we reduced the proof core to defining a logical relation, proving its
fundamental property and a few corollaries, as shown in~\cref{ch:derive-formally},
Extending this logical relation to System F proved comparably more straightforward.

\paragraph{Parametricity versus ILC}
Both parametricity and ILC define logical relations across program executions on
different inputs. When studying parametricity, differences are only allowed in
the implementations of abstractions (through abstract types or other
mechanisms). To be related, different implementations of the same abstraction
must give results that are equivalent according to the calling program.
Indeed, parametricity defines not just a logical relation but a \emph{logical
equivalence}, that can be shown to be equivalent to contextual
equivalence~(as explained for instance by \citet[Ch.~48]{Harper2016PFPL} or by
\citet{Ahmed2006stepindexed}).

When studying ILC, logical equivalence between terms |t1| and |t2|
(written |pElemDt1 tau t1 t2|), appears to be generalized by the existence
of a valid change |de| between |t1| and |t2| (that is, |fromto tau t1 dt t2|).
As in earlier chapters, if terms |e1| and |e2| are equivalent, any valid change
|dt| between them is a nil change, but validity allows describing other changes.
% The syntax we use
% for change types suggests that

% then extend differentiation to System F.

\section{The parametricity transformation}
\label{sec:parametricity-transform}
First, we show a variant of their parametricity transformation, adapted to a
variant of STLC without base types but with type variables. Presenting |stlc|
using type variables will help when we come back to System F, and allows
discussing parametricity on STLC\@@.
This transformation
is based on the presentation of STLC as calculus |stlc|, a \emph{Pure Type
System} (PTS)~\citep[Sec.~5.2]{Barendregt1992lambda}.

\paragraph{Background}
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
sort |star|; those terms |tau| such that |/- tau : star| are
types.\footnote{Calculus |stlc| has also a sort |box| such that |/- star : box|,
but |box| itself has no type. Such a sort appears only in PTS typing
derivations, not in well-typed terms themselves, so we do not discuss it
further.} We do not intend to give a full introduction to PTSs, only to
introduce what's strictly needed for our presentation, and refer the readers to
existing presentations~\citep{Barendregt1992lambda}.

Instead of base types, |stlc| use uninterpreted type variables |alpha|, but
do not allow terms to bind them. Nevertheless, we can write open terms, free in
type variables for, say, naturals, and term variables for operations on
naturals. STLC restricts |Pi|-types |PPi (x : A). B| to the usual arrow types |A
-> B| through |ptsRel|: one can show that in |PPi (x : A) . B|, variable |x|
cannot occur free in |B|.

\paragraph{Parametricity}
\citeauthor{Bernardy2011realizability} show how to transform a typed term |Gamma
/- t : tau| in a strongly normalizing PTS $P$ into a proof that |t| satisfies a
parametricity statement for |tau|. The proof is in a logic represented by PTS
$P^2$. PTS $P^2$ is constructed uniformly from $P$, and is strongly normalizing
whenever $P$ is.
When the base PTS $P$ is |stlc|,
\citeauthor{Bernardy2011realizability}'s transformation produces terms
in a PTS |stlc2|, produced by transforming |stlc|.
PTS |stlc2| extends |stlc| with a separate sort |cstar| of propositions, together with
enough abstraction power to abstract propositions over values.
Like |stlc|, |stlc2| uses uninterpreted type variables |alpha| and does not
allow abstracting over them.

In parametricity statements about |stlc|, we write |pElemDt1 tau t1 t2| for a
proposition (hence, living in |cstar|) that states that |t1| and |t2| are
related. This proposition is defined, as usual, via a \emph{logical relation}.
We write |dxx| for a proof that |x1| and |x2| are related. For type variables |alpha|,
transformed terms abstract over an arbitrary relation |rAlpha| between |alpha1| and
|alpha2|. When |alpha| is instantiated by |tau|, |rAlpha| \emph{can} (but does
not have to) be instantiated with relation |pElemDt1 tau|, but |rAlpha| abstracts
over arbitrary \emph{candidate} relations (similar to the notion of reducibility
candidates~\citep[Ch.~14.1.1]{girard1989proofs}). Allowing alternative
instantiations makes parametricity statements more powerful, and it is also
necessary to define parametricity for impredicative type systems (like System F)
in a predicative ambient logic.%
\footnote{Specifically, if we require |rAlpha| to be instantiated with the
logical relation itself for |tau| when |alpha| is instantiated with |tau|, the
definition becomes circular. Consider the definition of |pElemDt1 (forall alpha.
tau) t1 t2|: type variable |alpha| can be instantiated with the same type
|forall alpha. tau|, so the definition of |pElemDt1 (forall alpha. tau) t1 t2|
becomes impredicative.}

A transformed term |ppp(t)| relates two executions of terms |t| in different
environments: it can be read as a proof that term |t| maps related inputs to
related outputs. The proof strategy that |ppp(t)|
uses is the standard one for proving fundamental properties of logical relations;
but instead of doing a proof in the metalevel logic (by induction on terms and
typing derivations), |stlc2| serves as an object-level logic, and |ppp|
generates proof terms in this logic by recursion on terms. At the metalevel,
\citeauthor[Th. 3]{Bernardy2011realizability} prove that for any well-typed term
|Gamma /- t : tau|, proof |ppp t| shows that |t| satisfies the parametricity statement
for type |tau| given the hypotheses |ppp Gamma| (or more formally,
|ppp(Gamma) /- ppp(t): pElemDt1 tau (idx1 t) (idx2 t)|).
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
second computation. To wit, the straightforward definition is:
\begin{code}
  idxi(x) = xi
  idxi(\(x : sigma) -> t) = \(xi : sigma) -> idxi t
  idxi(s t) = (idxi s) (idxi t)
  idxi(sigma -> tau) = idxi(sigma) -> idxi(tau)
  idxi(alpha) = alphai
\end{code}

It might be unclear how the proof |ppp t| references the original term |t|.
Indeed, it does not do so explicitly. But since in PTS $\beta$-equivalent types
have the same members, we can construct typing judgement that mention |t|. As
mentioned, from |Gamma /- t : tau| it follows that
|ppp(Gamma) /- ppp(t): pElemDt1 tau (idx1 t) (idx2 t)|~\citep[Th.
3]{Bernardy2011realizability}. This is best shown on a small example.

\begin{example}
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

This typing judgement does not mention |id|. But since |x1 `betaeq`
idx1 id x1| and
|x2 = idx2 id x2|, we can also show that |id|'s outputs are related whenever the
inputs are:
\begin{multline*}
|alpha1 : star, alpha2 : star, rAlpha : alpha1 -> alpha2 -> cstar /-| \\
  |pid : PPi ((x1 : alpha1)) (x2 : alpha2). pElemDt1 alpha x1 x2 -> pElemDt1 alpha
  (idx1 id x1) (idx2 id x2)|.
\end{multline*}
More concisely, we can show that:
\[
|alpha1 : star, alpha2 : star, rAlpha : alpha1 -> alpha2 -> cstar /-
pid : pElemDt1 (alpha -> alpha) (idx1 id) (idx2 id)|.
\]
\end{example}

\section{Differentiation and parametricity}
\label{sec:differentiation-dep-types-stlc}
\pg{Figure out if we're just redoing \citep{Bernardy10}.}
We obtain a close variant of differentiation by altering the transformation for
binary parametricity. We obtain a variant very close to the one investigated by \citet*{Bernardy10}.
Instead of only having proofs that values are related, we can modify |pElemDt1 (tau)
t1 t2| to be a type of values---more precisely, a dependent type |elemDt2 tau t1
t2| of valid changes, indexed by source |t1 : idx1(tau)| and destination |t2 :
idx2(tau)|. Similarly, |rAlpha| is replaced by a dependent type of changes, not
propositions, that we write |DtAlpha|.
Formally, this is encoded by replacing sort |cstar| with |star| in
\citet{Bernardy2011realizability}'s transform, and by moving
target programs in a PTS that allows for both simple and dependent types, like
the Edinburgh Logical Framework; such a PTS is known as
|lamp|~\citep{Barendregt1992lambda}.

For type variables |alpha|, we specialize the transformation further, ensuring
that |alpha1 = alpha2 = alpha| (and adapting |idx1, idx2| accordingly to \emph{not} add
subscripts to type variable). Without this
specialization, we get to deal with changes across different types, which we
don't do just yet but defer to \cref{sec:param-derive-changes-across-types}.

We first show how the transformation affects typing contexts:
\begin{code}
  derive(emptyCtx) = emptyCtx
  derive(Gamma, x : sigma) = derive(Gamma), x1 : sigma, x2 : sigma, dx : elemDt2 sigma x1 x2
  derive(Gamma, alpha : star) = derive(Gamma), alpha : star, DtAlpha : alpha -> alpha -> star
\end{code}
Unlike standard differentiation, transformed programs bind, for each input
variable |x: sigma|,
a source |x1: sigma|, a destination |x2 : sigma|, and a valid change |dx| from
|x1| to |x2|. More in detail, for each variable in input programs |x : sigma|, programs produced by standard
differentiation bind both |x : sigma| and |dx : sigma|; valid use of these
programs requires |dx| to be a valid change with source |x|, but this is not
enforced through types.
Instead, programs produced by \emph{this variant} of differentiation bind,
for each variable in input programs |x : sigma|, both source |x1 :
sigma|, destination |x2 : sigma|, and a valid change |dx| from |x1| to |x2|,
where validity is enforced through dependent types.

For input type variables |alpha|, output programs also bind a dependent type of
valid changes |DtAlpha|.

Next, we define the type of changes. Since change types are indexed by source
and destination, the type of function changes forces them to be valid, and the
definition of function changes resembles our earlier logical relation for
validity.
More precisely, if |df| is a change from |f1| to |f2| (|df : elemDt2 (sigma -> tau) f1 f2|), then
|df| must map any change |dx| from initial input |x1| to updated input |x2| to a
change from initial output |f1 x1| to updated output |f2 x2|.
\begin{code}
  elemDt2 (sigma -> tau) f1 f2 = PPi ((x1 x2 : sigma)) (dx : elemDt2 sigma x1 x2) .
    elemDt2 tau (f1 x1) (f2 x2)
  elemDt2 alpha x1 x2 = DtAlpha x1 x2
\end{code}
At this point, the transformation on terms acts on abstraction and application
to match the transformation on typing contexts. The definition of |derive(\(x :
sigma) -> t| follows the definition of |derive(Gamma, x : sigma)|---both
transformation results bind the same variables |x1, x2, dx| with the same types.
Application provides corresponding arguments.
\begin{code}
  derive(x) = dx
  derive(\(x : sigma) -> t) = \(x1 x2 : sigma) (dx : elemDt2 sigma x1 x2) -> derive(t)
  derive(s t) = derive(s) (idx1 s) (idx2 s) (derive t)
\end{code}
% Unlike standard differentiation, we pass around both source and
% destination of changes, and the type of changes is indexed by both source and
% destination.
% Making different choices would still give us a correct
% transformation; but
% The transformation
% Here, we could just as well pass only the source, but
% next section we are going to alter this transformation to produce proofs of
% correctness
% are next going to pass around

If we extend the language to support primitives and their manually-written
derivatives, it is useful to have contexts also bind,
next to type variables |alpha|, also change structures for |alpha|, to
allow terms to use change operations. Since the differentiation output does not
use change operations here, we omit change structures for now.

\begin{remark}[Validity and |`oplus`|]
  \label{rem:validity-oplus-system-f-not-really}
Because we omit change structures (here and through most of the chapter),
the type of differentiation only suggests that |derive t| is a valid change, but
not that validity agrees with |`oplus`|.

In other words, dependent types as used
here do not prove all theorems expected of an incremental transformation.
While we can prove the fundamental property
of our logical relation, we cannot prove that |`oplus`| agrees with
differentiation for abstract types. As we did in \cref{sec:chs-types-contexts} (in
particular \cref{req:base-change-structures}), we must require that validity
relations provided for type variables agree with implementations of |`oplus`| as
provided for type variables: formally, we must state (internally) that
|forall ((x1 x2 : alpha)) (dx: DtAlpha x1 x2). pElemDt1 alpha (x1 `oplus` dx) x2|.
We can state this requirement by internalizing
logical equivalence (such as shown in \cref{sec:parametricity-transform}, or
using \citet{Bernardy10}'s variant in |lamp|). But since this statement
quantifies over members of |alpha|, it is not clear if it can be proven
internally when instantiating |alpha| with a type argument. We leave this
question (admittedly crucial) for future work.
%or if such a proof resembles .
%
% we expect it cannot be proved internally without
% extending the language, similarly to how parametricity cannot be proven
% internally to System F.
\end{remark}

This transformation is not incremental,
as it recomputes both source and destination for each application,
but we could fix this by replacing |idx2 s| with |idx1 s `oplus` derive s| (and
passing change structures to make |`oplus`| available to terms), or by not
passing destinations. We ignore such complications here.
\pg{Don't. A formal proof becomes a variant of Bernardy2011realizability.}
% A proof that this variant of |derive| is correct proceeds similarly to our
% earlier proof of \cref{thm:derive-correct}, but it requires additional
% lemmas about |idx1| and |idx2|.
% \begin{theorem}
% If |Gamma /- t : tau| then |derive (Gamma) /- derive t : elemDt2 tau (idx1 t) (idx2 t)|.
% \end{theorem}

\section{Proving differentiation correct externally}
Instead of producing dependently-typed programs that show their correctness, we
might want to produce simply-typed programs (which are easier to compile
efficiently) and use an external correctness proof, as in
\cref{ch:derive-formally}. We show how to generate such external proofs here.
For simplicity, here we produce external correctness proofs for the
transformation we just defined on dependently-typed outputs, rather than
defining a separate simply-typed transformation.

Specifically, we show how to generate
%Along similar lines, we believe we can also generate
from well-typed terms |t| a proof that |derive t| is correct, that is, that
|pElemDt2 tau (idx1 t) (idx2 t) (derive t)|.
% \pg{This variant is pointless because |derive t| is intrinsically correct, but
%   we could show this for transformations that are not.}
%While we show this proof for intrinsically-typed

Proofs are generated through the following transformation, defined in terms of
the transformation from \cref{sec:differentiation-dep-types-stlc}. Again, we
show first typing contexts and the logical relation:
\begin{code}
  deriveP(emptyCtx) = emptyCtx
  deriveP(Gamma, x : tau) = deriveP(Gamma), x1 : tau, x2 : tau,
    dx : elemDt2 tau x1 x2, dxx : pElemDt2 tau x1 x2 dx
  deriveP(Gamma, alpha : star) = deriveP(Gamma), alpha : star,
    DtAlpha : alpha -> alpha -> star,
    rAlpha : PPi ((x1 : alpha)) (x2 : alpha) (dx : elemDt2 alpha x1 x2) -> cstar

  pElemDt2 (sigma -> tau) f1 f2 df =
    PPi ((x1 x2 : sigma)) (dx : elemDt2 sigma x1 x2) (dxx : pElemDt2 sigma x1 x2 dx).
      pElemDt2 tau (f1 x1) (f2 x2) (df x1 x2 dx)
  pElemDt2 alpha x1 x2 dx = rAlpha x1 x2 dx
\end{code}
The transformation from terms to proofs then matches the definition of typing contexts:
\begin{code}
  deriveP(x) = dxx
  deriveP(\(x : sigma) -> t) =
    \(x1 x2 : sigma) (dx : elemDt2 sigma x1 x2) (dxx : pElemDt2 sigma x1 x2 dx) ->
      deriveP(t)
  deriveP(s t) = deriveP(s) (idx1 s) (idx2 s) (derive t) (deriveP t)
\end{code}
This term produces a proof object in PTS |lamp2|, which is produced by
augmenting |lamp| following \citet{Bernardy2011realizability}.
The informal proof content of generated proofs follows
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

% End of %if style /= newcode:
%endif

\section{Combinators for polymorphic change structures}
\label{sec:param-derive-changes-across-types}

%if style /= newcode

%format ChangeStruct2
%format NilChangeStruct2
%format `bplus` = "\myboxplus"
%format bplus = "(" `bplus` ")"
%instance bnilc = "\mathbf{0}_2"

%format CS = "\mathbb{CS}"

%format delta = "\delta"
%format dsigma = delta "_" sigma
%format dtau = delta "_" tau
%format dtaua = delta "_{\tau a}"
%format dtaub = delta "_{\tau b}"
%format $ = "\mathrel{\$}"
%format ListMu = List "_{\mu}"
%else

\begin{code}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Examples.ChangeStructureFirstClass where

class ChangeStruct t where
  type Dt t = r | r -> t
  oplus :: t -> Dt t -> t

\end{code}
%endif

Earlier, we restricted our transformation on |stlc| terms, so that there could be a change
|dt| from |t1| to |t2| only if |t1| and if |t2| have the same type. In this
section we lift this restriction and define \emph{polymorphic} change
structures (also called change structures when no ambiguity arises). To do so,
we sketch how to extend core change-structure operations to polymorphic change structures.

We also show a few \emph{combinators}, combining existing polymorphic change
structures into new ones. We believe the combinator types are more enlightening
than their implementations, but we include them here for completeness.
We already described a few constructions on non-polymorphic change structures;
however, polymorphic change structures enable new constructions that insert or
remove data, or apply isomorphisms to the source or destination type.

We conjecture that combinators for polymorphic change structure can be used to
compose, out of small building blocks, change structures that, for instance,
allow inserting or removing elements from a recursive datatype such as lists.
Derivatives for primitives could then be produced using equational reasoning as
described in \cref{sec:plugin-design}.
However, we leave investigation of such avenues to future work.

We describe change operations for polymorphic change structures via a Haskell
record containing change operations, and we define combinators on polymorphic
change structures. Of all change operations, we only consider |`oplus`|; to
avoid confusion, we write |`bplus`| for the polymorphic variant of |`oplus`|.
\begin{code}
data CS tau1 dtau tau2 = CS {
  bplus :: tau1 -> dtau -> tau2
}
\end{code}
This code define a record type constructor |CS| with a data constructor also
written |CS|, and a field accessor written |bplus|; we use |tau1|, |dtau| and
|tau2| (and later also |sigma1|, |dsigma| and |sigma2|) for
Haskell type variables. To follow Haskell lexical rules, we use here lowercase
letters (even though Greek ones).

We have not formalized definitions of validity, or proofs that it agrees with
|`bplus`|, but for all the change structures and combinators in this section,
this exercise appears no harder than the ones in \cref{ch:change-theory}.

In \cref{sec:diff-examples-tc,sec:cts-motivation} change structures are embedded in Haskell
using type class |ChangeStruct tau|. Conversely, here we do not define a type
class of polymorphic change
structures, because (apart from the simplest scenarios), Haskell type class
resolution is unable to choose a \emph{canonical} way to construct a polymorphic
change structure using our combinators.

All existing change structures (that is, instances of |ChangeStruct tau|) induce
generalized change structures |CS tau (Dt^tau) tau|.
\begin{code}
typeCS :: ChangeStruct tau => CS tau (Dt^tau) tau
typeCS = CS oplus
\end{code}

We can also have change structures across different types.
Replacement changes are possible:
\begin{code}
replCS :: CS tau1 tau2 tau2
replCS = CS $ \x1 x2 -> x2
\end{code}
% Unbreak Emacs syntax highlighting with $
But replacement changes are not the only option. For product types, or for any
form of nested data, we can apply changes to
the different components, changing the type of some components. We can also
define a change structure for nullary products (the unit type) which can be
useful as a building block in other change structures:%
\begin{code}
prodCS :: CS sigma1 dsigma sigma2 -> CS tau1 dtau tau2 -> CS (sigma1, tau1) (dsigma, dtau) (sigma2, tau2)
prodCS scs tcs = CS $ \ (s1, t1) (ds, dt) -> (bplus scs s1 ds, bplus tcs t1 dt)
unitCS :: CS () () ()
unitCS = CS $ \() () -> ()
\end{code}
% Unbreak Emacs syntax highlighting with $
The ability to modify a field to one of a different type is also known as
in the Haskell community as \emph{polymorphic record update}, a feature that has
proven desirable in the context of lens
libraries~\citep{OConnor2012polymorphic,Kmett2012mirrored}.

We can also define a combinator |sumCS| for change structures on sum types,
similarly to our earlier construction described in \cref{sec:chs-sums}.
This time, we choose to forbid changes across branches since they're
inefficient, though we could support them as well, if desired.
\begin{code}
sumCS :: CS s1 ds s2 -> CS t1 dt t2 ->
  CS (Either s1 t1) (Either ds dt) (Either s2 t2)

sumCS scs tcs = CS go
  where
    go (Left s1) (Left ds) = Left $ bplus scs s1 ds
    go (Right t1) (Right dt) = Right $ bplus tcs t1 dt
    go _ _ = error "Invalid changes"
\end{code}

Given two change structures from |tau1| to |tau2|, with respective change types
|dtaua| and |dtaub|, we can also define a new change structure with change type
|Either dtaua dtaub|, that allows using changes from either structure.
We capture this construction through combinator |mSumCS|, having the following
signature:
\begin{code}
mSumCS :: CS tau1 dtaua tau2 -> CS tau1 dtaub tau2 -> CS tau1 (Either dtaua dtaub) tau2

mSumCS acs bcs = CS go
  where
    go t1 (Left dt) = bplus acs t1 dt
    go t1 (Right dt) = bplus bcs t1 dt
\end{code}
This construction is possible for non-polymorphic change structures; we only
need change structures to be first-class (instead of a type class) to be able to internalize this construction in Haskell.

Using combinator |lInsCS| we can describe updates going from type |tau1| to type |(sigma, tau2)|,
assuming a change structure from |tau1| to |tau2|:
that is, we can prepend a value of type |sigma| to our data while we modify it.
Similarly, combinator |lRemCS| allows removing values:
% What's more, we can also define change structures that allow inserting or
% removing elements into nested tuples.
% We believe combining such change structures might produce
% more interesting ones.
\begin{code}
lInsCS :: CS t1 dt t2 -> CS t1 (s, dt) (s, t2)
lInsCS tcs = CS $ \t1 (s, dt) -> (s, bplus tcs t1 dt)

lRemCS :: CS t1 dt (s, t2) -> CS t1 dt t2
lRemCS tcs = CS $ \t1 dt -> snd $ bplus tcs t1 dt
\end{code}
% Unbreak Emacs syntax highlighting with $

We can also transform change structures given suitable conversion functions.
\begin{code}
lIsoCS :: (t1 -> s1) -> CS s1 dt t2 -> CS t1 dt t2
mIsoCS :: (dt -> ds) -> CS t1 ds t2 -> CS t1 dt t2
rIsoCS :: (s2 -> t2) -> CS t1 dt s2 -> CS t1 dt t2
isoCS :: (t1 -> s1) -> (dt -> ds) -> (s2 -> t2) -> CS s1 ds s2 -> CS t1 dt t2
\end{code}
To do so, we must only compose |`bplus`| with the given conversion functions
according to the types. Combinator |isoCS| arises by simply combining the other ones:
\begin{code}
lIsoCS f tcs     = CS $ \s1 dt -> bplus tcs (f s1) dt
mIsoCS g tcs     = CS $ \t1 ds -> bplus tcs t1 (g ds)
rIsoCS h tcs     = CS $ \t1 dt -> h $ bplus tcs t1 dt
isoCS f g h scs  = lIsoCS f $ mIsoCS g $ rIsoCS h scs
\end{code}

With a bit of datatype-generic programming infrastructure, we can reobtain only
using combinators the change
structure for lists shown in \cref{sec:simple-changes-list-map}, which allows
modifying list elements. The core definition is the following one:
\begin{code}
listMuChangeCS :: CS a1 da a2 -> CS (ListMu a1) (ListMu da) (ListMu a2)
listMuChangeCS acs = go where
    go =  isoCS unRollL unRollL rollL $
          sumCS unitCS $ prodCS acs go
\end{code}
The needed infrastructure appears in \cref{fig:change-structure-list-w-combinators}.

% -- This change structure is implemented directly, but should be done using combinators.
% listChangeCS :: CS a1 da a2 -> CS (List a1) (List da) (List a2)
% listChangeCS acs = resCS
%   where
%     resCS = CS go
%     go Nil Nil = Nil
%     go (Cons a1 as1) (Cons da das) = Cons (bplus acs a1 da) (bplus resCS as1 das)
%     go _ _ = error "Invalid change"

\begin{figure}[h]
\texths %drop extra space around figure
\begin{code}
-- Our list type:
data List a = Nil | Cons a (List a)

-- Equivalently, we can represent lists as a fixpoint of a sum-of-product pattern functor:
data Mu f = Roll { unRoll :: f (Mu f) }
data ListF a x = L { unL :: Either () (a, x) }
type ListMu a = Mu (ListF a)

rollL :: Either () (a, ListMu a) -> ListMu a
rollL = Roll . L
unRollL :: ListMu a -> Either () (a, ListMu a)
unRollL = unL . unRoll

-- Isomorphism between |List| and |ListMu|:
lToLMu :: List a -> ListMu a
lToLMu Nil = rollL $ Left ()
lToLMu (Cons a as) = rollL $ Right (a, lToLMu as)

lMuToL :: ListMu a -> List a
lMuToL = go . unRollL where
  go (Left ()) = Nil
  go (Right (a, as)) = Cons a (lMuToL as)

-- A change structure for |List|:
listChangesCS :: CS a1 da a2 -> CS (List a1) (List da) (List a2)
listChangesCS acs = isoCS lToLMu lToLMu lMuToL $ listMuChangeCS acs
\end{code}
% Unbreak Emacs syntax highlighting with $

  \caption{A change structure that allows modifying list elements.}
  \label{fig:change-structure-list-w-combinators}
\end{figure}

\paragraph{Section summary}
We have defined polymorphic change structures and shown they admit a rich
combinator language. Now, we return to using these change structures for
differentiating |stlc| and System F.
% With a better way to describe a change from values of type |a| to
% values of type |b|,
%\pg{Later we sketch change structures across types.}

%\pg{Idea: |ChangeStruct2 t1 t2, Iso t2 t3) => ChangeStruct2 t1 t3|}
% Lists can be described as the fixpoint of a sum of
% product: |List a = mu X. 1 + A `times` X|

%if style /= newcode
\section{Differentiation for System F}
\label{sec:param-derive-changes-across-types-transform}
After introducing changes across different types, we can also generalize
differentiation for |stlc| so that it allows for the now generalized changes:
\begin{code}
  elemDt2 (sigma -> tau) f1 f2 = PPi ((x1 : idx1 sigma)) (x2 : idx2 sigma) (dx : elemDt2 sigma x1 x2) .
    elemDt2 tau (f1 x1) (f2 x2)
  elemDt2 alpha x1 x2 = DtAlpha x1 x2

  derive(x) = dx
  derive(\(x : sigma) -> t) = \(x1 : idx1 sigma) (x2 : idx2 sigma) (dx : elemDt2 sigma x1 x2) -> derive(t)
  derive(s t) = derive(s) (idx1 s) (idx2 s) (derive t)

  derive(emptyCtx) = emptyCtx
  derive(Gamma, x : tau) = derive(Gamma), x1 : idx1(tau), x2 : idx2(tau), dx : elemDt2 tau x1 x2
  derive(Gamma, alpha : star) = derive(Gamma), alpha1 : star, alpha2 : star, DtAlpha : alpha1 -> alpha2 -> star
\end{code}
By adding a few additional rules, we can extend differentiation to System F (the
PTS |sysf|). We choose to present the additional rules using System F syntax
rather than PTS syntax.
\begin{code}
  elemDt2 (forall alpha . T) f1 f2 =
    PPi ((alpha1 : *)) (alpha2 : *) (DtAlpha : alpha1 -> alpha2 -> star). elemDt2 T (f1 [alpha1]) (f2 [alpha2])
  derive(PLambda alpha . t) =
    \(alpha1 alpha2: star) (DtAlpha : alpha1 -> alpha2 -> star) -> derive(t)
  derive(t [tau]) = derive t (idx1 tau) (idx2 tau) (elemDt2 tau)
\end{code}
Produced terms use a combination of System F and dependent types, which is known
as |lap2|~\citep{Barendregt1992lambda} and is strongly normalizing. This PTS
corresponds to second-order (intuitionistic) predicate logic and is part of
Barendregt's \emph{lambda cube}; |lap2| does not admit types depending on types
(that is, type-level functions), but admits all other forms of abstraction in
the lambda cube (terms on terms like |stlc|, terms on types like System F, and
types on terms like LF/|lamp|).

Finally, we sketch a transformation producing proofs that differentiation is
correct for System F\@@.
\begin{code}
  deriveP(emptyCtx) = emptyCtx
  deriveP(Gamma, x : tau) = deriveP(Gamma), x1 : idx1(tau), x2 : idx2(tau),
    dx : elemDt2 tau x1 x2, dxx : pElemDt2 tau x1 x2 dx
  deriveP(Gamma, alpha : star) = deriveP(Gamma),
    alpha1 : star, alpha2 : star, DtAlpha : alpha1 -> alpha2 -> star
    rAlpha : PPi ((x1 : alpha1)) (x2 : alpha2) (dx : elemDt2 alpha x1 x2) -> cstar

  pElemDt2 (forall alpha. T) f1 f2 df =
    PPi ((alpha1 : *)) (alpha2 : *) (DtAlpha : alpha1 -> alpha2 -> star)
    (rAlpha : PPi ((x1 : alpha1)) (x2 : alpha2) (dx : elemDt2 alpha x1 x2) -> cstar).
      pElemDt2 T (f1 [alpha1]) (f2 [alpha2]) (df [alpha1] [alpha2] [DtAlpha])
  pElemDt2 (sigma -> tau) f1 f2 df =
    PPi ((x1 : idx1 sigma)) (x2 : idx2 sigma) (dx : elemDt2 sigma x1 x2) (dxx : pElemDt2 sigma x1 x2 dx).
      pElemDt2 tau (f1 x1) (f2 x2) (df x1 x2 dx)
  pElemDt2 alpha x1 x2 dx = rAlpha x1 x2 dx

  deriveP(x) = dxx
  deriveP(\(x : sigma) -> t) =
    \  (x1 : idx1 sigma) (x2 : idx2 sigma) (dx : elemDt2 sigma x1 x2)
       (dxx : pElemDt2 sigma x1 x2 dx) ->
       deriveP(t)
  deriveP(s t) = deriveP(s) (idx1 s) (idx2 s) (derive t) (deriveP t)
  deriveP(PLambda alpha . t) =
    \  (alpha1 alpha2: star) (DtAlpha : alpha1 -> alpha2 -> star)
       (rAlpha : PPi ((x1 : alpha1)) (x2 : alpha2) (dx : elemDt2 alpha x1 x2) -> cstar) ->
       deriveP(t)
  deriveP(t [tau]) = deriveP t (idx1 tau) (idx2 tau) (elemDt2 tau) (pElemDt2 tau)
\end{code}
Produced terms live in |lap22|, the logic produced by extending |lap2| following
\citeauthor{Bernardy2011realizability}. A variant producing proofs for a
non-dependently-typed differentiation (as suggested earlier) would produce
proofs in |sysf2|, the logic produced by extending |sysf| following
\citeauthor{Bernardy2011realizability}.

%endif

\section{Related work}
Dependently-typed differentiation for System F, as given, coincides with the
parametricity transformation for System F given by \citet*[Sec.~3.1]{Bernardy10}. But our
application is fundamentally different: for known types, \citeauthor{Bernardy10}
only consider identity relations, while we can consider non-identity relations
as long as we assume that |`ominus`| is available for all types.\pg{say this
  earlier!}
What is more, \citeauthor{Bernardy10} do not consider changes, the update
operator |`oplus`|, or change structures across different types: changes are
replaced by proofs of relatedness with no computational significance.
Finally, non-dependently-typed differentiation (and its corectness proof) is
novel here, as it makes limited sense in the context of parametricity, even
though it is a small variant of \citeauthor{Bernardy10}'s parametricity transform.
%(if we assume |`ominus`| is available)
\pg{Demonstrate the actual contributions, they aren't here!}

\section{Prototype implementation}
\label{sec:param-derive-implementation}
We have written a prototype implementation of the above rules for a PTS
presentation of System F, and verified it on a few representative examples of
System F terms. We have built our implementation on top of an existing
typechecker for PTSs.\footnote{\url{https://github.com/Toxaris/pts/}, by Tillmann
  Rendel, based on \citet{vanBenthemJutting1994checking}'s algorithm for
  PTS typechecking.}

Since our implementation is defined in terms of a generic PTS, some of the rules
presented above are unified and generalized in our implementation, suggesting
the transformation might generalize to arbitrary PTSs. In the absence of
further evidence on the correctness of this generalization, we leave a detailed
investigation as future work.

  % elemDt2 (forall X . T) f1 f2 = PPi ((X1 : *)) (X2 : *) (DX : *). elemDt2 T (f1 [X1]) (f2 [X2])
  % derive(Lambda X . t) = Lambda X1 X2 DX. derive(t)
  % derive(t [T]) = derive t [idx1 T] [idx2 T] [elemDt2 T]
%}

% \chapter{Stuff}
% In this chapter, we relate our formalization of changes with the one by
% \citet{CaiEtAl2014ILC} in \cref{sec:alt-change-validity}.
% \pg{We have proved equivalence with the one-sided definition of validity.}
% \subsection{Alternative definitions of change validity}
% \label{sec:alt-change-validity}

% % \newcommand{\ilcA}{ILC'14}
% % \newcommand{\ilcB}{ILC'17}

% In this section we compare the formalization of ILC in this thesis (\ilcB)
% with the one we and others used in our \emph{old-style}
% formalization, that is, our first formalization of change
% theory~\citep{CaiEtAl2014ILC} (\ilcA).
% We discuss both formalizations using our current notation and terminology, except for concepts
% that are not present here.
% Both formalizations model function changes semantically, but the two models we
% present are different. Overall, \ilcB{} uses simpler machinery and seems easier
% to extend to more general base languages. Instead, \ilcA{} studies additional
% entities, which however are in some ways better behaved.

% In \ilcB{} function changes whose input and output domains contain
% \emph{invalid} changes; but function changes must map valid changes to valid
% changes. As shown, |eval(derive t)| maps valid changes to valid changes.

% Instead, \ilcA{} does not define validity on change set |Dt^A|. For each value
% |a : A| \ilcA{} defines a \emph{based} change set |Dt^a|; elements of |Dt^a|
% \emph{correspond} to changes that are valid with respect to |a|.
% Changes |df : Dt^f| for a function |f : A -> B| have a dependent type |df : (a :
% A) -> Dt^a -> Dt^(f a)|, hence their input and output domains are restricted to
% \emph{only} contain ``valid'' changes. Based change sets are in some ways better
% behaved. However, |eval(derive t)| does not belong to any based change set, because
% it has the ``wrong'' domain, even though |eval(derive t)|, when applied to
% ``valid changes'', has in some sense the ``correct behavior''. More precisely,
% \ilcA{} introduces an incremental semantics |evalInc t| (different from the one in \ilcB{}), proves it
% has a ``correct behavior'', and shows that |eval(derive t)| has a behavior that ``matches''
% |evalInc t|. In turn, to make this precise, \ilcA{} defines formally when when a
% based change and a change have ``matching behaviors'' through a logical
% relation called \emph{erasure}: function change |df : (a : A) -> Dt^a -> Dt^(f
% a)| (with source |f : A -> B)| erases to erased change |df' : A -> Dt^A -> Dt^B|
% (written |erase f df df'|)
% if, given any change |da : Dt^a| with source |a| that erases to |da' : Dt^A|,
% output change |df a da : Dt^(f a)| erases to |df' a da' : Dt^B|.
% For base types, erasure simply connects corresponding |da' : Dt^a| with |da :
% Dt^A| in a manner dependent from the base type (often, just throwing away any
% embedded proofs of validity).
% This relation is called erasure because it goes from dependently-typed functions
% to non-dependently-typed functions. This style of relation resembles the ones
% used to show that a compiler produces outputs that relate to their inputs.
% Changes are then ``well-behaved'' if they are the erasure of a based
% change.\footnote{\citeauthor{CaiEtAl2014ILC} use different terminology: They say
% ``changes'' instead of ``based changes'', and ``erased changes'' instead of
% ``changes''. Here we change terms to use a single, consistent terminology.}

% \paragraph{Relating the two models}
% The two approaches have a different architecture, but reach similar results.
% In particular, they give the same definition and predict the same behavior for
% |eval(derive t)| in any example we are aware of.

% Based on a partial mechanized proof, we conjecture that a change is valid in
% \ilcB{} if and only if it is the erasure of a based change in \ilcA{}.

% We have sketched a mechanized proof of this conjecture, and have a partial proof
% for functions. To complete this proof, we would however need to combine the two
% definitions of change structures (the one in \ilcA{} using based change sets and
% the one in \ilcB{} using plain change sets), and show each operation mirrors the
% other one. For instance, we'd need proofs relating the different definitions of
% |`oplus`|, so that |erases a da da' -> a `oplus` da = a `oplus` da'|.
% We have not completed such proofs as of this writing.

% % We have also sketched a proof of our conjecture. However,

% % In this thesis we have given a novel semantic model of function changes.

% % In particular, we focus on change
% % validity for function spaces, and its role in the overall proof
% % of |derive(param)|'s correctness. Specifically, we compare
% % new-style valid function changes to old-style ones, and sketch in
% % which sense they are equivalent.

% We have seen that based function changes have type |df : (a : A) -> Dt^a ->
% Dt^(f a)|.
% However, based function changes have to also satisfy an additional
% equation called \emph{preservation of future}:\footnote{Name suggested by Yufei Cai.}
%   \[|f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da)|.\]
% This equation appears inelegant, and formal proofs were often complicated by the
% need to perform rewritings using it.
% If we replace |f1 `oplus` df| with |f2| and |a1 `oplus` da| with |a2|, this
% equation becomes |f1 a1 `oplus` df a1 da = f2 a2|, a consequence of |fromto f1
% df f2|. So one might suspect that valid function changes also satisfy this
% equation. We show this is indeed the case:

% % This equation is one requirement that old-style function changes
% % had to satisfy. What we have seen is that the new-style
% % definition of validity, although different (and we believe
% % simpler), implies the same equation.
% % First, we show that our valid function changes satisfy
% \begin{lemma}
%   A valid function change |fromto (A -> B) f1 df f2| satisfies equation
%   \[|f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da)|\]
%   on any valid input |fromto (A -> B) a1 da a2|.
% \end{lemma}
% Beware, however, this equation on changes is not actually equivalent to the same
% equation for based changes, since variables quantify over different sets (based
% change sets versus change sets) and since operators like |`oplus`| refer to
% different (though related) operations.

% Also beware the two models are unlikely to be isomorphic in any straightforward
% sense. Initially, we conjectured such an isomorphism would actually exist and
% tried defining it. Please keep in mind we work in a constructive setting, hence
% we tried defining a constructive isomorphism.
% %
% However, try converting a based function change |df' : Dt^f| with source |f : A
% -> B| to a valid function change |df : Dt^(A -> B) = \(a : A) (da : Dt^A) ->
% dt|. We would expect |dt| to compute |df' a da|, modulo a few conversions. But
% first, |da| need not be valid. We'd have to generate some output change anyway.
% We can pick |df a (nil a)|, or |nil (f a)|, or something else. But then, if
% |df'| results from converting a valid function change |df0|, |df| will not have
% the same behavior as |df0| on invalid changes. Hence, our conversion would not
% be an isomorphism.
% Worse, in a constructive and proof-relevant setting, we need to a decision
% procedure that given |a : A| and |da : Dt^A| produces either a proof that |da|
% is valid for |a|, or a proof that it is not valid. But validity might be
% undecidable in general, especially if |A| is in turn a set of functions.

% Overall, the relation between the two models is vaguely similar to the relation
% between two models of the same language: while their elements have different
% characteristics, they enable showing similar facts about the language (though
% not necessarily the same ones).

% % While that formulation has lots of conceptual elegance, programs
% % produced by |derive(param)| are expressed in STLC, which does not
% % support dependent types and cannot express proofs; hence
% % |derive(param)| cannot produce changes that are valid according
% % to \citeauthor{CaiEtAl2014ILC}. Instead,
% % \citeauthor{CaiEtAl2014ILC} need to give a separate semantics
% % mapping terms to their validity-embedding changes, and then
% % relate validity-embedding changes to the ``erased changes''
% % produced by |derive(param)|.\footnote{While we didn't realize
% %   back then, we could have probably reused the theory of
% %   realizability to perform erasure and extract the computational
% %   content from validity-embedding changes.} While this additional
% % step is not conceptually hard, mechanizing it took significant
% % work; moreover, dealing with both validity-embedding changes and
% % erased changes introduced significant inelegant noise in quite a
% % few definitions and theorem statements.

% % Using our formalization, we have also defined a type of
% % validity-embedding changes |Dt^v|, with elements that pair a
% % change and its validity proof:
% % \[|Dt^v = Sigma [ dv `elem` Dt^V ] valid v dv|.\]

% % However, such new-style validity-embedding changes are not
% % equivalent to old-style changes on function spaces, even if we
% % restrict our attention to valid inputs; we need one last step to
% % relate them together. Take an arbitrary function |f1 : A -> B|.
% % For \citeauthor{CaiEtAl2014ILC}, |df' : Dt^f1| means that |df'|
% % maps validity-embedding changes to validity-embedding changes;
% % for us, |df' : Dt^f1| means that |df'| contains (1) a map |df|
% % from changes to changes and (2) a proof that |df| preserves
% % validity: in a sense, new-style changes split what was a map of
% % validity-embedding changes into its action on changes and its
% % action on validity proofs. This ``splitting'' becomes trickier
% % for higher-order function types, such as |(A -> B) -> (C -> D)|,
% % so it must be defined by induction on types; essentially, we need
% % to adapt \citeauthor{CaiEtAl2014ILC}'s erasure.

% % We have not attempted a mechanization of the full equivalence,
% % but we have been satisfied with mechanizing several fragments
% % without further issues.

% \paragraph{Mechanization overhead}
% The mechanization of \ilcB{} appears simpler and
% smaller than the mechanization for \ilcA{}, because we avoid needing erasure,
% but also for other smaller simplifications.

% Most importantly, our fundamental relation is ``two-sided''
% (|fromto V v1 dv v2|) rather than ``one-sided'' (|valid V v dv| or |dv : Dt^v|);
% that is, validity specifies both the source and the destination
% explicitly. This is easier now that validity proofs are separate
% from changes. While this might seem trivial, it's somewhat
% significant for functions, especially in terms of mechanization
% overhead in Agda.
% %
% Indeed, \ilcB{} validity allows stating that |df : Dt^(A -> B)|
% is a change from |f1| to |f2|, instead of stating that |df| is a
% change from |f1| to |f1 `oplus` df = \a -> f1 a `oplus` df a (nil
% a)|. What's more, assume |fromto A a1 da a2|: according to
% \ilcB validity preservation, change |df a1 da| has
% destination |f2 a2|. Instead, according to \ilcA{} validity
% preservation, change |df a1 da| has destination |(f1 `oplus` df)
% (a1 `oplus` da)|, that is |f1 (a1 `oplus` da) `oplus` df (a1
% `oplus` da) (nil (a1 `oplus` da))|, which adds significant noise
% to mechanized proving with \ilcA definitions.

% \subsection{Further alternatives and related work}
% %\paragraph{Possible alternatives and related work}
% \paragraph{Junkless models}
% Change sets in \ilcB{} contain invalid elements, or \emph{junk}
% A model without junk, like \ilcA{}, can be desirable.\pg{Can it?}
% We conjecture we could combine
% the benefits of the two models by defining change sets indexed from both sides:

% |Dt2 (A -> B) f1 f2 = Dt2 A a1 a2 -> Dt2 B (f1 a1) (f2 a2)|.

% One could then define a set of valid changes containing their source and
% destination:

% |Dt^V = exists v1 : V, v2 : V. ^^ Dt2^V v1 v2|.

% In this approach, |Dt^(A -> B)| is not a set of functions, but we can still
% define an operation that applies an element of |Dt^(A -> B)| to an element of
% |Dt^A| and produces an element of |Dt^B|.

% We believe the main open question is not whether defining such a model is
% possible, but about the formalization overhead and their exact properties.

% Such junkless models are closely related to models based on directed graphs and reflexive
% graphs, where values are graphs vertexes, changes are edges between change
% source and change destination (as hinted earlier). In graph language, validity
% preservation means that function changes are graph homomorphisms.

% Based on similar insights, \citet{Atkey2015ILC} suggests modeling ILC using
% reflexive graphs, which have been used to construct parametric models for System
% F and extensions, and calls for research on the relation between ILC and
% parametricity.
% As a follow-up work \citet{CaiPhD} studies models of ILC based on directed and
% reflexive graphs.

% In ILC, instead, |fromto V v1 dv v2| holds even if |v1| and |v2| are different
% and this difference is observable in the program, but require that |dv| is a
% correct description of these differences.

% Similarly to our proof, \citet*{Acar08} prove correctness of incrementalization
% using a logical relation across executions of programs on base and updated
% inputs. There, incremental computation proceeds by executing the same program
% using an incremental semantics.
% The proof is done on an untyped language using a step-indexed logical relation,
% and authors choose to use a step-indexed big-step semantics, where the
% step-indexing is sound relative to step counts for a standard small-step
% semantics.
% Based on a few preliminary
% experiments by me and Yann Régis-Gianas, we conjecture it should be possible to
% adapt the approach to step-indexing in that proof to give a correctness proof of
% ILC on an untyped language using an operational semantics.

% \Citeauthor*{Acar08}'s step-indexed logical relation for incremental computation
% resembles the step-indexed logical relation by \citet{Ahmed2006stepindexed} to
% model parametricity and program equivalence.
% However, if terms |t1| and |t2| are
% related according to \citeauthor*{Ahmed2006stepindexed}'s program equivalence
% (at a certain step count) and |t1| terminates (at certain step counts), then
% |t2| terminates and |t1| and |t2|'s results are related (at a certain step count).
% Instead, if terms |t1| and |t2| are related according to \citeauthor*{Acar08}'s
% relation (at a certain step count),
% |t1| terminates (at certain step counts) \emph{and} |t2| terminates,
% \emph{then} |t1| and |t2|'s results are related (at a certain step count).%
% \footnote{The step-indexing details we omit are the same in both definitions.}
% That is, with \citeauthor*{Acar08}'s logical relation, termination of |t1| in no
% way implies termination of |t2|, exactly because |t1| and |t2| need not be
% equivalent.

% Let us see concretely why a logical relation for incrementalization must relate |t1|
% and |t2| even if they are not equivalent and in particular |t1| terminates and |t2|
% doesn't. Consider incrementalizing function |t = if x then 0 else loop| when |x|
% goes from |true| to |false|, assuming that |loop| is a diverging subterm. Such a
% change for |x| is valid, hence it must be mapped (by function application and
% $\beta$-reduction) to a valid change from terminating term |if true then 0 else
% loop| to non-terminating term |if false then 0 else loop|.

% \section{The relation with parametricity and the abstraction theorem}

% In this section we discuss similarities between correctness of |derive(param)|
% (\cref{thm:derive-correct}) and the fundamental property of logical relations,
% for the case of binary logical relations. This section is intended for logical
% relation experts, and we keep it rather informal.

% %format ppp(t) = "\mathcal{P}(" t ")"

% Most studies of logical relations mention no term transformation that relates to
% |derive(param)|; one exception is given by \citet{Bernardy2011realizability}.
% They study relational parametricity, a particular binary logical relation, where
% the fundamental property of logical relations becomes the abstraction theorem. To
% prove the abstraction theorem, \citeauthor{Bernardy2011realizability} present a
% term transformation |ppp(param)|; we'll show the analogy between this term
% transformation and
% |derive(param)|.%
% %
% \footnote{\citeauthor{Bernardy2011realizability} were not the first to introduce
%   such a transformation, but we base our comparison off their presentation and
%   avoid discussing their related work.}

% Transformation |ppp(t)| takes a term |t| to a proof term |ppp(t)| in a suitable
% object logic (related to the one of |t|), that proves that |t| maps logically
% related inputs to logically related outputs. For binary logical relations and
% simply-typed $\lambda$-calculus, we can specialize their definition to the
% following:

% %format (idx1 (t)) = "\mathcal{S}_1(" t ")"
% %format (idx2 (t)) = "\mathcal{S}_2(" t ")"

% \begin{code}
%   (t1, t2) `elem` r(sigma -> tau) =
%     forall x1 x2 : sigma, px : (x1, x2) `elem` r(sigma). (t1 x1, t2 x2) `elem` r(tau)
%   ppp(x) =
%       px
%   ppp(\(x : sigma) -> t) =
%     \(x1 x2 : sigma) (px : (x1, x2) `elem` r(sigma)) -> ppp(t)
%   ppp(s t) =
%     ppp(s) (idx1 s) (idx2 s) ppp(t)
% \end{code}

% where |idx1 s| and |idx2 s| subscript variables in terms with 1 and 2:
% \begin{code}
%   idx1(x) = x1
%   idx1(\(x : sigma) -> t) = \(x1 : sigma) -> idx1 t
%   idx1(s t) = (idx1 s) (idx1 t)

%   idx2(x) = x2
%   idx2(\(x : sigma) -> t) = \(x2 : sigma) -> idx2 t
%   idx2(s t) = (idx2 s) (idx2 t)
% \end{code}

% To see the analogy, let's show a variant of differentiation. This time,
% |derive(\x -> t) = \x1 x2 dx -> derive(t)| is a function that binds not just the
% source of |dx|, but also its target, and the additional symmetry simplifies its
% theoretical study.

% \begin{code}
%   Dt2 : (v1 v2 : V)
%   Dt2 : (v1 v2 : V) -> Set
%   Dt2 v1 v2 = Sigma [ dv `elem` Dt^V ] (fromto sigma v1 dv v2)
%   (f1, df, f2) `elem` r(sigma -> tau) =
%     forall x1, dx, x2 : sigma, dxx : r(sigma) . (f1 x1, df x1 x2 dx, f2 x2) `elem` r(tau)

%   derive(x) = dx
%   derive(\(x : sigma) -> t) = \x1 x2 (dx : Dt2 x1 x2) -> derive(t)
%   derive(s t) = derive(s) (idx1 s) (idx2 s) (derive t)

%   derive(\(x : sigma) -> t) = \x1 x2 (fromto sigma x1 dx x2) -> derive(t)
% \end{code}

% \pg{connection}
% For readers familiar with staging,
% we explain how \citeauthor{Bernardy2011realizability}'s
% transformation relates to standard proofs of the abstraction theorem.
% In short, (a) the usual proof of the abstraction theorem
% can be regarded as an \emph{interpreter} from object-level terms to metalevel
% proofs; (b) standard interpreters can be turned into compilers by staging, so
% that they evaluate object-level code for a function instead of the function
% itself at the metalevel; (c) an ``interpreter'' that produces a metalevel proof
% can be staged into a ``compiler'' (or term transformation) into an object-level
% proof term in a suitable logic; (d) the above definition of |p(t)| corresponds
% (informally) to staging the proof of the abstraction theorem.
% \begin{enumerate}
% \item Recall that the abstraction theorem is proven by
% induction on terms.\footnote{Or on typing derivations, but as discussed we
%   regard the two as isomorphic, since typing is syntax-directed.} Let's write
% |P(t)| to say that term |t| satisfies the abstraction theorem; then the theorem
% statement is |forall t. P(t)| in the metalevel logic. The proof is constructive,
% so we can regard it (informally) under the lens of the Curry-Howard isomorphism.
% Under this lens, a metalevel proof of |forall t. P (t)| is a function from terms
% |t| to a metalevel proof of |P(t)|; a proof by induction is a structurally
% recursive function from terms to metalevel proofs, just like an interpreter is a
% structural recursive function from terms to metalevel functions. Hence, we
% regard the proof of the abstraction theorem as an interpreter.
% \item Staging an interpreter produces a compiler, which evaluates
%   not to a value |v| but to code that will later evaluate to
%   value |v|; this code will already be specialized for the input
%   term.
% \item Similarly, by staging an interpreter that produces proofs,
%   we produce a compiler from term to proofs.
% \end{enumerate}

% % Most other proofs,
% % instead of creating a proof term, but simply produce a similar proof in the meta
% % logic by induction on terms. The two proof strategies are related by an analogue
% % of staging.


% % Here we discuss the relation with parametricity, the abstraction theorem, and
% % the fundamental property of logical relations, for readers familiar with these
% % topics. Parametricity is typically studied for type systems containing System F,
% % but \citet{Bernardy2011realizability} generalize it to arbitrary PTSs.



% % Correctness of |derive(param)| (\cref{thm:derive-correct}) relates to binary
% % parametricity. However, usual statements of binary parametricity mention no
% % analog of changes or |derive(param)|. One defines a relational interpretation of
% % terms, mapping input relations to output relations, and shows this maps

\section{Chapter conclusion}
In this chapter, we have sketched how to define and prove correct
differentiation following \citet{Bernardy2011realizability}'s and
\citet{Bernardy10}'s work on
parametricity by code transformation. We give no formal correctness proof, but
proofs appear mostly an extension of their methods. An important open point is
\cref{rem:validity-oplus-system-f-not-really}.
We have implemented and tested differentiation in an existing mature PTS
implementation, and verified it is type-correct on a few typical terms.

We leave further investigation as future work.
