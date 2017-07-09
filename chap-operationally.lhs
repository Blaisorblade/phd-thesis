% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{(Un)typed ILC, operationally}
\label{ch:bsos}

In \cref{ch:derive-formally} we have proved ILC correct for a
simply-typed $\lambda$-calculus. What about other languages, with more expressive
type systems or no type system at all?

In this chapter, we prove that ILC is still correct in untyped
call-by-value (CBV) $\lambda$-calculus. We do so without using
denotational semantics, but using only an environment-based
big-step operational semantics and \emph{step-indexed logical
relations}. The formal development in this chapter stands alone
from the rest of the thesis, though we do not repeat ideas
present elsewhere.

We prove ILC correct using, in increasing order of complexity,
\begin{enumerate}
\item STLC and standard syntactic logical relations;
\item STLC and step-indexed logical relations;
\item an untyped $\lambda$-calculus and step-indexed logical relations.
\end{enumerate}
We have fully mechanized the second proof in Agda\footnote{Source code available
in this GitHub repo: \url{https://github.com/inc-lc/ilc-agda}.}, and done the
others on paper. In all cases we prove the fundamental property for
validity; we detail later which corollaries we prove in which
case.
The proof for untyped $\lambda$-calculus is the most
interesting, but the others can serve as stepping stones. We are
currently working (together with Yann Régis-Gianas) on
mechanizing the proof for untyped $\lambda$-calculus in
Coq.\footnote{Mechanizing the proof for untyped
  $\lambda$-calculus is harder for purely technical reasons:
  mechanizing well-founded induction in Agda is harder than
  mechanizing structural induction.}

Using operational semantics and step-indexed logical relations
simplifies extending the proofs to more expressive languages,
where denotational semantics or other forms of logical relations
would require more sophistication, as argued by
\citet{Ahmed2006stepindexed}.

Proofs by (step-indexed) logical relations also promise to be
scalable. All these proofs appear to be slight variants of
proof techniques for logical program equivalence and
parametricity, which are well-studied topics, suggesting the
approach might scale to more expressive type systems. Hence, we
believe these proofs clarify the relation with parametricity that
has been noticed earlier \citep{Atkey2015ILC}. However, actually
proving ILC correct for a polymorphic language (such as System F)
is left as future work.

We also expect that from our logical relations, one might derive a logical
\emph{partial equivalence relation} among changes, similarly to
\cref{sec:change-equivalence}, but we leave a development for future work.

Compared to earlier chapters, this one will be more technical and
concise, because we already introduced the ideas behind both ILC
and logical relation proofs.

\paragraph{Binding and environments}
On the technical side, we are able to mechanize our proof without
needing any technical lemmas about binding or weakening, thanks
to a number of choices we mention later.

Among other reasons, we avoid lemmas on binding because instead of substituting
variables with arbitrary terms, we record mappings from variables to closed
values via environments. We also used environments in \cref{sec:preliminaries},
but this time we use syntactic values rather than semantic ones.
As a downside, on paper, using environments makes for
more and bigger definitions, because we need to carry around both an environment
and a term, instead of merging them into a single term via substitution, and
because values are not a subset of terms but an entirely separate category.
But on paper the extra work is straightforward, and in a mechanized setting it
is simpler than substitution, especially in a setting with an intrinsically
typed term representation (see \cref{sec:sem-style-and-rw}).

\paragraph{Background/related work}
Our development is inspired significantly by the use of
step-indexed logical relations by \citet{Ahmed2006stepindexed}
and \citet*{Acar08}. We refer to
those works and to Ahmed's lectures at OPLSS 2013%
\footnote{\url{https://www.cs.uoregon.edu/research/summerschool/summer13/curriculum.html}.}
for an introduction to (step-indexed) logical relations.

\paragraph{Intensional and extensional validity}
Until this point, change validity only specifies how function
changes behave, that is, their \emph{extension}.
Using operational semantics, we can specify how valid function
changes are concretely defined, that is, their \emph{intension}.
To distinguish the two concepts, we contrast extensional validity
and intensional validity.
Some extensionally valid changes are not intensionally valid, but
such changes are never created by derivation.
Defining intensional validity helps to understand function
changes:
function changes are produced from changes to values in
environments or from functions being replaced altogether.
Requiring intensional validity helps to implement
change operations such as |`oplus`| more efficiently, by
operating on environments.
Later, in \cref{ch:defunc-fun-changes},
we use similar ideas to implement change operations on
\emph{defunctionalized} function changes: intensional validity
helps put such efforts on more robust foundations, even though we
do not account formally for defunctionalization but only for
the use of closures in the semantics.

We use operational semantics to define extensional validity in
\cref{sec:typed-proof} (using plain logical relations) and
\cref{sec:silr-typed-proof} (using step-indexed logical
relations). We switch to intensional validity definition in
\cref{sec:intensional-step-indexed-validity}.

% Thanks to operational semantics, we can choose to define change
% validity \emph{intensionally} rather than \emph{extensionally},
% that is, based on how changes are defined internally, rather than
% just how they behave.

% Our earlier definition of validity is based on behavior, hence
% \emph{extensional}. We present a step-indexed definition of
% extensional validity in \cref{sec:silr-typed-proof}.
% We introduce a concept of intensional validity, that captures
% formally that function changes arise from changing environments
% or functions being replaced altogether
% (\cref{sec:intensional-step-indexed-validity}).
% which introduces
% intensional validity as a variant of extensional validity,
% defined in

% According to earlier definitions, functions
% We earlier defined va
% Also, using operational semantics, we can show more formally how
% function changes arise: we model function values as closures, and
% in the model we show in
% \cref{sec:intensional-step-indexed-validity}, function change
% values are either closure changes (which only modify
% environments) or replacement closures, that is replacement
% changes for closures that produce replacement changes as result.

\paragraph{Non-termination and general recursion}
This proof implies correctness of ILC in the presence of general recursion,
because untyped $\lambda$-calculus supports general recursion via
fixpoint combinators. However, the proof only applies to
terminating executions of base programs, like for earlier
authors~\citep*{Acar08}: we prove that if a function terminates
against both a base input |v1| and an updated one |v2|, its derivative
terminates against the base input and a valid input change |dv|
from |v1| to |v2|.

We can also add a fixpoint construct to
our \emph{typed} $\lambda$-calculus and to our mechanization,
without significant changes to our relations. However, a
mechanical proof would require use of well-founded induction,
which our current mechanization avoids.
We return to this point in \cref{sec:bos-fixpoints}.

While this support for general recursion is effective in some
scenarios, other scenarios can still be incrementalized better
using structural recursion.
More efficient support for general recursion is
a separate problem that we do not tackle here and leave for
future work. We refer to discussion in
\cref{sec:general-recursion}.

\paragraph{Correctness statement}
Our final correctness theorem is a variant of
\cref{thm:derive-correct-oplus}, that we repeat for comparison:

\begin{fullCompile}
\deriveCorrectOplus*
\end{fullCompile}
\begin{partCompile}
\begin{restatable*}[|derive(param)| is correct, corollary]{corollary}{deriveCorrectOplus}
  \label{thm:derive-correct-oplus}
  If |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |eval(t) rho1 `oplus` eval(derive(t)) drho = eval(t) rho2|.
\end{restatable*}
\end{partCompile}

We present our final correctness theorem statement in
\cref{sec:intensional-step-indexed-validity}. We anticipate it
here for illustration: the new statement is more explicit about
evaluation, but otherwise broadly similar.

\begin{restatable*}[|derive(param)| is correct, corollary]{corollary}{deriveCorrectOplusSI}
  \label{thm:derive-correct-types-si-intensional}
  Take any term |t| that is well-typed (|Gamma /- t : tau|) and
  any suitable environments |rho1, drho, rho2|, intensionally
  valid at any step count (|forall k. (k, rho1, drho, rho2) `elem`
  envset Gamma|).
  Assume |t| terminates in both the old environment |rho1| and
  the new environment |rho2|, evaluating to output values |v1| and
  |v2| (|bseval t rho1 v1| and |bseval t rho2 v2|).
  Then |derive t| evaluates in environment |rho| and change environment |drho|
  to a change value |dv| (|dbseval t rho1 drho dv|),
  and |dv| is a valid change from |v1| to |v2|, so that |v1
  `oplus` dv = v2|.
\end{restatable*}

Overall, in this chapter we present the following contributions:
\begin{itemize}
\item We give an alternative presentation of derivation, that can
  be mechanized without any binding-related lemmas, not even
  weakening-related ones, by introducing a separate syntax for
  change terms (\cref{sec:bsos-formalization}).
\item We prove formally ILC correct for STLC
  using big-step semantics and logical relations (\cref{sec:typed-proof}).
\item We show formally (with pen-and-paper proofs) that our
  semantics is equivalent to small-step semantics definitions
  (\cref{sec:sanity-check-big-step}).
\item We introduce a formalized step-indexed variant of our definitions and
  proofs for simply-typed $\lambda$-calculus
  (\cref{sec:typed-proof}), which scales directly to definitions
  and proofs for \emph{untyped} $\lambda$-calculus.
\item For typed $\lambda$-calculus, we also mechanize our
  step-indexed proof.
\item In addition to (extensional) validity, we introduce a
concept of intensional validity, that captures formally that
function changes arise from changing environments or functions
being replaced altogether
(\cref{sec:intensional-step-indexed-validity}).
\end{itemize}

\section{Formalization}
\label{sec:bsos-formalization}
To present the proofs, we first describe our formal model of CBV
ANF $\lambda$-calculus.
We define an untyped ANF language, called |ilcUntau|.
We also define a simply-typed variant, called |ilcTau|, by adding on top
of |ilcUntau| a separate Curry-style type system.

In our mechanization of |ilcTau|, however, we find it more
convenient to define a Church-style type system (that
is, a syntax that only describes typing derivations for
well-typed terms) separately from the untyped language.

Terms resulting from differentiation satisfy additional
invariants, and exploiting those invariants helps simplify the
proof. Hence we define separate languages for change terms
produced from differentiation, again in untyped (|dilcUntau|) and
typed (|dilcTau|) variants.

The syntax is summarized in \cref{fig:anf-lambda-calculus}, the
type systems in \cref{fig:anf-lambda-calculus-typing}, and the
semantics in \cref{fig:anf-lambda-calculus-semantics}. The base
languages are mostly standard, while the change languages pick a
few different choices.

\input{fig-syntactic-ilc}

\subsection{Types and contexts}
\label{sec:bsos-anf-types}
%
We show the syntax of types, contexts and change types in
\cref{sfig:anf-types}.
We introduce types for functions, binary products and naturals.
Tuples can be encoded as usual through nested pairs.
Change types are mostly like earlier, but this time we use
naturals as change for naturals (hence, we cannot define a total
|`ominus`| operation).

We modify the definition of change contexts and environment
changes to \emph{not} contain entries for base values: in this
presentation we use separate environments for base variables and
change variables. This choice avoids the need to define weakening
lemmas.

\subsection{Base syntax for \ilcUntau}
\label{sec:bsos-anf-syntax}
For convenience, we consider a $\lambda$-calculus in
A-normal form. We do not parameterize this calculus over language
plugins to reduce mechanization overhead, but we define separate syntactic
categories for possible extension points.

We show the syntax of terms in \cref{sfig:anf-syntax}.

Meta-variable |v| ranges over (closed) syntactic values, that is
evaluation results. Values are numbers, pairs of values or
closures. A closure is a pair of a function and an environment as
usual.
Environments |rho| are finite maps from variables to syntactic
values; in our mechanization using de Bruijn indexes,
environments are in particular finite lists of syntactic values.

Meta-variable |t| ranges over arbitrary terms and |w|
ranges over neutral forms. Neutral forms evaluate to values in
zero steps, but unlike values they can be open: a neutral form is
either a variable, a constant value |c|, a $\lambda$-abstraction or a
pair of neutral forms.

A term is either a neutral form, an application of neutral forms,
a let expression or an application of a primitive function |p| to
a neutral form. Multi-argument primitives are encoded as
primitives taking (nested) tuples of arguments. Here we use
literal numbers as constants and +1 and addition as primitives (to illustrate
different arities), but further primitives are possible.

\begin{notation}
  We use subscripts ${}_a {}_b$ for pair components, ${}_f {}_a$ for
  function and argument, and keep using ${}_1 {}_2$ for old and new
  values.
\end{notation}
\subsection{Change syntax for \dilcUntau}
\label{sec:bsos-anf-change-syntax}
Next, we consider a separate language for change terms, which can
be transformed into the base language. This language supports
directly the structure of change terms: base variables and change
variables live in separate namespaces. As we show later, for the typed language
those namespaces are represented by typing contexts |Gamma| and
|Dt^Gamma|: that is, the typing context for change variables is
always the change context for |Gamma|.

We show the syntax of change terms in \cref{sfig:anf-change-syntax}.

Change terms often take or bind two parameters at once, one for a
base value and one for its change.
Since a function change is applied to a base input
and a change for it at once, the syntax for change term has a
special binary application node |dwf wa dwa|; otherwise, in ANF,
such syntax must be encoded through separate applications via
|lett dfa = dwf wa in dfa dwa|. In the same way, closure changes
|rho `stoup` drho[\x dx -> dt]| bind two variables at once and
close over separate environments for base and change variables.
Various other changes in the same spirit simplify similar
formalization and mechanization details.

% In particular, values for
% function changes are again closures, but we require they bind
% two variables at the out
%
In change terms, we reuse primitives to stand for their
derivatives. The semantics evaluates the derivatives of
primitives correctly.
While strictly speaking differentiation \emph{must} map
primitives to standard terms, so that the resulting programs can
be executed by a standard semantics, doing so in a new
formalization yields little additional insight, and requires
writing concrete derivatives of primitives as de Bruijn terms.

\subsection{Differentiation}
\label{sec:bsos-anf-derive}
We show differentiation in \cref{sfig:anf-derive}.
Differentiation maps constructs in the language of base terms
one-to-one to constructs in the language of change terms.

\subsection{Typing \ilcTau{} and \dilcTau}
\label{sec:bsos-anf-typing}

We define typing judgement for |ilcTau| base terms and for |dilcTau| change
terms. We show typing rules in
\cref{sfig:anf-change-typing}.

Typing for base terms is mostly standard. We use judgements |`vdashPrim` p| and
|`vdashConst` c| to specify typing of primitive functions and constant values.
%
For change terms, one could expect a type system only proving
judgements with shape |Gamma, Dt^Gamma /- dt : Dt^tau| (where
|Gamma, Dt^Gamma| stands for the concatenation of |Gamma| and
|Dt^Gamma|). To simplify inversion on such judgements (especially
in Agda), we write instead |Gamma /-- dt : tau|, so that
one can verify the following derived typing rule for |derive|:
\begin{typing}
  \Rule[T-Derive]
  {|Gamma /- t : tau|}
  {|Gamma /-- derive t : tau|}
\end{typing}

We also use mutually recursive typing judgment |//= v : tau| for values and |//=
rho : Gamma| for environments, and similarly |//== dv : tau| for change values
and |//== drho : Gamma| for change environments.
We only show the (unsurprising) rules for |//= v : tau| and omit the others. One
could alternatively and equivalently define typing on syntactic values |v| by
translating them to neutral forms |w = v*| (using unsurprising definitions in
\cref{sec:sanity-check-big-step}) and reusing typing on terms, but as usual we
prefer to avoid substitution.
\begin{typing}
\Axiom[TV-Nat]{|//= n : Nat|}

\Rule[TV-Pair]
  {|//= va : taua|\\
  |//= vb : taub|}
  {|//= pair va vb : taua `times` taub|}

\raisebox{0.5\baselineskip}{\fbox{|//= v : tau|}}

\Rule[TV-Lam]
{|Gamma , x : sigma /- t : tau|\\
  |//= rho : Gamma|}
{|//= rho[\x -> t] : sigma -> tau|}
\end{typing}

\subsection{Semantics}
\label{sec:bsos-anf-semantics}
We present our semantics for base terms in \cref{sfig:anf-base-semantics}.
Our semantics gives meaning to pairs of a environment |rho| and term |t|,
consistent with each other, that we write |envpair rho t|. By ``consistent'' we mean that
|rho| contains values for all free variables of |t|, and (in a typed language)
values with compatible values (if |Gamma /- t : tau| then |//= rho : Gamma|).
Judgement |envpair rho t (downto n) v| says that |envpair rho t| evaluates to
value |v| in |n| steps. The definition is given via a CBV big-step semantics.
Following \citet*{Acar08}, we index our evaluation judgements via a step count,
which counts in essence $\beta$-reduction steps; we use such step counts later,
to define step-indexed logical relations.
Since our semantics uses environments, $\beta$-reduction steps are implemented
not via substitution but via environment extension, but the resulting
step-counts are the same (\cref{sec:sanity-check-big-step}).
Applying closure |vf = rho'[\x -> t]| to argument |va| produces environment-term
pair |envpair ((rho', x := va)) t|, which we abbreviate as |vapply vf va|. We'll
reuse this syntax later to define logical relations.

In our mechanized formalization, we have additionally proved
lemmas to ensure that this semantics is sound relative to our
earlier denotational semantics (adapted for the ANF syntax).

Evaluation of primitives is delegated to function |evalPrim|. We show
complete equations for the typed case; for the untyped case, we
must turn |evalPrim| and |devalPrim| into relations (or add explicit error
results), but we omit the standard details (see also
\cref{sec:silr-untyped-proof}).

For simplicity, we assume evaluation of primitives takes one step.
We conjecture higher-order primitives might need to be assigned
different costs, but leave details for future work.

We can evaluate neutral forms |w| to syntactic values |v| using a simple
evaluation function |evalVal w rho|, and use |evalPrim p v| to
evaluate primitives.
When we need to omit indexes, we write |bseval t rho v| to mean
that for some |n| we have |ibseval t rho n v|.

We can also define an analogous non-indexed big-step
semantics for change terms, and we present it in \cref{sfig:anf-change-semantics}.

\subsection{Type soundness}
\label{sec:bsos-anf-soundness}

Evaluation preserves types in the expected way.
\begin{lemma}[Big-step preservation]
  \begin{enumerate}
  \item If |Gamma /- t : tau|, |//= rho : Gamma| and |ibseval t rho n v| then
|//= v : tau|.
\item If |Gamma /-- dt : tau|, |//= rho : Gamma|, |//== drho : Gamma| and
|dbseval dt rho drho dv| then |//== dv : tau|.
   \end{enumerate}
\end{lemma}
\begin{proof}
  By structural induction on evaluation judgements. In our intrinsically typed
  mechanization, this is actually part of the definition of values and big-step
  evaluation rules.
\end{proof}

To ensure that our semantics for \ilcTau{} is complete for the typed language,
instead of proving a small-step progress lemma or extending the semantics with
errors, we just prove that all typed terms normalize in the standard way.
As usual, this fails if we add fixpoints or for untyped terms. If we wanted to
ensure type safety in such a case, we could switch to functional big-step
semantics or definitional interpreters~\citep{Amin2017,Owens2016functional}.

\begin{theorem}[CBV normalization]
  \label{thm:bsos-normalization}
For any well-typed and closed term |/- t : tau|, there exist a step count |n| and value |v| such that |/- t (downto n) v|.
\end{theorem}
\begin{proof}
A variant of standard proofs of normalization for STLC~\citep[Ch.
12]{Pierce02TAPL}, adapted for big-step semantics rather than small-step
semantics (similarly to \cref{sec:typed-proof}).
We omit needed definitions and refer interested readers to our Agda
mechanization.
\end{proof}

We haven't attempted to prove this lemma for arbitrary change terms (though we
expect we could prove it by defining an erasure to the base language and
relating evaluation results), but we prove it for the result of differentiating
well-typed terms in \cref{thm:bsos-derive-normalization}.

\section{Validating our step-indexed semantics}
\label{sec:sanity-check-big-step}
In this section, we show how we ensure the step counts in our
base semantics are set correctly, and how we can relate this
environment-based semantics to more conventional semantics, based
on substitution and/or small-step. We only
consider the core calculus, without primitives, constants and
pairs. Results from this section are not needed later and we have
proved them formally on paper but not mechanized them, as our
goal is to use environment-based big-step semantics in our
mechanization.

To this end we relate our semantics first with
a big-step semantics based on substitution (rather than
environments) and then relating this alternative semantics to a
small-step semantics. Results in this section are useful to
understand better our semantics and as a design aide to modify
it, but are not necessary to the proof, so we have not mechanized
them.

As a consequence, we also conjecture that our logical relations
and proofs could be adapted to small-step semantics, along the lines
of \citet{Ahmed2006stepindexed}. We however do
not find that necessary. While small-step
semantics gives meaning to non-terminating programs, and that is
important for type soundness proofs, it does not seem useful (or
possible) to try to incrementalize them, or to ensure we do so
correctly.

In proofs using step-indexed logical relations, the use of
step-counts in definitions is often delicate and tricky to get
right.
But \citeauthor*{Acar08} provide a robust recipe to ensure
correct step-indexing in the semantics.
To be able to prove the fundamental property of logical relations,
we ensure step-counts agree with the ones induced by small-step
semantics (which counts $\beta$-reductions). Such a lemma is not
actually needed in other proofs, but only useful as a sanity
check.
We also attempted using the style of step-indexing
used by \citet{Amin2017}, but were unable to produce a proof. To
the best of our knowledge all proofs using step-indexed logical
relations, even with functional big-step semantics
\citep{Owens2016functional}, use step-indexing that agrees with
small-step semantics.

Unlike \citeauthor*{Acar08} we use environments in our big-step
semantics; this avoids the need to define substitution in our
mechanized proof. Nevertheless, one can show the two semantics
correspond to each other.
Our environments |rho| can be regarded as closed value
substitutions, as long as we also substitute away environments in values.
Formally,
we write |star rho t| for the ``homomorphic extension'' of
substitution |rho| to terms, which produces other terms.
If |v| is a value using environments, we write |w = starv v| for the
result of translating that value to not use environments; this
operation produces a closed neutral form |w|. Operations |star
rho t| and |starv v| can be defined in a mutually recursive way:
\begin{align*}
  |star rho x| &= |starv (rho(x))|\\
  |star rho (\x -> t)| &= |\x -> star rho t|\\
  |star rho (w1 w2)| &= |(star rho w1) (star rho w2)|\\
  |star rho (lett x = t1 in t2)| &= |lett x = star rho t1  in star rho t2|\\
  \\
  |starv (rho[\x -> t])| &= |\x -> star rho t|
\end{align*}
If |ibseval t rho n v| in our semantics,
a standard induction over the derivation of |ibseval t rho n v|
shows that |ibseval' (star rho t) n (starv v)|
%$|star rho t| \Downarrow_n |starv v|$
in a more conventional big-step
semantics using substitution rather than environments (also
following \citeauthor*{Acar08}):

\begin{typing}
  \Axiom[Var']{|ibseval' x 0 x|}

  \Axiom[Lam']{|ibseval' (\x -> t) 0 (\x -> t)|}

  \Rule[App']{
    |ibseval' (t[x := w2]) n w'|}
  {|ibseval' ((\x -> t) w2) (1 + n) w'|}

  \Rule[Let']{|ibseval' t1 n1 w1|\\
    |ibseval' (t2[x := w1]) n2 w2|}
  {|ibseval' (lett x = t1 in t2) (1 + n1 + n2) w2|}
\end{typing}
In this form, it is more apparent that the step indexes count
steps of $\beta$-reduction or substitution.

It's also easy to see that this big-step semantics agrees with a
standard small-step semantics $\mapsto$ (which we omit):
if |ibseval' t n w| then $|t| \mapsto^{n} |w|$.
Overall, the two statements can be composed, so our original
semantics agrees with small-step semantics:
if |ibseval t rho n v| then |ibseval' (star rho t) n (starv v)|
and finally
$|star rho t| \mapsto^{n} |starv v|$.
Hence, we can translate evaluation derivations using big-step
semantics to derivations using small-step semantics \emph{with
  the same step count}.

However, to state and prove the fundamental property we need not
prove that our semantics is sound relative to some other
semantics. We simply define the appropriate logical relation for
validity and show it agrees with a suitable definition for |`oplus`|.

Having defined our semantics, we proceed to define extensional validity.

\section{Validity, syntactically (\ilcTau{}, \dilcTau)}
\label{sec:typed-proof}
For our typed language |ilcTau|, at least as long as we do not add
fixpoint operators, we can define logical
relations using big-step semantics but without using
step-indexes. The resulting relations are well-founded only
because they use structural recursion on types.
We present in \cref{fig:big-step-validity-ext-nosi}
the needed definitions as a stepping stone to the
definitions using step-indexed logical relations.

Following \citet{Ahmed2006stepindexed} and \citet*{Acar08}, we
encode extensional validity
through two mutually recursive type-indexed families of ternary
logical relations, |valset tau| over closed values and |compset
tau| over terms (and environments).

These relations are analogous to notions we considered earlier
and express similar informal notions.
\begin{itemize}
\item With denotational semantics, we write |fromto tau v1 dv v2| to say
  that change value |dv `elem` eval(Dt^tau)| is a valid change from
  |v1| to |v2| at type |tau|. With operational semantics instead we
  write |(v1, dv, v2) `elem` valset tau|, where |v1|, |dv| and |v2|
  are now closed syntactic values.
\item For terms, with denotational semantics we write |fromto tau (eval
  t1 rho1) (eval dt drho) (eval t2 rho2)| to say that |dt| is a
  valid change from |t1| and |t2|, considering the respective
  environments. With operational semantics instead we write
  |(envpair rho1 t1, denvpair rho drho dt, envpair rho2 t2) `elem` compset tau|.
\end{itemize}

Since we use Church typing and only mechanize typed terms, we
must include in all cases appropriate typing assumptions.

Relation |compset tau| relates tuples of environments and
computations,
|envpair rho1 t1|, |denvpair rho drho dt| and |envpair rho2 t2|: it holds
if |t1| evaluates in environment |rho1| to |v1|,
and |t2| evaluates in environment |rho2| to |v2|, then
|dt| must evaluate in environments |rho| and |drho| to a change
value |dv|, with |v1, dv, v2| related by |valset tau|.
The environments themselves need not be related: this definition
characterizes validity \emph{extensionally}, that is, it can relate
|t1|, |dt| and |t2| that have unrelated implementations and
unrelated environments---in fact, even unrelated typing contexts.
This flexibility is useful to when relating closures of type
|sigma -> tau|: two closures might be related even if they have
close over environments of different shape. For instance,
closures |v1 = emptyRho[\x -> 0]| and |v2 = (y := 0)[\x -> y]| are
related by a nil change such as |dv = emptyRho[\x dx -> 0]|.
In \cref{sec:intensional-step-indexed-validity}, we discuss instead
an \emph{intensional} definition of validity.

In particular, for function types the relation |valset (sigma ->
tau)| relates function values |f1|, |df| and |f2| if they map
\emph{related input values} (and for |df| input changes) to
\emph{related output computations}.

We also extend the relation on values to environments via |envset
Gamma|: environments are related if their corresponding entries
are related values.
\begin{figure}[h!]
\begin{align*}
  |valset Nat| ={}& \{|(n1, dn, n2) `such` n1, dn, n2 `elem` Nat `wand` n1 + dn = n2|\}\\
  |valset (taua `times` taub)| ={} & \{|(pair va1 vb1, pair dva dvb, pair va2 vb2) `such` ^^^
                                   ^&^ (va1, dva, va2) `elem` valset taua
                                      ^^ `wand` ^^
                                      (vb1, dvb, vb2) `elem` valset taub |\}\\
  |valset (sigma -> tau)| ={}
                  |^&^ |\{|(vf1, dvf, vf2) `such` ^^^
                      ^&^ //= vf1 : sigma -> tau `wand`
                         //== dvf : sigma -> tau `wand`
                         //= vf2 : sigma -> tau ^^^
                      ^&^ `wandnosp` ^^^
                      ^&^ forall ((v1, dv, v2) `elem` (valset sigma)). ^^^
                      ^&^ qua ((vapply vf1 v1, dvapply dvf v1 dv, vapply vf2 v2) `elem` (compset tau)) |\}\\
  |compset tau| ={}&
                  \{|(envpair rho1 t1, denvpair rho drho dt, envpair rho2 t2) `such` ^^^
                    ^&^ (exists Gamma1 Gamma Gamma2 . ^^ Gamma1 /- t1 : tau `wand` ^^ Gamma /-- dt : tau `wand` Gamma2 /- t2 : tau) ^^^
                    ^&^ `wandnosp` ^^^
                    ^&^ forall v1 v2 . ^^^
                    ^&^ qua ((bseval t1 rho1 v1 `wand` bseval t2 rho2 v2)) => ^^^
                    ^&^ qua (exists dv . ^^ dbseval dt rho drho dv `wand` (v1, dv, v2) `elem` valset tau) |\}\\
                  \\
  |envset emptyCtx| ={} & \{|(emptyRho, emptyRho, emptyRho)|\} \\
  |envset (Gamma, x : tau)| ={} &
                                  \{|((rho1 , x := v1), (drho, dx := dv) , (rho2, x := v2)) `such` ^^^
                                  ^&^ (rho1, drho, rho2) `elem` envset Gamma `wand` (v1, dv, v2) `elem` valset tau|\} \\
  |fromtosyn Gamma tau t1 dt t2| ={}&
                                      |forall ((rho1, drho, rho2) `elem` envset Gamma) . ^^^
                                      ^&^ (envpair rho1 t1, denvpair rho1 drho dt, envpair rho2 t2) `elem` compset tau|
\end{align*}
\caption{Defining extensional validity via logical relations and big-step semantics.}
\label{fig:big-step-validity-ext-nosi}
\end{figure}

Given these definitions, one can prove the fundamental property.
\begin{theorem}[Fundamental property: correctness of |derive|]
  \label{thm:fund-lemma-derive-correct-types-nosi}
  For every well-typed term |Gamma /- t : tau| we have that
  |fromtosyn Gamma tau t (derive t) t|.
\end{theorem}
\begin{proof}[Proof sketch]
  By induction on the structure on terms, using ideas similar to
  \cref{thm:derive-correct}.
\end{proof}

It also follows that |derive t| normalizes:

\begin{corollary}[|derive | normalizes to a nil change]
  \label{thm:bsos-derive-normalization}
For any well-typed and closed term |/- t : tau|, there exist value |v| and
change value |dv| such that |/- t down v|, |/-- derive t ddown dv| and |(v, dv,
v) `elem` valset tau|.
\end{corollary}
\begin{proof}
A corollary of the fundamental property and of the normalization theorem
(\cref{thm:bsos-normalization}): since |t| is well-typed and closed it
normalizes to a value |v| for some step count (|/- t down v|).
The empty environment change is valid: |(emptyRho, emptyRho, emptyRho) `elem`
envset emptyCtx|, so from the fundamental property we get that |(/- t, /-- derive
t, /- t) `elem` compset tau|. From the definition of |compset tau| and
|/- t down v| it follows that there exists |dv| such that |/-- derive t ddown
dv| and |(v, dv, v) `elem` valset tau|.
\end{proof}
%{
%format (valset' (tau)) = "\mathcal{RV'}\left\llbracket" tau "\right\rrbracket"
%format (compset' (tau)) = "\mathcal{RC'}\left\llbracket" tau "\right\rrbracket"
\begin{remark}
  Compared to prior work,
  these relations are unusual for two reasons. First, instead of
  just relating two executions of a term, we relate two
  executions of a term with an execution of a change term.
  Second, most such logical relations (including
  \citet{Ahmed2006stepindexed}'s one, but except \citet{Acar08}'s
  one) define a logical relation (sometimes called \emph{logical
    equivalence}) that characterizes contextual equivalence, while we
  don't.

  Consider a logical equivalence defined through sets |(compset'
  tau)| and |(valset' tau)|.
  If |(t1, t2) `elem` (compset' tau)| holds and |t1| terminates
  (with result |v1|),
  then |t2| must terminate as well (with result |v2|), and their
  results |v1| and |v2| must in turn be logically equivalent
  (|v1, v2 `elem` valset' tau|).
  And at base types like |Nat|, |(v1, v2) `elem` (valset' Nat)|
  means that |v1 = v2|.

  Here. instead, the fundamental property relates two executions
  of a term on \emph{different} inputs, which might take
  different paths during execution. In a suitably extended language,
  we could even write term |t = \x -> if x = 0 then 1 else loop|
  and run it on inputs |v1 = 0| and |v2 = 1|: these inputs are
  related by change |dv = 1|, but |t| will converge on |v1| and
  diverge on |v2|. We must use a semantics that allow such
  behavioral difference.
  Hence, at base type |Nat|, |(v1, dv, v2) `elem` valset Nat|
  means just that |dv| is a change from |v1| to |v2|, hence that
  |v1 `oplus` dv| is equivalent to |v2| because |`oplus`| agrees
  with extensional validity in this context as well. And if |(envpair rho1 t1,
  denvpair rho drho dt, envpair rho2 t2) `elem` compset tau|, term |t1| might
  converge while |t2| diverges: only if both converge must their
  results be related.

  These subtleties become more relevant in the presence of
  general recursion and non-terminating programs, as in
  untyped language |ilcUntau|, or in a hypothetical extension of
  |ilcTau| with fixpoint operators.
\end{remark}
%}

\section{Step-indexed extensional validity (\ilcTau{}, \dilcTau)}
\label{sec:silr-typed-proof}
Step-indexed logical relations define approximations to a
relation, to enable dealing with non-terminating programs.
Logical relations relate the behavior of multiple terms during
evaluation; with step-indexed logical relations, we can take a
bound $k$ and restrict attention to evaluations that take at most
$k$ steps overall, as made precise by the definitions.
Crucially, entities related at step count $k$ are also
related at any step count $j < k$. Conversely, the higher the step count, the
more precise the defined relation. In the limit, if entities are related at all
step counts, we simply say they are related.
This construction of limits resembles various other approaches to constructing
relations by approximations, but the entire framework remains elementary. In
particular, the relations are defined simply because they are well-founded (that
is, only defined by induction on smaller numbers).
Proofs of logical relation statement need to deal with step-indexes, but when
they work (as here) they are otherwise not much harder than other syntactic or
logical relation proofs.

For instance, if we define equivalence as a step-indexed logical relation, we
can say that two terms are equivalent for $k$ or fewer steps, even if they might
have different behavior with more steps available. In our case, we can say that
a change appears valid at step count $k$ if it behaves like a valid change in
``observations'' using at most $k$ steps.

Like before, we define a relation on values and one on computations as sets
|valset tau| and |compset tau|.
Instead of indexing the sets with the step-count, we add the step counts to the
tuples they contain: so for instance |(k, v1, dv, v2) `elem` valset tau| means
that value |v1|, change value |dv| and value |v2| are related at step count $k$
(or $k$-related), and similarly for |compset tau|.

The details or the relation definitions are
subtle, but follow closely the use of step-indexing by
\citet*{Acar08}. We add mention of changes, and must decide how to use
step-indexing for them.

\paragraph{How step-indexing proceeds}
We explain gradually in words how the definition proceeds.

First, we say $k$-related function values take $j$-related arguments to $j$-related
results for all $j$ less than $k$. That is reflected in the definition for
|valset (sigma -> tau)|: it contains |(k, vf1, dvf, vf2)| if, for all
|(j, v1, dv, v2) `elem` (valset sigma))| with |j < k|, the result of
applications are also |j|-related.
However, the result of application are not syntactic applications encoding |vf1
v1|\footnote{That happens to be illegal syntax in this presentation, but can be
encoded for instance as |envpair (f := vf1, x := v1) (f x)|; and the problem is
more general.}.
It is instead necessary to use |vapply vf1 v1|, the result of one step of
reduction. The two definitions are not equivalent because a syntactic
application would take one extra step to reduce.

The definition for computations takes longer to describe. Roughly speaking, computations are $k$-related if, after $j$
steps of evaluations (with $j < k$), they produce values related at $k - j$
steps; in particular, if the computations happen to be neutral forms and
evaluate in zero steps, they're $k$-related as computations if the values they
produce are $k$-related.
In fact, the rule for evaluation has a wrinkle.
Formally, instead of saying that computations |(envpair rho1 t1, denvpair rho
drho dt, envpair rho2 t2)| are $k$-related, we say that |(k, envpair rho1 t1,
denvpair rho drho dt, envpair rho2 t2) `elem` compset tau|. We do not require
all three computations to take $j$ steps. Instead, if the first computation
|envpair rho1 t1| evaluates to a value in $j < k$ steps, and the second
computation |envpair rho2 t2| evaluates to a value in any number of steps,
\emph{then} the change computation |denvpair rho drho dt| must also terminate to
a change value |dv| (in an unspecified number of steps), and the resulting
values must be related at step-count $k-j$ (that is,
|(k - j, v1, dv, v2) `elem` valset tau|).

What is new in the above definition is the addition of changes, and the choice
to allow change term |dt| to evaluate to |dv| in an unbounded number of steps
(like |t2|), as no bound is necessary for our proofs.
This is why the semantics we defined for change terms has no step counts.

Well-foundedness of step-indexed logical relations has a small wrinkle, because
|k - j| need not be strictly less than |k|. But we define the two relations in a
mutually recursive way, and the pair of relations at step-count |k| is defined
in terms of the pair of relation at smaller step-count. All other recursive uses
of relations are at smaller step-indexes.

% Instead of observing the behavior of terms with an unbounded
% number of computation steps, as we did before, we observe the
% behavior of terms having a bounded
% we give a bound $k$, and observe
% behavior with at most $k$

In this section we index the relation by both types and step-indexes,
since this is the one we use in our mechanized proof. This
relation is defined by structural induction on types.
We show this definition in \cref{fig:big-step-validity-ext-si}.
Instead, in \cref{sec:silr-untyped-proof} we consider
untyped $\lambda$-calculus and drop types.
The resulting definition is very similar, but is defined by
well-founded recursion on step-indexes.

\begin{figure}[h!]
\begin{align*}
  |valset Nat| ={}& \{|(k, n1, dn, n2) `such` n1, dn, n2 `elem` Nat `wand` n1 + dn = n2|\}\\
  |valset (taua `times` taub)| ={} & \{|(k, pair va1 vb1, pair dva dvb, pair va2 vb2) `such` ^^^
                                   ^&^ (k, va1, dva, va2) `elem` valset taua
                                      ^^ `wand` ^^
                                      (k, vb1, dvb, vb2) `elem` valset taub |\}\\
  |valset (sigma -> tau)| ={}
                  |^&^ |\{|(k, vf1, dvf, vf2) `such` ^^^
                      ^&^ //= vf1 : sigma -> tau `wand`
                         //== dvf : sigma -> tau `wand`
                         //= vf2 : sigma -> tau ^^^
                      ^&^ `wandnosp` ^^^
                      ^&^ forall ((j, v1, dv, v2) `elem` (valset sigma)). ^^ j < k => ^^^
                      ^&^ qua ((j, vapply vf1 v1, dvapply dvf v1 dv, vapply vf2 v2) `elem` (compset tau)) |\}\\
  |compset tau| ={}&
                  \{|(k, envpair rho1 t1, denvpair rho drho dt, envpair rho2 t2) `such` ^^^
                    ^&^ (exists Gamma1 Gamma Gamma2 . ^^ Gamma1 /- t1 : tau `wand` ^^ Gamma /-- dt : tau `wand` Gamma2 /- t2 : tau) ^^^
                    ^&^ `wandnosp` ^^^
                    ^&^ forall j v1 v2 . ^^^
                    ^&^ qua ((j < k `wand` bseval t1 rho1 v1 `wand` bseval t2 rho2 v2)) => ^^^
                    ^&^ qua (exists dv . ^^ dbseval dt rho drho dv `wand` (k - j, v1, dv, v2) `elem` valset tau) |\}\\
                  \\
  |envset emptyCtx| ={} & \{|(k, emptyRho, emptyRho, emptyRho)|\} \\
  |envset (Gamma, x : tau)| ={} &
                                  \{|(k, (rho1 , x := v1), (drho, dx := dv) , (rho2, x := v2)) `such` ^^^
                                  ^&^ (k, rho1, drho, rho2) `elem` envset Gamma `wand` (k, v1, dv, v2) `elem` valset tau|\} \\
  |fromtosyn Gamma tau t1 dt t2| ={}&
                                      |forall ((k, rho1, drho, rho2) `elem` envset Gamma) . ^^^
                                      ^&^ (k, envpair rho1 t1, denvpair rho1 drho dt, envpair rho2 t2) `elem` compset tau|
\end{align*}
\caption{Defining extensional validity via \emph{step-indexed} logical relations and big-step semantics.}
\label{fig:big-step-validity-ext-si}
\end{figure}

Again, since we use Church typing and only mechanize typed terms, we
must include in all cases appropriate typing assumptions. This
choice does not match \citet{Ahmed2006stepindexed} but is
one alternative she describes as equivalent. Indeed, while
adapting the proof the extra typing assumptions and proof
obligations were not a problem.

At this moment, we do not require that related closures contain
related environments: again, we are defining \emph{extensional}
validity.

Given these definitions, we can prove that all relations are
\emph{downward-closed}: that is, relations at step-count $n$
imply relations at step-count $k < n$.
\begin{lemma}[Extensional validity is downward-closed]
  \label{lem:validity-typed-downward-closed}
  Assume $k \le n$.
  \begin{enumerate}
  \item If |(n, v1, dv, v2) `elem` valset tau| then |(k, v1, dv,
    v2) `elem` valset tau|.
  \item If |(n, envpair rho1 t1, denvpair rho drho dt, envpair rho2 t2) `elem`
    compset tau| then
    \[|(k, envpair rho1 t1, denvpair rho drho dt, envpair rho2 t2) `elem` compset tau|.\]
  \item If |(n, rho1, drho, rho2) `elem` envset Gamma| then
    |(k, rho1, drho, rho2) `elem` envset Gamma|.
  \end{enumerate}
\end{lemma}
\begin{proof}[Proof sketch]
  For |valset tau|, case split on |tau| and expand hypothesis and
thesis. If |tau = Nat| they coincide. For |valset (sigma ->
tau)|, parts of the hypothesis and thesis match.
For some relation |P|,
the rest of the hypothesis has shape |forall j < n. ^^ P(j, v1, dv, v2)|
and the rest of the thesis has shape |forall j < k. ^^ P(j, v1, dv,
v2)|. Assume $j < k$. We must prove |P(j, v1, dv, v2)|, but since
$j < k \le n$ we can just apply the hypothesis.

The proof for |compset tau| follows the same idea as
|valset (sigma -> tau)|.

For |envset Gamma|, apply the theorem for |valset tau| to each
environments entry |x : tau|.
\end{proof}

At this point, we prove the fundamental property.
\begin{theorem}[Fundamental property: correctness of |derive|]
  \label{thm:fund-lemma-derive-correct-types-si}
  For every well-typed term |Gamma /- t : tau| we have that
  |fromtosyn Gamma tau t (derive t) t|.
\end{theorem}
\begin{proof}[Proof sketch]
  By structural induction on typing derivations, using ideas
similar to \cref{thm:fund-lemma-derive-correct-types-nosi} and
relying on \cref{lem:validity-typed-downward-closed} to reduce
step counts where needed.
\end{proof}

\section{Step-indexed intensional validity}
\label{sec:intensional-step-indexed-validity}

Up to now, we have defined when a function change is valid
\emph{extensionally}, that is, purely based on its behavior, as
we have done earlier when using denotational semantics.
We conjecture that with these one can define |`oplus`| and prove
it agrees with extensional validity. However, we have not done
so.

Instead, we modify definitions in \cref{sec:silr-typed-proof} to
define validity \emph{intensionally}.
To ensure that |f1 `oplus` df = f2| (for a suitable |`oplus`|) we
choose to require that closures |f1|, |df| and |f2| close over
environments of matching shapes. This change does not complicate
the proof of the fundamental lemma: all the additional proof obligations
are automatically satisfied.

However, it can still be necessary to replace a function value
with a different one. Hence we extend our definition of values to
allow replacement values. Closure replacements produce
replacements as results, so we make replacement values
into valid changes for all types. We must also extend the change
semantics, both to allow evaluating closure replacements, and to
allow derivatives of primitive to handle replacement values.

We have not added replacement values to the syntax, so currently
they can just be added to change environments, but we don't
expect adding them to the syntax would cause any significant trouble.

We present the changes described above for the typed semantics. We have
successfully mechanized this variant of the semantics as well.
Adding replacement values |!v| requires extending the definition
of change values, evaluation and validity.
We add replacement values to change values:
\begin{code}
  dv := ... | ! v
\end{code}
Derivatives of primitives, when applied to replacement changes,
must recompute their output. The required additional equations
are not interesting, but we show them anyway for completeness:

  %devalPrim add (pair n1 n2) (pair dn1 dn2)  = dn1 + dn2
\begin{code}
  devalPrim succ n1 (!n2)                   = !(n2 + 1)
  devalPrim add (pair _ _) (!(pair m2 n2))  = !(m2 + n2)
  devalPrim add p1 (dp @ (pair dm (!n2)))   = !(evalPrim add (p1 `oplus` dp))
  devalPrim add p1 (dp @ (pair (!m) dv))    = !(evalPrim add (p1 `oplus` dp))
\end{code}

Evaluation requires a new rule, \textsc{E-BangApp}, to evaluate
change applications where the function change evaluates to a
replacement change:

{\footnotesize
\begin{typing}
   \Rule[E-BangApp]{%
    %|dbseval dwf rho drho (!(rho'[\x -> t]))|\\
    |dbseval dwf rho drho (!vf)|\\
    |bseval  wa  rho va|\\
    |dbseval dwa rho drho dva|\\
    %|bseval  t  (rho', x := va `oplus` dva) v|\\
    |vapply  vf (va `oplus` dva) down v|}
  {|dbseval (dwf wa dwa) rho drho (!v)|}
\end{typing}
}
  %  \Rule[E-BangApp]{%
  %   |dbseval dw1 rho drho (!(rho'[\x -> t]))|\\
  %   |bseval  w2  rho v2|\\
  %   |dbseval dw2 rho drho dv2|\\
  %   |bseval t  (rho', x := v2 `oplus` dv2) v|}
  % {|dbseval (dw1 w2 dw2) rho drho (!v)|}

Evaluation rule \textsc{E-BangApp} requires defining |`oplus`| on
syntactic values. We define it \emph{intensionally}:
\begin{definition}[Update operator |`oplus`|]
  %{
  %format matchGamma = "\mathsf{match\Gamma}"
  Operator |`oplus`| is defined on values by the following
  equations:

  \begin{code}
    v1 `oplus` ! v2 = v2
    rho[\x -> t] `oplus` drho[\x dx -> dt] =
      if matchGamma rho  drho then
        -- If |rho| and |drho| are environments for the same typing context |Gamma|:
        (rho `oplus` drho)[\x -> t]
      else
        -- otherwise, the input change is invalid, so just give
        -- any type-correct result:
        rho[\x -> t]
    n `oplus` dn                       = n + dn
    pair va1 vb1 `oplus` pair dva dvb  = pair (va1 `oplus` dva) (vb1 `oplus` dvb)
    -- An additional equation is needed in the untyped language,
    -- not in the typed one. This equation is for invalid
    -- changes, so we can just return |v1|:
    v1 `oplus` dv = v1
  \end{code}
  We omit the definition of |matchGamma rho drho|.

  We also define |`oplus`| on environments for matching contexts
  to combine values and changes pointwise:
  \begin{code}
    (x1 := v1, ..., xn := vn) `oplus` (dx1 := dv1, ..., dxn := dvn) =
        (x1 := v1 `oplus` dv1, ..., xn := vn `oplus` dvn)
  \end{code}
  %}
\end{definition}
The definition of update for closures can only update them in few cases, but
this is not a problem: as we show in a moment, we restrict validity to the
closure changes for which it is correct.

We ensure replacement values are accepted as valid for all types,
by requiring the following equation holds (hence, modifying all
equations for |valset|; we omit details):
\begin{align}
  \label{eq:val-replacement}
  |valset tau| \supseteq {}& \{| (k, v1, !v2, v2) `such` ^^ //= v1 : tau ^^ `wand` ^^ //= v2 : tau |\}
\end{align}
where we write |//= v : tau| to state that value |v| has type
|tau|; we omit the unsurprising rules for this judgement.

Finally, to restrict closure changes themselves, we modify the
definition for |valset (sigma -> tau)| by requiring that related elements
satisfy predicate |matchImpl vf1 dvf vf2|, defined by pattern matching syntax
(informally) via the following equations:

%format matchImpl = "\mathsf{matchImpl}"
\begin{code}
  matchImpl
    (rho1[\x -> t])
    (rho1 `stoup` drho[\x dx -> derive t])
    ((rho1 `oplus` drho)[\x -> t]) =
  matchImpl _ _ _ = False
\end{code}
Via |matchImpl| we require that the base
closure environment |rho1| and the base environment of the
closure change coincide, that |rho2 = rho1 `oplus` drho|,
and that |vf1| and |vf2| have |\x -> t| as body while |dvf| has body |\x dx ->
derive t|.

As an example for \cref{eq:val-replacement}, we also include explicitly
replacement closures in the definition of |valset (sigma -> tau)|.
\begin{align*}
  |valset (sigma -> tau)| ={}
                  |^&^ |\{|(k, vf1, dvf, vf2) `such` ^^^
                      ^&^ //= vf1 : sigma -> tau `wand`
                         //== dvf : sigma -> tau `wand`
                         //= vf2 : sigma -> tau ^^^
                      ^&^ `wandnosp` ^^^
                      ^&^ matchImpl vf1 dvf vf2 ^^^
                      ^&^ `wandnosp` ^^^
                      ^&^ forall ((j, v1, dv, v2) `elem` (valset sigma)). ^^ j < k => ^^^
                      ^&^ qua ((j, vapply vf1 v1, dvapply dvf v1 dv, vapply vf2 v2) `elem` (compset tau))|\}| ^^ `union` ^^^
                  ^&^| \{| (k, f1, !f2, f2) `such` ^^ //= f1 : sigma -> tau ^^ `wand` ^^ //= f2 : sigma -> tau |\}
\end{align*}

Using these updated definitions, we can again prove the
fundamental property, with the same statement as
\cref{thm:fund-lemma-derive-correct-types-si}, and we can also
prove that |`oplus`| agrees
with validity.

\begin{theorem}[Fundamental property: correctness of |derive|]
  \label{thm:fund-lemma-derive-correct-types-si-intensional}
  For every well-typed term |Gamma /- t : tau| we have that
  |fromtosyn Gamma tau t (derive t) t|.
\end{theorem}
\begin{theorem}[|`oplus`| agrees with step-indexed intensional validity]
  \label{thm:oplus-validity-intensional}
If |(k, v1, dv, v2) `elem` valset tau| then |v1 `oplus` dv = v2|.
\end{theorem}
\begin{proof}
  By induction on types. For type |Nat| validity coincides with the
  thesis. For type |pair taua taub|, we must simply apply the
  induction hypothesis on pair components.

  For closures, validity requires that |v1 = rho1[\x -> t], dv =
  drho[\x dx -> derive t], v2 = rho2[\x -> t]| with |rho1 `oplus`
  drho = rho2|, and there exists |Gamma| such that |Gamma, x :
  sigma /- t : tau|. Moreover, from validity we can show that |rho|
  and |drho| have matching shapes: |rho| is an environment
  matching |Gamma| and |drho| is a change environment matching
  |Dt^Gamma|. Hence, |v1 `oplus` dv| can update the stored
  environment, and we can show the thesis by the following
  calculation:
  \begin{multline*}
    |v1 `oplus` dv = rho1[\x -> t] `oplus` drho[\x dx -> dt] =|\\
    |(rho1 `oplus` drho)[\x -> t] = rho2[\x -> t] = v2|
  \end{multline*}
\end{proof}

We can also define |nilc| intensionally on values and
environments, and prove it correct. We omit the standard
definition of |nil| on environments.
For closures, we recurse on the environment.
\begin{definition}[Nil changes |nilc|]
  Nil changes on values are defined as follows:
\begin{code}
  nil (rho[\x -> t]) = rho `stoup` (nil rho)[\x dx -> derive t]
  nil (pair a b) = pair (nil a) (nil b)
  nil n = 0
\end{code}
\end{definition}
\begin{lemma}[|nilc| produces valid changes]
  For all values |//= v : tau| and indexes |k|, we have |(k, v, nil v, v)
  `elem` valset tau|.
\end{lemma}
\begin{proof}[Proof sketch]
  By induction on |v|. For closures we must apply the fundamental
  property
  (\cref{thm:fund-lemma-derive-correct-types-si-intensional}) to
  |derive t|.
\end{proof}

We conclude with the overall correctness theorem, analogous to
\cref{thm:derive-correct-oplus}.

\deriveCorrectOplusSI
\begin{proof}
  Follows immediately from
  \cref{thm:fund-lemma-derive-correct-types-si-intensional} and
  \cref{thm:oplus-validity-intensional}.
\end{proof}

\section{Untyped step-indexed validity (\ilcUntau{}, \dilcUntau{})}
\label{sec:silr-untyped-proof}
By removing mentions of types from step-indexed validity
(intensional or extensional, though we show extensional definitions), we can
adapt it to an untyped language.
We can still distinguish between functions, numbers and pairs by
matching on values themselves, instead of matching on types.
Without types, typing contexts |Gamma| now degenerate to lists of
free variables of a term; we still use them to ensure that
environments contain enough valid entries to evaluate a term.
Validity applies to terminating executions, hence we need not
consider executions producing dynamic type errors when proving
the fundamental property.

We show resulting definitions for extensional validity in
\cref{fig:big-step-validity-ext-si-untyped}; but we can also define
intensional validity and prove the fundamental lemma for it.
As mentioned earlier, for \ilcUntau{} we must turn |evalPrim| and |devalPrim|
into relations and update \textsc{E-Prim} accordingly.

The main difference in the proof is that this time, the recursion
used in the relations can only be proved to be well-founded
because of the use of step-indexes; we omit
details~\citep{Ahmed2006stepindexed}.

\begin{figure}[h!]
\begin{align*}
  |valsetunt| ={}& \{|(k, n1, dn, n2) `such` n1, dn, n2 `elem` Nat
                   `wand` n1 + dn = n2|\} | ^^ `union` ^^^
                  ^&^ |\{|(k, vf1, dvf, vf2) `such` ^^^
                      ^&^ forall ((j, v1, dv, v2) `elem` valsetunt). ^^ j < k => ^^^
                      ^&^ qua ((j, vapply vf1 v1, dvapply dvf v1 dv, vapply vf2 v2) `elem` compsetunt) |\}| ^^ `union` ^^^
                  ^&^ | \{|(k, pair va1 vb1, pair dva dvb, pair va2 vb2) `such` ^^^
                   ^&^ (k, va1, dva, va2) `elem` valsetunt
                      ^^ `wand` ^^
                      (k, vb1, dvb, vb2) `elem` valsetunt |\}\\
  |compsetunt| ={}&
                  \{|(k, envpair rho1 t1, denvpair rho drho dt, envpair rho2 t2) `such` ^^^
                    ^&^ forall j v1 v2 . ^^^
                    ^&^ qua ((j < k `wand` bseval t1 rho1 v1 `wand` bseval t2 rho2 v2)) => ^^^
                    ^&^ qua (exists dv . ^^ dbseval dt rho drho dv `wand` (k - j, v1, dv, v2) `elem` valsetunt) |\}\\
  \\
  |envset emptyCtx| ={} & \{|(k, emptyRho, emptyRho, emptyRho)|\} \\
  |envset (Gamma, x)| ={} &
                                  \{|(k, (rho1 , x := v1), (drho, dx := dv) , (rho2, x := v2)) `such` ^^^
                                  ^&^ (k, rho1, drho, rho2) `elem` envset Gamma `wand` (k, v1, dv, v2) `elem` valsetunt|\} \\
  |fromtosynuntyped Gamma t1 dt t2| ={}&
                                      |forall ((k, rho1, drho, rho2) `elem` envset Gamma) . ^^^
                                      ^&^ (k, envpair rho1 t1, denvpair rho1 drho dt, envpair rho2 t2) `elem` compsetunt|
\end{align*}
\caption{Defining extensional validity via \emph{untyped step-indexed} logical relations and big-step semantics.}
\label{fig:big-step-validity-ext-si-untyped}
\end{figure}

Otherwise, the proof proceeds just as earlier in
\cref{sec:silr-typed-proof}: We prove that the relations are
downward-closed, just like in \cref{lem:validity-typed-downward-closed}
(we omit the new statement), and we prove the new fundamental
lemma by induction on the structure of terms (not of typing derivations).

%format `subset` = "\subseteq"

\begin{theorem}[Fundamental property: correctness of |derive|]
  \label{thm:fund-lemma-derive-correct-untyped-si}
  If |FV(t) `subset` Gamma| then we have that |fromtosynuntyped
  Gamma t (derive t) t|.
\end{theorem}
\begin{proof}[Proof sketch]
  Similar to the proof of
\cref{thm:fund-lemma-derive-correct-types-si}, but by structural
induction on terms and complete induction on step counts, not on
typing derivations.

However, we can use the induction hypothesis in the same ways as
in earlier proofs for typed languages: all uses of the induction
hypothesis in the proof are on smaller terms, and some also at
smaller step counts.
\end{proof}

\section{General recursion in \ilcTau{} and \dilcTau}
\label{sec:bos-fixpoints}

%format rec = "\mathbf{rec}"
%format drec = "\mathbf{drec}"

We have sketched informally in \cref{sec:general-recursion} how to support
fixpoint combinators.

We have also extended our typed languages with a
fixpoint combinators and proved them correct formally (not
mechanically, yet). In this section, we include the needed
definitions to make our claim precise. They are mostly
unsurprising, if long to state.

Since we are in a call-by-value setting, we only add recursive
functions, not recursive values in general.
To this end, we replace $\lambda$-abstraction |\x -> t| with recursive
function |rec f x -> t|, which binds both |f| and |x| in |t|, and
replaces |f| with the function itself upon evaluation.

The associated small-step reduction rule would be
|(rec f x -> t) v -> t [x := v, f := rec f x -> t]|. As before,
we formalize reduction using big-step semantics.

Typing rule \textsc{T-Lam} is replaced by a rule for recursive functions:
\begin{typing}
  \Rule[T-Rec]{|Gamma , f : sigma -> tau, x : sigma /- t : tau|}
  {|Gamma /- rec f x -> t : sigma -> tau|}
\end{typing}
We replace closures with recursive closures in the definition of values:
\begin{code}
  w ::= rec f x -> t | ...
  v ::= rho[rec f x -> t] | ...
\end{code}
We also modify the semantics for abstraction and application. Rules
\textsc{E-Val} and \textsc{E-App} are unchanged: it is sufficient to adapt the
definitions of |evalVal| and |vapply|.
\begin{code}
evalVal (rec f x -> t) rho     = rho[rec f x -> t]

vapply vf va =
  case vf of rho'[rec f x -> t] ->
    envpair ((rho', f := vf, x := va)) t
\end{code}

We also modify the language of changes and some of its evaluation rules.
Since the derivative of a recursive function |f = rec f x -> t| can call the base
function, we remember the original function body |t| in the
derivative, together with its derivative |derive t|. This should not be
surprising: in \cref{sec:general-recursion}, where recursive functions are
defined using |letrec|, a recursive function |f| is in scope in the body of its
derivative |df| Here we use a different syntax, but still ensure that |f| is in
scope in the body of derivative |df|.
The definitions are otherwise unsurprising, if long.

{
\begin{code}
dw ::= drec f df x dx -> t `stoup` dt | ...
dv ::= rho `stoup` drho[drec f df x dx -> t `stoup` dt] | ...

derive (rec f x -> t) = drec f df x dx -> t `stoup` derive t

devalVal (drec f df x dx -> dt) rho drho =
  rho `stoup` drho[drec f df x dx -> t `stoup` dt]

dvapply dvf va dva =
  case dvf of
    rho' `stoup` drho' [rec f df x dx -> dt] ->
      let vf = rho'[rec f x -> t]
      in
        denvpair ((rho', f := vf , x := va)) ((drho' , df := dvf , dx := dva)) dt
\end{code}

\begin{typing}
  \Rule[T-DRec]{
    |Gamma , f : sigma -> tau, x : sigma /- t : tau|\\
    |Gamma , f : sigma -> tau, x : sigma /-- dt : tau|
  }
  {|Gamma /-- drec f df x dx -> t `stoup` dt : sigma -> tau|}
\end{typing}
}

We must also update the logical relations to use the new
definition of application between values. We omit details.

\begin{theorem}[Fundamental property: correctness of |derive|]
  \label{thm:fund-lemma-derive-correct-types-si-intensional-rec}
  For every well-typed term |Gamma /- t : tau| we have that
  |fromtosyn Gamma tau t (derive t) t|.
\end{theorem}
\begin{proof}[Proof sketch]
  Essentially as before.

  Going through the proof will reveal one interesting difference:
  To prove the fundamental property for recursive
  functions at step-count |k|, this time we must use the
  fundamental property inductively on the same term, but at
  step-count |j < k|.

  This happens because to evaluate |dw = derive(rec f x -> t)| we
  evaluate |derive t| with the value |dv| for |dw| in the
  environment: to show this invocation is valid, we must show |dw|
  is itself a valid change. But the step-indexed
  definition to |valset (sigma -> tau)| constrains the evaluation
  of the body only |forall j < k|.

  % Consider the case for recursive abstraction |dw' = derive(rec f
  % x -> t)| at step-count |k|. After unfolding a few definitions
  % (which we skip here), we must show for any |j < k| and for any
  % |j|-valid argument change that running the derivative of the
  % recursive abstraction evaluates (using rule \textsc{E-DApp})
  % |derive t| with an environment change that is valid. But this
  % time, the value of the recursive function change |dw'| is itself
  % in the environment! Luckily, we can show that |dw'| is valid at
  % step-count |j| by using the fundamental property inductively,
  % since |j < k|. The proof otherwise proceeds similarly to the
  % proof for abstraction.

  % In a bit more detail, for recursive abstractions in the end we
  % must roughly show that for all |j < k| the recursive abstractions
  % in question, applied to |j|-valid arguments, give |j|-valid
  % resulting computations. The proof uses the fundamental property
  % recursively on |t| and on a |j|-valid environment. But this time,
  % the environment contains closures

  % There is \emph{one} critical difference in the proof
  % a recursive function is valid at step-count
\end{proof}

\section{Future work}
We have shown that |`oplus`| and |nilc| agree with validity,
which we consider a key requirement of a core ILC proof. However,
change structures support further operators. We leave operator
|`ominus`| for future work, though we are not aware of particular
difficulties.
However, |`ocompose`| deserves special attention.
\subsection{Change composition}
We have looked into change composition, and it appears that
composition of change expression is not always valid, but we
conjecture that composition of change values preserves validity.
Showing that change composition is valid appears related to
showing that \citeauthor{Ahmed2006stepindexed}'s logical equivalence
is a transitive relation, which is a subtle issue. She only
proves transitivity in a typed setting and with a stronger
relation, and her proof does not carry over directly; indeed,
there is no corresponding proof in the untyped setting of
\citet*{Acar08}.

However, the failure of transitivity we have verified is not
overly worrisome: the problem is that transitivity is too strong
an expectation in general. Assume that |fromtosynuntyped Gamma e1
de1 e2| and |fromtosynuntyped Gamma e2 de2 e3|, and try to show
that |fromtosynuntyped Gamma e1 (de1 `ocompose` de2) e3|: that
is, very roughly and ignoring the environments, we can assume
that |e1| and |e3| terminate, and have to show that their result
satisfy some properties. To use both our hypotheses, we need to
know that |e1|, |e2| and |e3| all terminate, but we have no such
guaranteed for |e2|. Indeed, if |e2| always diverges (because it
is, say, the diverging term |omega = (\x -> x x) (\x -> x x)|), then |de1| and |de2|
are vacuously valid. If |e1| and |e3| terminate, we can't expect
|de1 `ocompose` de2| to be a change between them. To wit, take
|e1 = 0|, |e2 = omega|, |e3 = 10|, and |de1 = de2 = 0|. We can
verify that for any |Gamma| we have |fromtosynuntyped Gamma e1 de1 e2| and
|fromtosynuntyped Gamma e2 de2 e3|, while |fromtosynuntyped
Gamma e1 (de1 `ocompose` de2) e3| means the absurd
|fromtosynuntyped Gamma 0 (0 `ocompose` 0) 10|.

\paragraph{A possible fix}
Does transitivity hold if |e2| terminates?
we cannot conclude anything from
|(k, e1, de1, e2) `elem` compset tau `wand` (k, e2, de2, e3)
`elem` compset tau|.

But like in \citet{Ahmed2006stepindexed}, if |e2| amd |e3| are
related at all step counts, that is, if |(k, e1, de1, e2) `elem`
compset tau `wand` (forall n. (n, e2, de2, e3) `elem` compset
tau)|, and if additionally |e2| terminates, we conjecture that
\citeauthor{Ahmed2006stepindexed}'s proof goes through. We have
however not yet examined all details.

% transitivity requires using a typed setting.
% However, her
% logical relation is indeed transitive, and we believe
% We conjecture

% Defining |nil| should not be a a problem: the nil change of a
% closure just takes nil changes or each environment entry.

% As explained by \citeauthor{Ahmed2006stepindexed}, transitivity
% of her logical relation is subtle.
% For us this corresponds to two questions that we leave open:
% \pg{resume; it's composition and transitivity of change equivalence.}

\section{Development history}
\label{sec:ilc-bsos-dev-history}
The proof strategy used in this chapter comes from a
collaboration between me and Yann Régis-Gianas, who came up with the
general strategy and the first partial proofs for untyped $\lambda$-calculi.
After we both struggled for a while to set up step-indexing correctly enough for a
full proof, I first managed to give the definitions in this chapter and
complete the proofs here described. Régis-Gianas then mechanized a variant of
this proof in Coq~\citet{Giarrusso2018Static}.

\section{Conclusion}
In this chapter we have shown how to construct novel models for
ILC by using (step-indexed) logical relations, and have used this
technique to deliver a new syntactic proof of correctness for ILC
for simply-typed $lambda$-calculus and to deliver the first proof
of correctness of ILC for untyped $\lambda$-calculus. Moreover,
our proof appears rather close to existing
logical-relations proofs, hence we believe it should be possible
to translate other results to ILC theorems.

By formally defining intensional validity for closures, we
provide a solid foundation for the use of defunctionalized
function changes (\cref{ch:defunc-fun-changes}).

This proof builds on \citet{Ahmed2006stepindexed}'s
work on step-indexed logical relations, which enable handling of
powerful semantics feature using rather elementary techniques.
The only downside is that it can be tricky to set up the correct
definitions, especially for a slightly non-standard semantics
like ours.
As an exercise, we have shown that the our semantics is
equivalent to more conventional presentations, down to the
produced step counts.
