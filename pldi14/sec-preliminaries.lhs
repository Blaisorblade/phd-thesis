% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter[Preliminaries]{Preliminaries: syntax and semantics of
  simply-typed λ-calculus}
\label{sec:preliminaries}

To discuss how we incrementalize programs and prove that
our incrementalization technique gives correct results, we specify
which foundation we use for our proofs and what object language we
study.

We mechanize our correctness proof using Agda, hence we use
Agda's underlying type theory as our foundation. We discuss
what this means in \cref{sec:metalanguage}.

Our object language is a standard simply-typed $\lambda$-calculus
(STLC)~\citep[Ch.~9]{Pierce02TAPL}, parameterized over base types
and constants. We term the set of base types and constants a
\emph{language plugin} (see \cref{sec:lang-plugins}). In our
examples we assume that the language plugins supports needed base
types and constants. Later (e.g., in \cref{ch:derive-formally})
we add further requirements to language plugins, to support
incrementalization of the language features they add to our STLC.
%
Rather than operational semantics we use a denotational
semantics, which is however set-theoretic rather than
domain-theoretic. Our object language and its semantics are
summarized in \cref{fig:lambda-calc}.

At this point, readers might want to skip to \cref{sec:intro}
right away, or focus on denotational semantics, and refer to this
section as needed.

\section{Our proof meta-language}
\label{sec:metalanguage}
In this section we describe the logic (or meta-language) used in our
\emph{mechanized} correctness proof.

First, as usual, we distinguish between ``formalization'' (that
is, on-paper formalized proofs) and ``mechanization'' (that is,
proofs encoded in the language of a proof assistant for
computer-aided \emph{mechanized} verification).

To prove the correctness of \ILC, we provide a mechanized proof
in Agda~\citep{agda-head}. Agda implements intensional Martin-Löf
type theory (from now on, simply type theory), so type theory is
also the foundation of our proofs.

At times, we use conventional set-theoretic language to discuss
our proofs, but the differences are only superficial. For
instance, we might talk about a set of elements |S| and with
elements such as |s `elem` S|, though we always mean that |S| is
a metalanguage type, that |s| is a metalanguage value, and that |s : S|.
Talking about sets
avoids ambiguity between types of our meta-language and types of
our object-language (that we discuss next in
\cref{sec:intro-stlc}).
\begin{notation}
  We'll let uppercase latin letters |A, B, C ..., V, U| range
  over sets, never over types.
\end{notation}

We do not prove correctness of all our language plugins. However,
in earlier work~\citep{CaiEtAl2014ILC} we prove correctness for
a language plugin supporting \emph{bags}, a type of collection (described in
\cref{sec:motiv-example}). For that proof, we extend our logic by
postulating a few standard axioms on the implementation of bags,
to avoid proving correct an implementation of bags, or needing to
account for different values representing the same bag (such
different values typically arise when implementing bags as search
trees).

\subsection{Type theory versus set theory}
Here we summarize a few features of type theory over set theory.

Type theory is dependently typed, so it generalizes
function type |A -> B| to \emph{dependent} function type |(x : A)
-> B|, where |x| can appear free in |B|. Such a type guarantees
that if we apply a function |f : (x : A) -> B| to an argument |a
: A|, the result has type |B [ x := a ]|, that is |B| where |x|
is substituted by |a|. At times, we will use dependent types in
our presentation.

Moreover, by using type theory:
\begin{itemize}
\item We do not postulate the law of excluded middle; that is,
  our logic is constructive.
\item Unlike set theory, type theory is proof-relevant: that is,
  proofs are first-class mathematical objects.
\item Instead of subsets
  $\{x \in A \mid P(x)\}$, we must use $\Sigma$-types
  $\Sigma (x : A) P(x)$ which contain pairs of elements $x$ and
  proofs they satisfy predicate $P$.
\item In set theory, we can assume without further ado functional
  extensionality, that is, that functions that give equal results
  on all equal inputs are equal themselves. Intuitionistic type
  theory does not prove functional extensionality, so we need to
  add it as a postulate. In Agda, this postulate is known to be
  consistent~\citep{Hofmann96}, hence it is safe to assume%
  \footnote{\url{http://permalink.gmane.org/gmane.comp.lang.agda/2343}}.
%\item All our function spaces are limited to computable functions.
\end{itemize}

To handle binding issues in our object language, our
formalization uses typed de Bruijn indexes, because this
techniques takes advantage of Agda's support for type refinement
in pattern matching. On top of that, we implement a HOAS-like
frontend, which we use for writing specific terms.

% Our Agda formalization, Scala implementation and benchmark
% results are available at the URL
% \url{http://inc-lc.github.io/}.
% All lemmas and theorems presented
% in this chapter have been proven in Agda.
% In the chapter, we present an overview of
% the formalization in more human-readable form, glossing over some
% technical details.

\section{Simply-typed λ-calculus}
\label{sec:intro-stlc}

We consider as object language a strongly-normalizing
simply-typed $\Gl$-calculus (STLC). We choose STLC as it is the
simplest language with first-class functions and types, while
being a sufficient model of realistic total languages.%
\footnote{To know why we restrict to total languages see
  \cref{sec:general-recursion}.}
%
We recall the syntax and typing rules of STLC in
\cref{fig:lambda-calc:syntax,fig:lambda-calc:typing}, together
with metavariables we use. Language plugins define base types
|iota| and constants |c|. Types can be base types |iota| or
function types |sigma -> tau|. Terms can be constants |c|,
variables |x|, function applications |t1 t2| or
$\lambda$-abstractions |\(x : sigma) -> t|. To describe
assumptions on variable types when typing terms, we define (typing)
contexts |Gamma| as being either empty |emptyCtx|, or as context
extensions |Gamma, x : tau|, which extend context |Gamma| by
asserting variable |x| has type |tau|. Typing is defined through
a judgment |Gamma /- t : tau|, stating that term |t| under
context |Gamma| has type |tau|.%
%
\footnote{We only formalize typed terms, not untyped ones, so
  that each term has a unique type. That is, in the relevant
  jargon, we use \emph{Church-style} typing as opposed to
  \emph{Curry-style} typing.
  Alternatively, we use an
  intrinsically-typed term representation.
  In fact, arguably we mechanize at
  once both well-typed terms and their typing derivations. This
  is even more clear in our mechanization; see discussion
  in~\cref{sec:sem-style-and-rw}.}
%
For a proper introduction to STLC we refer the reader to
\citet[Ch.~9]{Pierce02TAPL}. We will assume significant
familiarity with it.

\input{pldi14/fig-lambda-calc}

\paragraph{An extensible syntax of types}
In fact, the definition of base types can be mutually recursive
with the definition of types. So a language plugin might add as
base types, for instance, collections of elements of type |tau|,
products and sums of type |sigma| and type |tau|, and so on.
%
However, this mutual recursion must satisfy a few technical
restrictions to avoid introducing subtle inconsistencies, and
Agda cannot enforce these restrictions across modules. Hence, if
we define language plugins as separate modules in our
mechanization, we need to verify \emph{by hand} that such
restrictions are satisfied (which they are). See
\cref{sec:modularity-limits} for the gory details.

\begin{notation}
We typically omit type annotations on $\lambda$-abstractions,
that is we write |\x -> t| rather than |\(x : sigma) -> t|. Such
type annotations can often be inferred from context (or type
inference). Nevertheless, whenever we discuss terms of shape |\x
-> t|, we're in fact discussing |\(x : sigma) -> t| for some
arbitrary |sigma|. We write |\x -> t| instead of %
$\Gl x .\ t$, %
for consistency with the notation we use later for Haskell
programs.

We often omit |emptyCtx| from typing contexts with some assumptions.
For instance we write |x : tau1, y : tau2| instead of |emptyCtx,
x : tau1, y : tau2|.

We overload symbols (often without warning) when they can be
disambiguated from context, especially when we can teach modern
programming languages to disambiguate such overloadings. For
instance, we reuse |->| for lambda abstractions |\x -> t|,
function spaces |A -> B|, and function types |sigma -> tau|, even
though the first is the separator.
\end{notation}

\paragraph{Extensions}
In our examples, we will use some unproblematic syntactic sugar
over STLC, including let expressions, global definitions, type
inference, and we will use a Haskell-like concrete syntax. In
particular, when giving type signatures or type annotations in
Haskell snippets, we will use |::| to separate terms or variables
from their types, rather than |:| as in
$\lambda$-calculus. To avoid confusion, we never use |:| to
denote the constructor for Haskell lists.

At times, our concrete examples will use Hindley-Milner (prenex)
polymorphism, but this is also not such a significant extension.
A top-level definition using prenex polymorphism, that is of type
|forall alpha. tau| (where |alpha| is free in |tau|), can be
taken as sugar for a metalevel family of object-level programs,
indexed by type argument |tau1| of definitions of type |tau
[alpha := tau1]|. We use this trick without explicit mention in
our first implementation of incrementalization in
Scala~\citep{CaiEtAl2014ILC}.

\subsection{Denotational semantics for STLC}
\label{sec:denotational-sem}
To prove that incrementalization preserves the semantics of our
object-language programs, we define a semantics for STLC. We use
a naive set-theoretic denotational semantics: Since STLC is
strongly normalizing~\citep[Ch.~12]{Pierce02TAPL}, its semantics
need not handle partiality. Hence, we can use denotational
semantics but eschew using domain theory, and simply use sets
from the metalanguage (see \cref{sec:metalanguage}). Likewise, we
can use normal functions as domains for function types.

We first associate, to every type |tau|, a set of values
|eval(tau)|, so that terms of a type |tau| evaluate to values in
|eval(tau)|. We call set |eval(tau)| a \emph{domain}. Domains
associated to types |tau| depend on domain associated to base
types |iota|, that must be specified by language plugins
(\cref{req:base-types}).

\begin{definition}[Domains and values]
  The domain $\Eval{\Gt}$ of a type $\Gt$ is defined as in
  \cref{fig:correctness:values}. A value is a member of a domain.
\end{definition}

We let metavariables |u, v, ...|, |a, b, ...| range over members
of domains; we tend to use |v| for generic values and |a| for
values we use as a function argument. We also let metavariable
|f, g, ...| range over values in the domain for a function type.
At times we might also use metavariables |f, g, ...| to range
over \emph{terms} of function types; the context will clarify
what is intended.

Given this domain construction, we can now define a denotational
semantics for terms. The plugin has to provide the evaluation
function for constants. In general, the evaluation function
|eval(t)| computes the value of a well-typed term |t| given the
values of all free variables in |t|. The values of the free
variables are provided in an environment.

\begin{definition}[Environments]
  An environment $\Gr$ assigns values to the names of free
  variables.

  \begin{syntax}
    \Gr ::= \EmptyContext \mid \ExtendEnv{x}{v}
  \end{syntax}

  We write $\Eval{\GG}$ for the set of
  environments that assign values to the names bound in $\GG$
  (see \cref{fig:correctness:environments}).
\end{definition}

\paragraph{Notation}
We often omit |emptyRho| from environments with some assignments.
For instance we write |x = v1, y = v2| instead of |emptyRho, x =
v1, y = v2|.

\begin{definition}[Evaluation]
  \label{def:evaluation}
  Given $\Typing{t}{\tau}$, the meaning of $t$ is defined by the
  function $\Eval{t}$ of type $\Fun{\Eval{\GG}}{\Eval{\tau}}$
  in \cref{fig:correctness:evaluation}.
\end{definition}

This is a standard denotational semantics of the simply-typed
$\Gl$-calculus.

For each constant |c : tau|, the plugin provides |evalConst(c) :
eval(tau)|, the semantics of |c| (by \cref{req:constants}); since
constants don't contain free variables, |evalConst(c)| does not
depend on an environment.

% \begin{definition}[Program equivalence]
%   Take two terms |t1, t2| with the same context and type, that
%   is, such that |Gamma /- t1 : tau| and |Gamma /- t2 : tau|. We
%   say terms |t1, t2| are denotationally equivalent, and write |t1
%   `cong` t2|, if |eval(t1) = eval(t2)|.
% \end{definition}
% \begin{lemma}
%   Program equivalence is indeed an equivalence relation.
% \end{lemma}

We define a program equivalence across terms of the same type |t1
`cong` t2| to mean |eval t1 = eval t2|.

\begin{restatable}[Denotational equivalence]{definition}{denotEqual}
  \label{def:denot-equivalence}
  We say that two terms |Gamma /- t1 : tau| and |Gamma /- t2:
  tau| are denotationally equal, and write |Gamma //= t1 `cong` t2
  : tau| (or sometimes |t1 `cong` t2|), if for all environments
  |rho : eval Gamma| we have that |eval t1 rho = eval t2 rho|.
\end{restatable}
\begin{remark}
  Beware that denotational equivalence cannot always be strengthened
  by dropping unused variables:
  that is, |Gamma, x : sigma //= t1 `cong` t2 : tau| does not
  imply |Gamma //= t1 `cong` t2 : tau|, even if |x| does not
  occur free in either |t1| or |t2|. Counterexamples
  rely on |sigma| being an empty type. For instance, we cannot weaken
  |x : emptyTau //= 0 `cong` 1 : Int| (where |emptyTau| is an
  empty type): this equality is only true vacuously, because
  there exists no environment for context |x : emptyTau|.
\end{remark}

\subsection{Weakening}
While we don't discuss our formalization of variables in full, in
this subsection we discuss briefly weakening on STLC terms and
state as a lemma that weakening preserves meaning. This lemma is needed in
a key proof, the one of \cref{thm:derive-correct}.

As usual, if a term |t| is well-typed in a given context
|Gamma1|, and context |Gamma2| extends |Gamma1| (which we
write as |Gamma1 `preceq` Gamma2|), then |t| is also well-typed in
|Gamma2|.
\begin{lemma}[Weakening is admissible]
  \label{lem:weakening}
  The following typing rule is admissible:
\begin{typing}
  \Rule[Weaken]
  { |Gamma1 /- t : tau|\\
    |Gamma1 `preceq` Gamma2|}
  {|Gamma2 /- t : tau|}
\end{typing}
\end{lemma}

Weakening also preserves semantics. If a term |t| is typed in
context |Gamma1|, evaluating it requires an environment matching
|Gamma1|. So if we weaken |t| to a bigger context |Gamma2|,
evaluation requires an extended environment matching |Gamma2|,
and is going to produce the same result.
\begin{lemma}[Weakening preserves meaning]
  \label{lem:weaken-sound}
  Take |Gamma1 /- t : tau| and |rho1 : eval(Gamma1)|. If |Gamma1
  `preceq` Gamma2| and |rho2 : eval(Gamma2)| extends |rho1|, then
  we have that
  \[|eval(t) rho1 = eval(t) rho2|.\]
\end{lemma}

Mechanize these statements and their proofs requires some care.
We have a meta-level type |Term Gamma tau| of object terms having
type |tau| in context |Gamma|. Evaluation has type |eval(param) :
Term Gamma tau -> eval(Gamma) -> eval(tau)|, so |eval(t) rho1 =
eval(t) rho2| is not directly ill-typed.
%
To remedy this, we define formally the subcontext relation
|Gamma1 `preceq` Gamma2|, and an explicit operation that weakens
a term in context |Gamma1| to a corresponding term in bigger
context |Gamma2|, |weaken : Gamma1 `preceq` Gamma2 -> Term Gamma1
tau -> Term Gamma2 tau|.
%
We define the subcontext relation |Gamma1 `preceq` Gamma2| as a
judgment using \emph{order preserving embeddings}.%
\footnote{As mentioned by James Chapman at
  \url{https://lists.chalmers.se/pipermail/agda/2011/003423.html},
  who attributes them to Conor McBride.} We refer to our
mechanized proof for details, including auxiliary definitions and
relevant lemmas.

\subsection{Substitution}
Some facts can be presented using (capture-avoiding) substitution
rather than environments, and we do so at some points, so let us
fix notation. We write |t [x := s]| for the result of
substituting variable |x| in term |t| by term |s|.

We have mostly avoided mechanizing proofs about substitution, but
we have mechanized substitution following
\citet{Keller2010hereditary} and proved the following
substitution lemma:
\begin{lemma}[Substitution lemma]
  For any term |Gamma /- t : tau|, variable |x :
  sigma| bound in |Gamma|, we write |Gamma - x| for the result of
  removing variable |x| from |Gamma| (as defined by \citeauthor{Keller2010hereditary}).
  Take term |Gamma - x /- s : sigma|, and
  environment |rho : eval (Gamma - x)|.
  Then, we have that substitution and evaluation commute as follows:
  \[|eval (t [x := s]) rho = eval t (rho, x = eval s rho)|.\]
\end{lemma}
% subst-lemma : ∀ {σ τ Γ} (t : Term Γ τ) (x : Var Γ σ) s rho → ⟦ subst t x s ⟧Term rho ≡ ⟦ t ⟧Term (extend-env x rho (⟦ s ⟧Term rho))

\subsection{Discussion: Our mechanization and semantic style}
\label{sec:sem-style-and-rw}
To formalize meaning of our programs, we use denotational
semantics while nowadays most prefer operational semantics, in
particular small-step. Hence, we next justify our choice and
discuss related work.

We expect we could use other semantics techniques, such as
big-step or small-step semantics. But at least for such a simple
object language, working with denotational semantics as we use it
is easier than other approaches in a proof assistant, especially
in Agda.

\begin{itemize}
\item Our semantics |eval(param)| is a function and not a
  relation, like in small-step or big-step semantics.
\item It is clear to Agda that our semantics is a total function,
  since it is structurally recursive.
\item Agda can normalize |eval(param)| on partially-known terms
  when normalizing goals.
\item The meanings of our programs are well-behaved Agda
  functions, not syntax, so we know ``what they mean'' and need
  not prove any lemmas about it. We need not prove, say, that
  evaluation is deterministic.
\end{itemize}

In Agda, the domains for our denotational semantics are simply
Agda types, and semantic values are Agda values---in other words,
we give a denotational semantics in terms of type
theory.
Using denotational semantics allows us to state the specification
of differentiation directly in the semantic domain, and take
advantage of Agda's support for equational reasoning for proving
equalities between Agda functions.

\paragraph{Related work}
Our variant is used for instance by
\citet{McBride2010outrageous}, who attribute it to
\citet{Augustsson1999exercise} and \citet{Altenkirch1999monadic}.
In particular, \citet{Altenkirch1999monadic} already define our
type |Term Gamma tau| of simply-typed $\lambda$-terms |t|,
well-typed with type |tau| in context |Gamma|, while
\citet{Augustsson1999exercise} define semantic domains by
induction over types.
\citet{Benton2012strongly} and \citet{Allais2017typeandscope}
also discuss this approach to formalizing $\lambda$ terms, and
discuss how to best prove various lemmas needed to reason, for
instance, about substitution.

More in general, similar approaches are becoming more common when
using proof assistants. Our denotational semantics could be
otherwise called a \emph{definitional interpreter} (which is in
particular compositional), and mechanized formalizations using a
variety of definitional interpreters are nowadays often
advocated, either using denotational
semantics~\citep{Chlipala08}, or using \emph{functional} big-step
semantics. Functional semantics are so convenient that their use
has been advocated even for languages that are \emph{not}
strongly normalizing~\citep{Owens2016functional,Amin2017}, even
at the cost of dealing with step-indexes.

\subsection{Language plugins}
\label{sec:lang-plugins}
Our object language is parameterized by \emph{language plugins} (or just
plugins) that encapsulate its domain-specific aspects.

In our examples, our language plugin will typically support
integers and primitive operations on them. However, our plugin
will also support various sorts \emph{collections} and base
operations on them. Our first example of collection will be
\emph{bags}. Bags are unordered collections (like sets) where
elements are allowed to appear more than once (unlike in sets), and
they are also called multisets.

Our formalization is parameterized over one language plugin
providing all base types and primitives. In fact, we expect a
language plugin to be composed out of multiple language plugins
merged together~\citep{ErdwegGR12}. Our mechanization is mostly
parameterized over language plugins, but see
\cref{sec:modularity-limits} for discussion of a few limitations.

The sets of base types and primitive
constants, as well as the types for primitive constants, are
on purpose left unspecified and only defined by plugins ---
they are \emph{extensions points}.
%
We write some extension points using ellipses (``$\ldots$''), and
other ones by creating names, which typically use $^\CONST$ as a
superscript.

A plugin defines a set of base types $\iota$, primitives $c$ and
their denotational semantics $\EvalConst{c}$. As usual, we
require that $\EvalConst{c}: \Eval{\tau}$ whenever $c : \tau$.

\paragraph{Summary}
To sum up the discussion of plugins, we collect formally the plugin requirements we have
mentioned in this chapter.
\begin{restatable}[Base types]{requirement}{baseTypes}
  \label{req:base-types}
   There is a set of base types |iota|, and for each there is a domain |eval(iota)|.
\end{restatable}
\begin{restatable}[Constants]{requirement}{constants}
  \label{req:constants}
  There is a set of constants |c|. To each constant is associated
  a type |tau|, such that the constant has that type, that is
  $\ConstTyping{c}{\tau}$, and the constants' semantics matches
  that type, that is $\EvalConst{c}: \Eval{\tau}$.
\end{restatable}

% It will also need to explain how to support incrementalization for
% For each
% base type and base primitive, a language plugin
% will also have to provide support for incrementalization

% \begin{itemize}
% \item a representation for changes for each base type, and a
%   derivative for each primitive;
% \item proofs of correctness for its components.
% \end{itemize}

% Once a plugin
% specifies the primitives and how each is incrementalized,
% \ILC\ can
% and
% \ILC\ can glue together these simple derivatives in such a way
% that
% derivatives for arbitrary STLC expressions
% using these primitives can be computed.

% For instance, a language plugin could add support for a base type
% of integers |Int| with associated primitives

% In this chapter we will assume a language plugin

% Our |grand_total| example requires a plugin that provides a types for integers
% and bags and primitives such that we can implement |sum| and
% |merge|.

% Our first implementation and our first correctness proof are
% explicitly modularized to be parametric in the plugins, to
% clarify precisely the interface that plugins must satisfy.

After discussing the metalanguage of our proofs, the object
language we study, and its semantics, we begin discussing
incrementalization in next chapter.
