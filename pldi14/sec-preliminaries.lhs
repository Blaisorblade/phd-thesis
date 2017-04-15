% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter[Preliminaries]{Preliminaries: syntax and semantics of
  simply-typed λ-calculus}
\label{sec:preliminaries}

Before discussing how we incrementalize programs and proving that
our incrementalization technique gives correct results, we define
what foundation we use for our proofs and what programs we
study.

We mechanize our correctness proof using Agda, hence we use Agda
also as our foundation. We discuss what this means in
\cref{sec:metalanguage}.

Our object language is a standard simply-typed $\lambda$-calculus
(STLC)~\citep[Ch. 9]{Pierce02TAPL},
parameterized over base types and constants. We term the set of
base types and constants a \emph{language plugin} (see
\cref{sec:lang-plugins}). In our examples we assume that the
language plugins supports needed base types and constants.
Moreover, we will later add further requirements to language
plugins, to support incrementalization of the features they add.
We use a set-theoretic denotational semantics rather than
operational semantics.

At this point, readers might want to skip to \cref{sec:intro}
right away, or focus on denotational semantics; if needed, they
might want to come back here where needed.

\section{Our proof meta-language}
\label{sec:metalanguage}
In this section we describe the logic (or meta-language) used in our
\emph{mechanized} correctness proof.

First, as usual, we distinguish between ``formalization'' (which
refers to on-paper formalized proofs) and ``mechanization''
(which refers to proofs encoded in the language of a proof
assistant for computer-aided \emph{mechanized} verification).

To prove the correctness of \ILC, we provide a mechanized proof
in Agda~\citep{agda-head}. Agda is an implementation of
intensional Martin-Löf type theory, so our proofs use a
type-theoretic foundation.

At times, we use conventional set-theoretic language to discuss
our proofs, but the differences are only superficial. For
instance, we might talk about a set of elements |S| and with
elements such as |s `elem` S|, though we always mean that |S| is
a type in our metalanguage, and that |s : S|. Talking about sets
avoids ambiguity between types of our meta-language and types of
our object-language (that we discuss next in
\cref{sec:intro-stlc}).

In our examples we consider a language plugin supporting
\emph{bags}, a type of collection (described in
\cref{sec:motiv-example}). We extend our logic by postulating a
few standard axioms on the implementation of bags, to avoid
proving correct an implementation of bags, or needing to account
for different values representing the same bag (such different
values typically arise when implementing bags as search trees).

\subsection{Type theory versus set theory}
Martin-Löf type theory is dependently typed, so we can form the
dependent function type |(x : A) -> B| where |x| can appear free
in |B|. Dependent function types are a powerful generalization of
type |A -> B|: Such a type guarantees that if we apply a function
|f : (x : A) -> B| to an argument |a : A|, the result has type |B
[ x := a ]|, that is |B| where |x| is substituted by |a|. We will
at times use dependent types in our presentation.

For our purposes, the other differences between set theory and
type theory affecting our formalization are limited:
\begin{itemize}
\item We do not postulate the law of excluded middle, so our
  logic is constructive.
\item Unlike set theory, type theory is proof-relevant: that is,
  proofs are first-class mathematical objects.
\item Instead of sets, we use types; instead of subsets
  $\{x \in A \mid P(x)\}$, we must use $\Sigma$-types
  $\Sigma (x : A) P(x)$ which contain pairs of elements $x$ and
  proofs they satisfy predicate $P$.
\item In set theory we can assume functional extensionality, that
  is, that functions that give equal results on all equal inputs
  are equal themselves. Intuitionistic type theory does not prove
  functional extensionality, so we need to add it as a postulate.
  This postulate is known to be consistent with Agda's type
  theory~\citep{Hofmann96}, hence it is safe to assume in Agda%
  \footnote{\url{http://permalink.gmane.org/gmane.comp.lang.agda/2343}}.
\end{itemize}

To handle binding issues in our object language, our
formalization uses typed de Brujin indexes, because this
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
simply-typed $\Gl$-calculus (STLC).

We recall the syntax and typing rules of STLC in
\cref{fig:lambda-calc:syntax,fig:lambda-calc:typing}, together
with the metavariables we use. Language plugins define base types
|iota| and constants |c|. Types can be base types |iota| or
function types |sigma -> tau|. Terms can be constants |c|,
variables |x|, function applications |t1 t2| or lambda
abstractions |\x -> t|. To describe assumptions on variable types
when typing terms, we define typing contexts |Gamma| as being
either empty |emptyCtx|, or as context extensions |Gamma, x :
tau|, which extend context |Gamma| by asserting variable |x| has
type |tau|. Typing is defined through a judgment |Gamma /- t :
tau|, stating that term |t| under typing context |Gamma| has type
|tau|. For a more proper introduction to STLC we refer the reader
to \citet[Ch. 9]{Pierce02TAPL}.

\input{pldi14/fig-lambda-calc}

In fact, the definition of base types might be mutually recursive
with the definition of types. So a language plugin might add as
base types, for instance, collections of elements of type |tau|,
products and sums of type |sigma| and type |tau|, and so on.
%
However, this mutual recursion must satisfy a few technical
restrictions, and dividing mutually recursive types into
different modules runs into a few obstacles we do not fully
address in practice. See \cref{sec:modularity-limits} for the gory details.

\subsection{Denotational semantics for STLC}
\label{sec:denotational-sem}
To prove that incrementalization preserves the final results of
our object-language programs, we need to specify a semantics for
STLC. To this end we use a naive set-theoretic denotational semantics. Since STLC is
strongly normalizing~\citep[Ch. 12]{Pierce02TAPL}, our semantics need not
handle partiality, in particular we can eschew
using domain theory. Instead, we simply use sets, as provided by
the ambient theory (see \cref{sec:metalanguage} for discussion).

We first associate, to every type |tau|, a set of values
|eval(tau)|, so that terms of a type |tau| evaluate to values in
|eval(tau)|. We call set |eval(tau)| a \emph{domain}. Domains
associated to types |tau| depend on domain associated to base
types |iota|, that must be specified by language plugins.

Defining domains to collect values is standard in denotational
semantics, but usually domains are not just sets, but they must
be enriched by additional structure used to represent
nonterminating programs. However, since our calculus is strongly
normalizing and all functions are total, we can avoid using
domain theory or other techniques to model partiality: our
domains are simply sets. Likewise, we can use normal
functions as the domain of function types.

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

  We write $\Eval{\GG}$ for the set of environments that assign
  values to the names bound in $\GG$ (see
  \cref{fig:correctness:environments}).
\end{definition}


\begin{definition}[Evaluation]
  \label{def:evaluation}
  Given $\Typing{t}{\tau}$, the meaning of $t$ is defined by the
  function $\Eval{t}$ of type $\Fun{\Eval{\GG}}{\Eval{\tau}}$
  in \cref{fig:correctness:evaluation}.
\end{definition}

This is a standard denotational semantics of the simply-typed
$\Gl$-calculus.

For each constant |c : tau|, the plugin provides |evalConst(c) :
eval(tau)|, the semantics of |c|; since constants don't contain
free variables, |evalConst(c)| does not depend on an environment.

% We define a program equivalence across terms of the same type |t1
% `cong` t2| to mean |eval(t1) = eval(t2)|.

% \begin{definition}[Program equivalence]
%   Take two terms |t1, t2| with the same context and type, that
%   is, such that |Gamma /- t1 : tau| and |Gamma /- t2 : tau|. We
%   say terms |t1, t2| are denotationally equivalent, and write |t1
%   `cong` t2|, if |eval(t1) = eval(t2)|.
% \end{definition}
% \begin{lemma}
%   Program equivalence is indeed an equivalence relation.
% \end{lemma}

In our examples, we will use some unproblematic syntactic sugar
over STLC, including let expressions, global definitions, type
inference, and we will use a Haskell-like concrete syntax. In
particular, when giving type signatures or type annotations in
Haskell snippets, we will use |::| to separate terms or variables
from their types, rather than |:| as in
$\lambda$-calculus.\pg{Reconsider.}
%
At times, our concrete examples will use Hindley-Milner
polymorphism, but this is also not a significant extension. A
polymorphic definition of type |forall alpha. tau| (where |alpha|
is free in |tau|) can be taken as sugar for a family, indexed by
type argument |tau1| of definitions of type |tau [alpha :=
tau1]|; we use this trick without explicit mention in our first
implementation of incrementalization in
Scala~\citep{CaiEtAl2014ILC}.

\subsection{Weakening}
While we don't discuss our formalization of variables in full, in
this subsection we discuss briefly weakening on STLC terms and
state as a lemma that weakening preserves meaning. This lemma is needed in
a key proof, the one of \cref{thm:correct-derive}.

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

\subsection{Discussion: Our choice of semantics style}
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

Our variant is used for instance by
\citet{McBride2010outrageous}, who attribute it to
\citet{Augustsson1999exercise} and \citet{Altenkirch1999monadic}.
In particular, \citet{Altenkirch1999monadic} already define our
type |Term Gamma tau| of simply-typed lambda terms |t|,
well-typed with type |tau| in context |Gamma|, while
\citet{Augustsson1999exercise} defines semantic domains by
induction over types.\footnote{We formalize through meta-level
  type |Term Gamma tau| only well-typed terms, that is our
  formalization of typing is Church-style. In fact, arguably
  |Term Gamma tau| describes at once both well-typed terms and
  their typing derivations.}

More in general, similar approaches are becoming more common when
using proof assistants. Our denotational semantics could be
otherwise called a \emph{definitional interpreter} (which is in
particular compositional), and mechanized formalizations using a
variety of definitional interpreters are nowadays often
advocated, either using denotational
semantics~\citep{Chlipala08}, or using \emph{functional} big-step
semantics, even for languages that are not strongly
normalizing~\citep{Owens2016functional,Amin2017}.

\subsection{Language plugins}
\label{sec:lang-plugins}
Our STLC is parameterized by \emph{language plugins} (or just
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
We use ellipses (``$\ldots$'') for some extension points, and
give names to others when needed to refer to them.

A plugin defines a set of base types $\iota$, primitives $c$ and
their denotational semantics $\EvalConst{c}$. As usual, we
require that $\EvalConst{c}: \Eval{\tau}$ whenever $c : \tau$.

\paragraph{Summary}
To sum up, we collect formally the plugin requirements we have
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
% |merge|.\pg{Elaborate.}

% Our first implementation and our first correctness proof are
% explicitly modularized to be parametric in the plugins, to
% clarify precisely the interface that plugins must satisfy.
