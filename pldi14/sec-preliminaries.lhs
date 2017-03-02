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

Our object language is a standard simply-typed $\lambda$-calculus (STLC),
parameterized over base types and constants. We term the set of
base types and constants a \emph{language plugin} (see
\cref{sec:lang-plugins}). In our examples we assume that the
language plugins supports needed base types and constants.
Moreover, we will later add further requirements to language
plugins, to support incrementalization of the features they add.

At this point, readers might want to skip to \cref{sec:intro}
right away; if needed, they might want to come back here where
needed. Language plugins are the least standard presentation
choice.

\section{Our proof meta-language}
\label{sec:metalanguage}
In this section we describe the meta-language used in our
correctness proof.
To prove the correctness of \ILC, we provide a mechanized proof
in Agda~\citep{agda-head}. Agda is an implementation of
intensional Martin-Löf type theory.

To make our proofs more accessible, we present them in terms of
set theory, though for convenience we still use (informally)
dependently-typed type signatures where useful. For readers
familiar with type theory, we will also discuss at some points
relevant differences between the two presentations; however,
readers unfamiliar with type theory can skip such discussions
without prejudice.

In our examples we consider a language plugin supporting
\emph{bags}, a type of collection (described in
\cref{sec:motiv-example}). We extend our logic by postulating a
few standard axioms on the implementation of bags, to avoid
proving correct an implementation of bags, or needing to account
for different values representing the same bag (such different
values typically arise when implementing bags as search trees).

\subsection{Type theory versus set theory}
For our purposes, the differences between set theory and type
theory, and the two presentations of our formalization, are
limited:
\begin{itemize}
\item We use intuitionistic logic, so we do not use the law of
  excluded middle.
\item Unlike set theory, type theory is proof-relevant: that is,
  proofs are first-class mathematical objects.
\item Instead of sets, we use types; instead of subsets
  $\{x \in A \mid P(x)\}$, we must use $\Sigma$-types
  $\Sigma (x : A) P(x)$ which contain pairs of elements $x$ and
  proofs they satisfy predicate $P$.
\item We postulate functional extensionality,
  that is, functions that give equal results on any equal inputs
  are equal themselves. This postulate is known to be consistent
  with Agda's type theory~\citep{Hofmann96}, hence it is safe to
  assume in Agda%
  \footnote{\url{http://permalink.gmane.org/gmane.comp.lang.agda/2343}}.
\end{itemize}

To handle binding issues in our object language, our
formalization uses typed de Brujin indexes, because this
techniques takes advantage of Agda's support for type refinement
in pattern matching. On top of that, we implement a HOAS-like
frontend, that we use for writing specific terms.


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
\cref{fig:lambda-calc:syntax,fig:lambda-calc:typing}.
Language plugins define base types and constants. For a more
proper introduction to STLC we refer the reader to \citet[Ch.
9]{Pierce02TAPL}.

\input{pldi14/fig-lambda-calc}

\subsection{Denotational semantics for STLC}
\label{sec:denotational-sem}
To prove that incrementalization preserves the final results of
our object-language programs, we need to specify a semantics for
STLC. To this end we use a denotational semantics. Since STLC is
strongly normalizing~\citep[Ch. 12]{Pierce02TAPL} we need not
handle partiality in our semantics, in particular we can eschew
using domain theory. Instead, we simply use sets, as provided by
the ambient theory (see \cref{sec:metalanguage} for discussion).

% Using denotational semantics allows us to state the specification
% of differentiation directly in the semantic domain, and take
% advantage of Agda's support for equational reasoning for proving
% equalities between Agda functions.

% The domains for our denotational semantics
% are simply Agda types, and semantic values are Agda values---in
% other words, we give a denotational semantics in terms of type
% theory.\footnote{Alternatively, some would call such a semantics
%   a definitional interpreter~\citep{Amin2017}.}

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

\begin{definition}[Domains]
  The domain $\Eval{\Gt}$ of a type $\Gt$ is defined as in
  \cref{fig:correctness:values}.
\end{definition}

Given this domain
construction, we can now define a denotational semantics for
terms. The plugin has to provide the evaluation function for
constants. In general, the evaluation function |eval(t)| computes the value of a
well-typed term |t| given the values of all free variables in
|t|. The values of the free variables are provided in an
environment.

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
inference, and we will use a Haskell-like concrete syntax.
\pg{Let expressions, global definitions, HM polymorphism...}


\subsection{Language plugins}
\label{sec:lang-plugins}
Our STLC is parameterized by \emph{language plugins} (or just
plugins) that encapsulate its domain-specific aspects. For instance

The sets of base types and primitive
constants, as well as the typing rules for primitive constants, are
on purpose left unspecified and only defined by plugins --- they are \emph{extensions points}.
%
We use ellipses (``$\ldots$'') for some extension points, and
give names to others when needed to refer to them.

A plugin defines a set of base types $\iota$, primitives $c$ and
their denotational semantics $\EvalConst{c}$. As usual, we
require that $\EvalConst{c}: \Eval{\tau}$ whenever $c : \tau$.

Our formalization is parameterized over one language plugin
providing all base types and primitives. In fact, we expect a
language plugin to be composed out of multiple language plugins
merged together~\citep{ErdwegGR12}.

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
