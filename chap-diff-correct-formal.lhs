% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Changes and differentiation, formally}
\label{ch:derive-formally}
\input{pldi14/fig-differentiation}

To support incrementalization, in this chapter we introduce differentiation and
formally prove it correct. That is, we prove that |eval(derive(t))| produces
derivatives. As we explain in \cref{sec:derivative-formal}, derivatives
transform valid input changes into valid output changes (\cref{slogan:derive}).
Hence, we define what are valid changes (\cref{sec:changes-formally}). As we'll
explain in \cref{sec:validity-logical}, validity is a logical relation. As we
explain in \cref{sec:derive-correct-proof}, our correctness theorem is the
\emph{fundamental property} for the validity logical relation, proved by induction
over the structure of terms.
%
Crucial definitions or derived facts are summarized in \cref{fig:differentiation}.
%
Later, in \cref{ch:change-theory} we study consequences of correctness and
change operations.

All definitions and proofs in this and next chapter is mechanized in Agda,
except where otherwise indicated. To this writer, given these definitions all
proofs have become straightforward and unsurprising. Nevertheless, first
obtaining these proofs took a while. So we typically include full proofs.
We also believe these proofs clarify the meaning and consequences of our definitions.
To make proofs as accessible as possible, we try to provide enough detail that
our target readers can follow along \emph{without} pencil and paper, at the
expense of making our proofs look longer than they would usually be. As we
target readers proficient with STLC (but not necessarily proficient with logical
relations), we'll still omit routine steps needed to reason on STLC, such as
typing derivations or binding issues.

\section{Changes and validity}
\label{sec:changes-formally}
In this section we introduce formally (a) a description of changes; (b) a
definition of which changes are valid. We have already introduced informally in
\cref{ch:static-diff-intro} these notions and how they fit together. We next
define the same notions formally, and deduce their key properties.
Language plugins extend these definitions for base types and constants that they
provide.

To formalize the notion of changes for elements of a set |V|, we define the
notion of \emph{basic change structure} on |V|.

\begin{definition}[Basic change structures]
  \label{def:bchs}
  A basic change structure on set |V|, written |bchs(V)|, comprises:
  \begin{subdefinition}
  \item a change set |Dt^V|
  \item a ternary \emph{validity} relation |fromto V v1 dv v2|, for |v1, v2
    `elem` V| and |dv `elem` Dt^V|, that we read as ``|dv| is a valid change
    from source |v1| to destination |v2| (on set |V|)''.
  % \item a ternary relation called \emph{validity}.
  %   We say that
  %   We write this relation as |fromto V v1 dv
  %   v2|, where |v1, v2 `elem` V| and |dv `elem` Dt^V|, and say that |dv| is a
  %   valid change from source |v1| to destination |v2| (on set |V|).
  % \item a ternary relation called \emph{validity} among |V|, |Dt^V| and |V|.
  %   When this relation holds
  %   If |v1, v2
  %   `elem` V| and |dv `elem` DV|, and this relation holds, we write |fromto V v1
  %   dv v2| and say that |dv| is a valid change from source |v1| to destination
  %   |v2| (on set |V|).
  \end{subdefinition}
\end{definition}

\begin{example}
In \cref{ex:valid-bag-int,ex:invalid-nat} we exemplified
informally change types and validity on naturals, integers and
bags.\pg{revise if we add more examples.}
We define formally basic change structures on naturals and integers.
Compared to validity for integers, validity for naturals ensures that the
destination |v1 + dv| is again a natural. For instance, given source |v1 =
1|, change |dv = -2| is valid (with destination |v2 = -1|) only on integers, not
on naturals.
% \footnote{For convenience we're implicitly identifying naturals with
%   non-negative integers, ignoring the isomorphism between them.}
\end{example}
\begin{definition}[Basic change structure on integers]
  Basic change structure |bchs(Int)| on integers has integers as changes
  (|Dt^Int=Int|) and the following validity judgment.
\begin{typing}
  \Axiom
  {\validfromto{|Int|}{|v1|}{|dv|}{|v1 + dv|}}
\end{typing}
\end{definition}

\begin{definition}[Basic change structure on naturals]
  Basic change structure |bchs(Nat)| on naturals has integers as changes
  (|Dt^Nat=Int|) and the following validity judgment.
\begin{typing}
  \Rule{|v1 + dv >= 0|}
  {\validfromto{|Nat|}{|v1|}{|dv|}{|v1 + dv|}}
\end{typing}
\end{definition}

Intuitively, we can think of a valid change from |v1| to |v2| as a graph
\emph{edge} from |v1| to |v2|, so we'll often use graph terminology when
discussing changes. This intuition is robust and can be made fully
precise.\footnote{See for instance Robert Atkey's blog post~\citep{Atkey2015ILC}
  or Yufei Cai's PhD thesis~\citep{CaiPhD}.}
More specifically, a basic change structure on |V| can
be seen as a directed multigraph, having as vertexes the elements of |V|, and as
edges from |v1| to |v2| the valid changes |dv| from |v1| to |v2|. This is a
multigraph because our definition allows multiple edges between |v1| and |v2|.

A change |dv| can be valid from |v1| to |v2| and from |v3| to |v4|, but we'll
still want to talk about \emph{the} source and \emph{the} destination of a
change. When we talk about a change |dv| valid from |v1| to |v2|, value |v1| is
|dv|'s source and |v2| is |dv|'s destination. Hence we'll systematically quantify
theorems over valid changes |dv| with their sources |v1| and destination |v2|,
using the following notation.%
\footnote{If you prefer, you can tag a change with its source and destination by
  using a triple, and regard the whole triple |(v1, dv, v2)| as a change.
  Mathematically, this gives the correct results, but we'll typically not use
  such triples as changes in programs for performance reasons.}
\begin{notation}[Quantification over valid changes]
  We write \[|forall (fromto V v1 dv v2).  P|,\] and say ``for all (valid)
  changes |dv| from |v1| to |v2| on set |V| we have |P|'', as a shortcut for
  \[|forall
    v1, v2 `elem`| V, |dv `elem` Dt^V,|\text{ if }|fromto V v1 dv v2|\text{ then }P.\]

  Since we focus on valid changes, we'll omit the word ``valid'' when clear from context.
  In particular, a change from |v1| to |v2| is necessarily valid.
\end{notation}

We can have multiple basic change structures on the same set.
\begin{example}[Replacement changes]
\label{ex:replacement}
For instance, for any set |V| we can talk about \emph{replacement changes} on
|V|: a replacement change |dv = !v2| for a value |v1 : V| simply specifies
directly a new value |v2 : V|, so that |fromto V v1 (! v2) v2|. We read |!| as
the ``bang'' operator.

A basic change structure can decide to use only replacement changes (which can
be appropriate for primitive types with values of constant size), or to make
|Dt^V| a sum type allowing both replacement changes and other ways to describe a
change (as long as we're using a language plugin that adds sum types).
\end{example}

\paragraph{Nil changes}
Just like integers have a null element |0|, among changes there can be nil
changes:
\begin{definition}[Nil changes]
  \label{def:nil-changes}
  We say that |dv: Dt^V| is a nil change for |v: V| if |fromto V v dv v|.
\end{definition}

For instance, |0| is a nil change for any integer number |n|.
However, in general a change might be nil for an element but not
for another. For instance, the replacement change |!6| is a nil
change on |6| but not on |5|.

We'll say more on nil changes in \cref{sec:derivative-formal,sec:nil-changes-intro}.

\subsection{Function spaces}
Next, we define a basic change structure that we call |bchs(A) ->
bchs(B)| for an arbitrary function space |A -> B|, assuming we have basic change
structures for both |A| and |B|.
%
We claimed earlier that valid function changes map valid input changes to valid
output changes. We make this claim formal through next definition.
\begin{definition}[Basic change structure on |A -> B|]
  \label{def:basic-change-structure-funs}
  Given basic change structures on |A| and |B|, we define a basic change
  structure on |A -> B| that we write |bchs(A) -> bchs(B)| as follows:
  \begin{subdefinition}
  \item Change set |Dt^(A -> B)| is |A -> Dt^A -> Dt^B|.
  \item Function change |df| is valid from |f1|
    to |f2| (that is, |fromto (A -> B) f1 df f2|) if and only if,
    for all valid input changes |fromto A a1 da a2|, value |df a1 da| is a valid
    output change from |f1 a1| to |f2 a2| (that is, |fromto B (f1 a1) (df a1 da) (f2 a2)|).
  \end{subdefinition}
\end{definition}

% More precisely, |df| is a valid function change
% from |f1| to |f2| if, for all changes |da| from |a1| to |a2| on set |A|,
% value |df a1 da|
% is a valid change from |f1 a1| to |f2 a2|.

\begin{notation}[Applying function changes to changes]
  When reading out |df a1 da| we'll often talk for brevity about applying |df|
  to |da|, leaving |da|'s source |a1| implicit when it can be deduced from
  context.
\end{notation}

We'll also consider valid changes |df| for curried $n$-ary functions. We show
what their validity means for curried binary functions |f : A -> B -> C|. We
omit similar statements for higher arities, as they add no new ideas.
\begin{lemma}[Validity on |A -> B -> C|]
  \label{lem:validity-binary-functions}
  For any basic change structures |bchs(A)|, |bchs(B)| and |bchs(C)|, function
  change |df: ^^ Dt^(A -> B -> C)| is valid from |f1| to |f2| (that is, |fromto
  (A -> B -> C) f1 df f2|) \emph{if and only if} applying |df| to valid input
  changes |fromto A a1 da a2| and |fromto B b1 db b2| gives a valid output change
  \[|fromto C (f a1 b1) (df a1 da b1 db) (f a2 b2)|.\]
\end{lemma}
\begin{proof}
  The equivalence follows from applying the definition of function validity of |df| twice.

  That is: function change |df| is valid (|fromto (A -> (B -> C)) f1 df f2|) if
  and only if it maps valid input change |fromto A a1 da a2| to valid output
  change
  \[|fromto (B -> C) (f1 a1) (df a1 da) (f2 a2)|.
  \]
  In turn, |df a1 da| is a function change, which is valid if and only if
  it maps valid input change |fromto B b1 db b2| to
  \[|fromto C (f a1 b1) (df a1 da b1 db) (f a2 b2)|\]
  as required by the lemma.
\end{proof}

\subsection{Derivatives}
\label{sec:derivative-formal}
Among valid function changes, derivatives play a central role, especially in the
statement of correctness of differentiation.

\begin{definition}[Derivatives]
  \label{def:derivative-raw} 
  Given function |f: ^^ A -> B|, function |df: ^^ A -> Dt^A -> Dt^B| is a
  derivative for |f| if, for all changes |da| from |a1| to |a2| on set |A|, change
  |df a1 da| is valid from |f a1| to |f a2|.
\end{definition}

However, it follows that derivatives are nil function changes:

\begin{lemma}[Derivatives as nil function changes]
  \label{def:derivative}
  Given function |f: ^^ A -> B|, function |df: ^^ Dt^(A -> B)| is a derivative
  of |f| if and only if |df| is a nil change of |f| (|fromto (A -> B) f df f|).
\end{lemma}
\begin{proof}
  First we show that nil changes are derivatives.
  First, a nil change |fromto (A -> B) f df f| has the right type to be a derivative, because |A -> Dt^A -> Dt^B = Dt^(A -> B)|.
  Since |df| is a nil change from |f| to |f|, by definition it maps valid input changes
  |fromto A a1 da a2| to valid output changes
  |fromto B (f a1) (df a1 da) (f a2)|. Hence |df| is a derivative as required.

  In fact, all proof steps are equivalences, and by tracing them backward, we
  can show that derivatives are nil changes: Since a derivative |df| maps valid
  input changes |fromto A a1 da a2| to valid output changes |fromto B (f a1) (df
  a1 da) (f a2)|, |df| is a change from |f| to |f| as required.
\end{proof}

Applying derivatives to nil changes gives again nil changes. This fact is useful
when reasoning on derivatives. The proof is a useful exercise on using validity.
\begin{lemma}[Derivatives preserve nil changes]
  \label{lem:derivatives-nil-changes}
  For any basic change structures |bchs(A)| and |bchs(B)|,
  function change |df : Dt^(A -> B)| is a derivative of |f : A -> B| (|fromto (A
  -> B) f df f|) if and only if applying |df|
  to an arbitrary input nil change |fromto A a da a| gives a nil change
  %
  \[|fromto B (f a) (df a da) (f a)|.\]
\end{lemma}
\begin{proof}
  Just rewrite the definition of derivatives (\cref{def:derivative}) using the
  definition of validity of |df|.

  In detail, by definition of validity for function changes
  (\cref{def:basic-change-structure-funs}), |fromto (A -> B) f1 df f2| means
  that from |fromto A a1 da a2| follows |fromto B (f1 a1) (df a1 da) (f2 a2)|.
  Just substitute |f1 = f2 = f| and |a1 = a2 = a| to get the required
  equivalence.
\end{proof}

Also derivatives of curried $n$-ary functions |f| preserve nil changes. We only
state this formally for curried binary functions |f : A -> B -> C|; higher
arities require no new ideas.
\begin{lemma}[Derivatives preserve nil changes on |A -> B -> C|]
  \label{lem:binary-derivatives-nil-changes}
  For any basic change structures |bchs(A)|, |bchs(B)| and |bchs(C)|,
  Change |df : Dt^(A -> B -> C)| is a derivative of |f : A -> B -> C|
  \emph{if and only if}
  applying |df| to nil changes |fromto A a
  da a| and |fromto B b db b| gives a nil change
  \[|fromto C (f a b) (df a da b db) (f a b)|.\]
\end{lemma}
\begin{proof}
  Similarly to validity on |A -> B -> C| (\cref{lem:validity-binary-functions}),
  the thesis follows by applying twice the fact that derivatives preserve nil
  changes (\cref{lem:derivatives-nil-changes}).

  In detail, since derivatives preserve nil changes, |df| is a derivative if and
  only if for all |fromto A a da a| we have |fromto (B -> C) (f a) (df a da) (f
  a)|. But then, |df a da| is a nil change, that is a derivative, and since it
  preserves nil changes, |df| is a derivative if and only if for all |fromto A a
  da a| and |fromto B b db b| we have |fromto C (f a b) (df a da b db) (f a b)|.
\end{proof}

\subsection{Basic change structures on types}
After studying basic change structures in the abstract, we apply them to the
study of our object language.

For each type |tau|, we can define a basic change structure on domain
|eval(tau)|, which we write |bchs(tau)|. Language plugins must provide basic
change structures for base types. To provide basic change structures for
function types |sigma -> tau|, we use the earlier construction for basic change
structures |bchs(sigma) -> bchs(tau)| on function spaces |eval(sigma -> tau)|
(\cref{def:basic-change-structure-funs}).
\begin{definition}[Basic change structures on types]
  \label{def:bchs-types}
  For each type |tau| we associate a basic change structure on domain
  |eval(tau)|, written |bchs(tau)| through the following equations:
\begin{code}
  bchs(iota) = ...
  bchs(sigma -> tau) = bchs(sigma) -> bchs(tau)
\end{code}%
\end{definition}
\begin{restatable}[Basic change structures on base
  types]{requirement}{baseBasicChangeStructures}
  \label{req:base-basic-change-structures}
  For each base type |iota|, the plugin defines a basic change structure on
  |eval(iota)| that we write |bchs(iota)|.
\end{restatable}

Crucially, for each type |tau| we can define a type |Dt^tau| of changes, that we
call \emph{change type}, such that the change set |Dt^eval(tau)| is just the
domain |eval(Dt^tau)| associated to change type |Dt^tau|: |Dt^eval(tau) =
eval(Dt^tau)|. This equation allows writing change terms that evaluate directly
to change values.%
\footnote{Instead, in earlier proofs~\citep{CaiEtAl2014ILC} the values of change
  terms were not change values, but had to be related to change values through a
  logical relation; see \cref{sec:alt-change-validity}.}

\begin{definition}[Change types]
  \label{def:change-types}
  The change type |Dt^tau| of a type |tau| is defined as follows:
  % in \cref{fig:change-types}.
\begin{align*}
  |Dt ^ iota| &= \ldots\\
  |Dt ^ (sigma -> tau)| &= |sigma -> Dt ^ sigma -> Dt ^ tau|
\end{align*}
\end{definition}
\begin{lemma}[|Dt| and |eval(param)| commute on types]
  For each type |tau|, change set |Dt^eval(tau)| equals the domain of change
  type |eval(Dt^tau)|.
\end{lemma}
\begin{proof}
  By induction on types. For the case of function types, we simply prove
  equationally that |Dt^eval(sigma -> tau) = Dt^(eval(sigma) -> eval(tau)) =
  eval(sigma) -> Dt^eval(sigma) -> Dt^eval(tau) = eval(sigma) -> eval(Dt^sigma)
  -> eval(Dt^tau) = eval(sigma -> Dt^sigma -> Dt^tau) = eval(Dt^(sigma ->
  tau))|. The case for base types is delegates to plugins
  (\cref{req:base-change-types}).
\end{proof}
\begin{restatable}[Base change types]{requirement}{baseChangeTypes}
  \label{req:base-change-types}
  For each base type |iota|, the plugin defines a change type |Dt^iota| such
  that |Dt^eval(iota) = eval(Dt^iota)|.
\end{restatable}

We refer to values of change types as \emph{change values} or just \emph{changes}.

\begin{notation}
  We write basic change structures for types |bchs(tau)|, not |bchs(eval(tau))|,
  and |fromto tau v1 dv v2|, not |fromto (eval tau) v1 dv v2|. We also write
  consistently |eval(Dt^tau)|, not |Dt^eval(tau)|.
\end{notation}

% We proceed in four steps: we (a) define a type |Dt^tau| of changes, that we call
% \emph{change type}, (b) define a logical relation for validity that picks valid
% changes out of all elements of change types (c) define a basic change structure
% on each type (d) verify that the basic change structure on \pg{do it and *then*
%   summarize it.}

%We can also give \emph{equivalent} definitions for changes directly on types.

\subsection{Validity as a logical relation}
\label{sec:validity-logical}

Next, we show an equivalent definition of validity for values of terms, directly
by induction on types, as a ternary
\emph{logical} relation between a change, its source and
destination. A typical logical relation constrains \emph{functions} to
map related input to related outputs. In a twist, validity constrains
\emph{function changes} to map related inputs to related outputs.
\begin{definition}[Change validity]
  \label{def:ch-validity}
We say that |dv| is a (valid) change from |v1| to |v2| (on type |tau|), and write
|fromto tau v1 dv v2|, if |dv : eval(Dt^tau)|, |v1, v2 :
eval(tau)| and |dv| is a ``valid'' description of the difference
from |v1| to |v2|, as we define in \cref{fig:validity}.
\end{definition}

The key equations for function types are:
\begin{align*}
  |Dt^(sigma -> tau)| &= |sigma -> Dt ^ sigma -> Dt ^ tau|\\
  |fromto (sigma -> tau) f1 df f2| &=
  |forall (fromto sigma a1 da a2) . ^^ fromto tau (f1 a1) (df a1 da) (f2 a2)|
\end{align*}

\begin{remark}
  \label{rem:validity-logical-recursion}
  We have kept repeating the idea that valid function changes map valid input
  changes to valid output changes. As seen in
  \cref{sec:higher-order-intro,lem:validity-binary-functions,lem:binary-derivatives-nil-changes},
  such valid outputs can in turn be valid function changes. We'll see the same
  idea at work in \cref{lem:bchs-contexts-types}, in the correctness proof of
  |derive(param)|.

  As we have finally seen in this section, this definition of validity can be
  formalized as a logical relation, defined by induction on types. We'll later
  take for granted the consequences of validity, together with lemmas such as
  \cref{lem:validity-binary-functions}.
\end{remark}

\subsection{Change structures on typing contexts}
To describe changes to the inputs of a term, we now also introduce change
contexts |Dt^Gamma|, environment changes |drho : eval(Dt^Gamma)|, and validity
for environment changes |fromto Gamma rho1 drho rho2|.

A valid environment change from |rho1 : eval(Gamma)| to |rho2:
eval(Gamma)| is an environment |drho : eval(Dt^Gamma)| that
extends environment |rho1| with valid changes for each entry. We
first define the shape of environment changes through
\emph{change contexts}:

\begin{definition}[Change contexts]
  \label{def:change-contexts}
  For each context |Gamma| we define change context |Dt^Gamma| as
  follows:
\begin{align*}
  \Delta\EmptyContext &= \EmptyContext \\
  \Delta\Extend*{x}{\tau} &= \Extend[\Extend[\Delta\Gamma]{x}{\tau}]{\D x}{\Delta\tau}\text{.}
\end{align*}
\end{definition}

Then, we describe validity of environment changes via a judgment.
\begin{definition}[Environment change validity]
  \label{def:env-ch-validity}
  We define validity for environment changes through judgment |fromto Gamma rho1
  drho rho2|, pronounced ``|drho| is an environment change from |rho1| to |rho2|
  (at context |Gamma|)'', where |rho1, rho2 : eval(Gamma), drho :
  eval(Dt^Gamma)|, via the following inference rules:
\begin{typing}
  \Axiom
  {\validfromto{\EmptyContext}{\EmptyEnv}{\EmptyEnv}{\EmptyEnv}}

  \Rule{|fromto Gamma rho1 drho rho2|\\
    |fromto tau a1 da a2|}{
  \validfromto{\Extend{x}{\tau}}
  {\ExtendEnv*[\rho_1]{x}{a_1}}
  {\ExtendEnv*[\ExtendEnv[\D\rho]{x}{a_1}]{dx}{\D{a}}}
  {\ExtendEnv*[\rho_2]{x}{a_2}}}
\end{typing}
\end{definition}

\begin{definition}[Basic change structures for contexts]
  \label{def:bchs-contexts}
  To each context |Gamma| we associate a basic change structure on set
  |eval(Gamma)|. We take |eval(Dt^Gamma)| as change set and reuse validity on
  environment changes (\cref{def:env-ch-validity}).
\end{definition}
\begin{notation}
  We write |fromto Gamma rho1 drho rho2| rather than |fromto (eval(Gamma)) rho1
  drho rho2|.
\end{notation}

Finally, to state and prove correctness of differentiation, we are going to need
to discuss function changes on term semantics. The semantics of a term |Gamma /-
t : tau| is a function |eval(t)| from environments in |eval(Gamma)| to values in
|eval(tau)|. To discuss changes to |eval t| we need a basic change structure on
function space |eval(Gamma) -> eval(tau)|.
\begin{lemma}%[Basic change structures for contexts and types]
  \label{lem:bchs-contexts-types}
  The construction of basic change structures on function spaces
  (\cref{def:basic-change-structure-funs}) associates to each context |Gamma|
  and type |tau| a basic change structure |bchs(Gamma) -> bchs(tau)| on function
  space |eval Gamma -> eval tau|.
\end{lemma}
\begin{notation}
As usual, we write the change set as |Dt^(eval Gamma -> eval tau)|; for
validity, we write |fromtosem Gamma tau f1 df f2| rather than |fromto (eval
Gamma -> eval tau) f1 df f2|.
\end{notation}

\section{Correctness of differentiation}
\label{sec:correct-derive}
In this section we state and prove correctness of
differentiation, a term-to-term transformation written
|derive(t)| that produces incremental programs. We recall that
all our results apply only to well-typed terms (since we
formalize no other ones).

Earlier, we described how |derive(param)| behaves through
\cref{slogan:derive}---here is it again, for reference:
%
\begin{fullCompile}
\sloganDerive*
\end{fullCompile}
\begin{partCompile}
\begin{restatable}{slogan}{sloganDerive}
  \label{slogan:derive}
  Term |derive(t)| maps input changes to output changes.
  That is, |derive(t)| applied to old base inputs and valid \emph{input changes}
  (from old inputs to new inputs) gives a valid \emph{output change} from |t|
  applied on old inputs to |t| applied on new inputs.
\end{restatable}
\end{partCompile}
In our slogan we do not specify what we meant by inputs, though we gave examples
during the discussion. We have now the notions needed for a more precise statement.
Term |derive t| must satisfy our slogan for
two sorts of inputs:
\begin{enumerate}
\item Evaluating |derive(t)| must map an environment change |drho| from
|rho1| to |rho2| into a valid result change |eval(derive(t)) drho|, going from
|eval(t) rho1| to |eval(t) rho2|.
\item As we learned since stating our slogan, validity is defined by recursion
over types. If term |t| has type |sigma -> tau|, change |eval(derive t) drho|
can in turn be a (valid) function change
(\cref{rem:validity-logical-recursion}). Function changes map valid changes for
\emph{their} inputs to valid changes for \emph{their} outputs.
\end{enumerate}

Instead of saying that |eval(derive t)| maps |fromto Gamma rho1 drho rho2| to a
change from |eval t rho1| to |eval t rho2|, we can say that function |evalInc t
= \rho drho -> eval(derive t) drho| must be a \emph{nil change} for |eval t|,
that is, a \emph{derivative} for |eval t|.
We give a name to this function change, and state |derive(param)|'s correctness
theorem.

\begin{definition}[Incremental semantics]
  \label{def:inc-semantics}
  We define the \emph{incremental semantics} of a well-typed term
  |Gamma /- t : tau| in terms of differentiation as:
  \[|evalInc t = (\rho1 drho -> eval(derive t) drho) : eval(Gamma)
    -> eval(Dt^Gamma) -> eval(Dt^tau)|.\]
\end{definition}

\begin{restatable}[|derive(param)| is correct]{theorem}{deriveCorrect}
  \label{thm:derive-correct}
  Function |evalInc t| is a derivative of |eval t|. That is, if
  |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |fromto tau (eval(t) rho1) (eval(derive t) drho) (eval(t)
  rho2)|.
\end{restatable}

For now we discuss this statement further; we defer the proof to
\cref{sec:derive-correct-proof}.

\begin{remark}[Why |evalInc| ignores |rho1|]
You might wonder why |evalInc t = \rho1 drho -> eval(derive(t)) drho| appears to
ignore |rho1|. But for all |fromto Gamma rho1 drho rho2|, change environment
|drho| extends |rho1|, which hence provides no further information. We are only
interested in applying |evalInc t| to valid environment changes |drho|, so
|evalInc t rho1 drho| can safely ignore |rho1|.
\end{remark}
\begin{remark}[Term derivatives]
  In \cref{ch:static-diff-intro}, we suggested that |derive t| only produced a
  derivative for closed terms, not for open ones. But |evalInc t = \rho drho ->
  eval(derive t) drho| is \emph{always} a nil change and derivative of |eval t|
  for any |Gamma /- t : tau|. There is no contradiction, because the
  \emph{value} of |derive t| is |eval(derive t) drho|, which is only a nil
  change if |drho| is a nil change as well. In particular, for closed terms
  (|Gamma = emptyCtx|), |drho| must equal the empty environment |emptyRho|,
  hence a nil change. If |tau| is a function type, |df = eval(derive t) drho|
  accepts further inputs; since |df| must be a valid function change, it will
  also map them to valid outputs as required by our \cref{slogan:derive}.
  Finally, if |Gamma = emptyCtx| and |tau| is a function type, then |df = eval
  (derive t) emptyRho| is a derivative of |f = eval t emptyRho|.

  We summarize this remark with the following definition and corollary.
\end{remark}
\begin{definition}[Derivatives of terms]
  For all closed terms of function type |/- t : sigma -> tau|, we call |derive t| the (term) derivative of |t|.
\end{definition}
\begin{restatable}[Term derivatives evaluate to
  derivatives]{corollary}{deriveCorrectClosed}
  % |derive(param)| on closed terms gives derivatives
  For all closed terms of function type |/- t : sigma -> tau|, function
  |eval(derive t) emptyRho| is a derivative of |eval t emptyRho|.
\end{restatable}
\begin{proof}
  Because |evalInc t| is a derivative (\cref{thm:derive-correct}), and applying
  derivative |evalInc t| to nil change |emptyRho| gives a derivative
  (\cref{lem:derivatives-nil-changes}).
\end{proof}
\begin{remark}
  We typically talk \emph{a} derivative of a function value |f : A -> B|, not
  \emph{the} derivative, since multiple different functions can satisfy the
  specification of derivatives. We talk about \emph{the derivative} to refer to
  a canonically chosen derivative. For terms and their semantics, the canonical
  derivative the one produced by differentiation. For language primitives, the
  canonical derivative is the one chosen by the language plugin under
  consideration.
\end{remark}

\Cref{thm:derive-correct} only makes sense if |derive(param)| has the right
static semantics:

\begin{restatable}[Typing of |derive(param)|]{lemma}{deriveTyping}
  \label{lem:derive-typing}
  Typing rule
  \begin{typing}
    \Rule[Derive]
    {|Gamma /- t : tau|}
    {|Dt ^ Gamma /- derive(t) : Dt ^ tau|}
  \end{typing}
  is derivable.
\end{restatable}

After we'll define |`oplus`|, in next chapter, we'll be able to relate |`oplus`|
to validity, by proving \cref{thm:valid-oplus}, which we state in advance here:
\begin{fullCompile}
\begin{restatable*}[|`oplus`| agrees with validity]{lemma}{validOplus}
  \label{thm:valid-oplus}
  If |fromto tau v1 dv v2| then |v1 `oplus` dv = v2|.
\end{restatable*}
\end{fullCompile}
\begin{partCompile}
\begin{restatable}[|`oplus`| agrees with validity]{lemma}{validOplus}
  \label{thm:valid-oplus}
  If |fromto tau v1 dv v2| then |v1 `oplus` dv = v2|.
\end{restatable}
\end{partCompile}

Hence, updating base result |eval(t) rho1| by change
|eval(derive(t)) drho| via |`oplus`| gives the updated result
|eval(t) rho2|.
\begin{fullCompile}
\begin{restatable*}[|derive(param)| is correct, corollary]{corollary}{deriveCorrectOplus}
  \label{thm:derive-correct-oplus}
  If |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |eval(t) rho1 `oplus` eval(derive(t)) drho = eval(t) rho2|.
\end{restatable*}
\end{fullCompile}
\begin{partCompile}
\begin{restatable}[|derive(param)| is correct, corollary]{corollary}{deriveCorrectOplus}
  \label{thm:derive-correct-oplus}
  If |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |eval(t) rho1 `oplus` eval(derive(t)) drho = eval(t) rho2|.
\end{restatable}
\end{partCompile} 
We anticipate the proof of this corollary:
\begin{proof}
  First, differentiation is correct (\cref{thm:derive-correct}), so under the hypotheses
  \[|fromto tau (eval(t) rho1) (eval(derive(t)) drho) (eval(t) rho2)|;\]
  that judgement implies the thesis \[|eval(t) rho1 `oplus` eval(derive(t)) drho = eval(t) rho2|\]
  because |`oplus`| agrees with validty (\cref{thm:valid-oplus}).
\end{proof}

\subsection{Plugin requirements}
Differentiation is extended by plugins on constants, so plugins
must prove their extensions correct.

\begin{restatable}[Typing of |deriveConst(param)|]{requirement}{constDifferentiation}
  \label{req:const-differentiation}
  For all $\ConstTyping{c}{\tau}$, the plugin defines
  |deriveConst(c)| satisfying |/- deriveConst(c) :
  Dt^tau|.
\end{restatable}

\begin{restatable}[Correctness of |deriveConst(param)|]{requirement}{deriveConstCorrect}
  \label{req:correct-derive-const}
  For all $\ConstTyping{c}{\tau}$, |eval(deriveConst(c))| is a derivative for
  |eval(c)|.
\end{restatable}
Since constants are typed in the empty context, and the only change for an empty environment is an empty environment, \cref{req:correct-derive-const} means that for all $\ConstTyping{c}{\tau}$ we have
\[|fromto tau (eval c emptyRho) (eval(deriveConst c) emptyRho) (eval c
  emptyRho)|.\]

\subsection{Correctness proof}
\label{sec:derive-correct-proof}
We next recall |derive(param)|'s definition and prove it satisfies
its correctness statement \cref{thm:derive-correct}.
%After stating on |derive(param)|, we define |derive(param)| and prove the requirements hold.
\begin{fullCompile}
\deriveDef*
\end{fullCompile}
\begin{partCompile}
\begin{restatable}[Differentiation]{definition}{deriveDef}
  \label{def:derive}
Differentiation is the following term transformation:
\deriveDefCore
where |deriveConst(c)| defines differentiation on primitives and
is provided by language plugins (see \cref{sec:lang-plugins}),
and |dx| stands for a variable generated by prefixing |x|'s
name with |d|, so that |derive(y) = dy| and so on.%
\end{restatable}
\end{partCompile}

Before correctness, we prove \cref{lem:derive-typing}:
\deriveTyping*
\begin{proof}
  The thesis can be proven by induction on the typing derivation
  |Gamma /- t : tau|. The case for constants is delegated to plugins in
  \cref{req:const-differentiation}.
\end{proof}

We prove \cref{thm:derive-correct} using a typical logical relations strategy.
We proceed by induction on term |t| and prove for each case that if
|derive(param)| preserves validity on subterms of |t|, then also |derive(t)|
preserves validity. Hence, if the input environment change |drho| is valid, then
the result of differentiation evaluates to valid change |eval(derive(t)) drho|.

Readers familiar with logical relations proofs should be able to reproduce this
proof on their own, as it is rather standard, once one uses the given
definitions. In particular, this proof resembles closely the proof of the
abstraction theorem or relational parametricity (as given by
\citet[Sec.~6]{Wadler1989theorems} or by \citet[Sec.~3.3,
Theorem~3]{Bernardy2011realizability}) and the proof of the fundamental theorem
of logical relations by \citet{Statman1985logical}.

Nevertheless, we spell this proof out, and use it to motivate how
|derive(param)| is defined, more formally than we did in
\cref{sec:informal-derive}. For each case, we first give a short proof sketch,
and then redo the proof in more detail to make the proof easier to follow.

\deriveCorrect*
\begin{proof}
  By induction on typing derivation |Gamma /- t : tau|.
  \begin{itemize}
  \item Case |Gamma /- x : tau|. The thesis is that |eval(derive(x))|
    is a derivative for |eval(x)|, that is |fromto tau (eval(x)
    rho1) (eval(derive(x)) drho) (eval(x) rho2)|.
    Since |drho| is a valid environment change
    from |rho1| to |rho2|, |eval(dx) drho| is a valid change
    from |eval(x) rho1| to |eval(x) rho2|. Hence, defining |derive(x) =
    dx| satisfies our thesis.
  \item Case |Gamma /- s t : tau|.
    %
    The thesis is that |eval(derive(s t))| is a derivative for |eval(s t)|, that is
    |fromto tau (eval(s t) rho1) (eval(derive(s t)) drho) (eval(s t) rho2)|.
    %
    By inversion of typing, there is some type |sigma| such that
    |Gamma /- s : sigma -> tau| and |Gamma /- t : sigma|.

    To prove the thesis, in short, you can apply the inductive
    hypothesis to |s| and |t|,
    obtaining respectively that |eval(derive s)| and |eval(derive t)|
    are derivatives for |eval(s)| and |eval(t)|. In particular, |eval(derive s)|
    evaluates to a validity-preserving function change.
    Term |derive (s t)|, that is |(derive s) t (derive t)|, applies
    validity-preserving function |derive s| to valid
    input change |derive t|, and this produces a valid change for
    |s t| as required.

    In detail, our thesis is that for all |fromto Gamma rho1 drho rho2| we have
    \[|fromto tau (eval(s t) rho1) (eval(derive(s t)) drho) (eval(s t) rho2)|,\]
    %
    where |eval(s t) rho = (eval(s) rho) (eval(t) rho)| and
    \begin{equational}
      \begin{code}
   eval(derive(s t)) drho
=  eval(derive(s) t (derive(t))) drho
=  (eval(derive(s)) drho) (eval(t) drho) (eval(derive(t)) drho)
=  (eval(derive(s)) drho) (eval(t) rho1) (eval(derive(t)) drho)
      \end{code}%
    \end{equational}%
    The last step relies on |eval(t) drho = eval(t) rho1|. Since
    weakening preserves meaning (\cref{lem:weaken-sound}), this
    follows because |drho : eval(Dt^Gamma)| extends |rho1 :
    eval(Gamma)|, and |t| can be typed in context |Gamma|.

    Our thesis becomes
    \[|fromto tau (eval s rho1 (eval t rho1)) (eval(derive s) drho (eval t rho1) (eval(derive t) drho)) (eval s rho2 (eval t rho2))|.\]

    By the inductive
    hypothesis on |s| and |t| we have
    \begin{gather*}
      |fromto (sigma -> tau) (eval(s) rho1) (eval(derive(s)) drho) (eval(s) rho2)| \\
      |fromto sigma (eval(t) rho1) (eval(derive(t)) drho) (eval(t) rho2)|.
    \end{gather*}
    Since |eval(s)| is a function, its validity
    means
    \[|forall (fromto sigma a1 da a2). ^^ fromto (tau) (eval s rho1 a1) (eval(derive s) drho a1 da) (eval s rho2 a2)|.\]

    Instantiating in this statement the hypothesis |fromto sigma a1 da a2| by
    |fromto sigma (eval t rho1) (eval(derive t) drho) (eval t rho2)| gives the
    thesis.

  \item Case |Gamma /- \x -> t : sigma -> tau|. By inversion of typing,
    |Gamma , x : sigma /- t : tau|.
    By typing of |derive(param)| you can show that
    \[|Dt^Gamma, x : sigma, dx : Dt^sigma /- derive(t): Dt^tau|.\]

    % In short, our thesis is that |eval(derive(\x -> t))| is a derivative
    % for |eval(\x -> t)|.
    % Because we pick |derive(\x -> t) = \x dx -> derive(t)|, and because of how validity is defined on functions,
    % our thesis is equivalent that |eval(derive t)| must be
    % By induction on |t| we know that
    % |eval(derive(t))| is a derivative for |eval(t)|.
    % %
    % We show that our thesis, that is correctness of |derive(\x ->
    % t)|, is equivalent to correctness of |derive(t)|, because we
    % pick |derive(\x -> t) = \x dx -> derive(t)|.

    In short, our thesis is that |evalInc(\x -> t) = \rho1 drho -> eval(\x dx -> derive(t)) drho| is a
    derivative of |eval(\x -> t)|. After a few simplifications, our thesis reduces to
    \[|fromto tau (eval t (rho1, x = a1))
      (eval(derive t) (drho, x = a1, dx = da))
      (eval t (rho2, x = a2))|\]
    for all |fromto Gamma rho1 drho rho2| and |fromto sigma a1 da a2|.
    But then, the thesis is simply that |evalInc t| is the derivative of |eval
    t|, which is true by inductive hypothesis.

    % Now, |eval(\x
    % dx -> derive(t)) = \drho a da -> eval(derive(t)) (drho, x = a, dx = da)| is just a curried version of |eval(derive(t))|; to wit,
    % observe their meta-level types: \pg{not because of the types.}
    % \begin{align*}
    % |eval(derive(t)) : eval(Dt ^ Gamma , x : sigma,
    %   dx : Dt^sigma) -> eval(Dt^tau)| \\
    %   |eval(\x dx -> derive(t)) : eval(Dt^Gamma)
    %   -> eval(sigma) -> eval(Dt^sigma) -> eval(Dt^tau)|
    % \end{align*}
    % Curried functions have equivalent behavior, so both ones give a derivative
    % for |eval t|, once we apply them to inputs for context |Gamma , x : sigma|
    % and corresponding valid changes.

    More in detail, our thesis is that |evalInc(\x -> t)| is a derivative
    for |eval(\x -> t)|, that is
    \begin{multline}
      \label{eq:der-corr-th1}
      |forall (fromto Gamma rho1 drho rho2) . ^^^ fromto (sigma -> tau) (eval(\x -> t) rho1) (eval(derive(\x -> t)) drho) (eval(\x -> t) rho2)|
    \end{multline}
  %
    By simplifying, the thesis \cref{eq:der-corr-th1} becomes
    % We can simplify the hypothesis |fromto (Gamma, x : sigma)
    % rho1 drho rho2| using the definition of validity on
    % environments. This
    \begin{multline}
      \label{eq:der-corr-th2}
      |forall (fromto Gamma rho1 drho rho2) . ^^^ fromto (sigma -> tau) (^^^(\a1 -> eval(t) (rho1, x = a1))) (\a1 da -> eval(derive(t)) (drho, x = a1, dx = da)) ((\a2 -> eval(t) (rho2, x = a2)))|.
    \end{multline}
    %
    By definition of validity of function type, the thesis
    \cref{eq:der-corr-th2} becomes
    \begin{multline}
      \label{eq:der-corr-th3}
      |forall (fromto Gamma rho1 drho rho2). ^^ forall (fromto sigma a1 da a2). ^^^
      fromto tau (^^^eval t (rho1, x = a1))
      (eval(derive t) (drho, x = a1, dx = da))
      (eval t (rho2, x = a2))|.
    \end{multline}

    To prove the rewritten thesis \cref{eq:der-corr-th3}, take the inductive hypothesis on |t|: it says
    that |eval(derive t)| is a derivative for |eval t|, so |eval(derive t)| maps
    valid environment changes on |Gamma , x : sigma| to valid changes on |tau|.
    But by inversion of the validity judgment,
    all valid environment changes on |Gamma , x : sigma| can be written as
    %
    \[
      \validfromto{\Extend{x}{\sigma}}
      {\ExtendEnv*[\rho_1]{x}{a_1}}
      {\ExtendEnv*[\ExtendEnv[\D\rho]{x}{a_1}]{dx}{\D{a}}}
      {\ExtendEnv*[\rho_2]{x}{a_2}},\]
    %
    for valid changes |fromto Gamma rho1
    drho rho2| and |fromto sigma a1 da a2|.
    So, the inductive hypothesis is that
    \begin{multline}
      |forall (fromto Gamma rho1 drho rho2). ^^ forall (fromto sigma a1 da a2). ^^^
      fromto tau (^^^eval t (rho1, x = a1))
      (eval(derive t) (drho, x = a1, dx = da))
      (eval t (rho2, x = a2))|.
    \end{multline}
    But that is exactly our thesis \cref{eq:der-corr-th3}, so we're done!
  \item Case |Gamma /- c : tau|. In essence, since weakening
    preserves meaning, we can rewrite the thesis to match
    \cref{req:correct-derive-const}.

    In more detail, the thesis is that |deriveConst(c)| is a
    derivative for |c|, that is, if |fromto Gamma rho1 drho
    rho2| then |fromto tau (eval(c) rho1) (eval(derive(c)) drho)
    (eval(c) rho2)|. Since constants don't depend on the
    environment and weakening preserves meaning
    (\cref{lem:weaken-sound}), and by the definitions of
    |eval(param)| and |derive(param)| on constants, the thesis
    can be simplified to |fromto tau (eval(c) emptyRho)
    (eval(deriveConst(c)) emptyRho) (eval(c) emptyRho)|, which is
    delegated to plugins in \cref{req:correct-derive-const}.
  \end{itemize}
\end{proof}

\section{Discussion}
\subsection{The correctness statement}
We might have asked for the following
correctness property:

\begin{theorem}[Incorrect correctness statement]
If |Gamma /- t : tau| and |rho1 `oplus` drho = rho2| then
|(eval(t) rho1) `oplus` (eval(derive(t)) drho) = (eval(t) rho2)|.
\end{theorem}

However, this property is not quite right. We can only prove correctness
if we restrict the statement to input changes |drho| that are
\emph{valid}. Moreover, to prove this
statement by induction we need to strengthen its conclusion: we
require that the output change |eval(derive(t)) drho| is also
valid. To see why, consider term |(\x -> s) t|: Here the output of |t|
is an input of |s|. Similarly, in |derive((\x -> s) t)|, the
output of |derive(t)| becomes an input change for subterm
|derive(t)|, and |derive(s)| behaves correctly only if only if
|derive(t)| produces a valid change.

Typically, change types
contain values that invalid in some sense, but incremental
programs will \emph{preserve} validity. In particular, valid
changes between functions are in turn functions that take valid input
changes to valid output changes. This is why we
formalize validity as a logical relation.

\subsection{Invalid input changes}
\label{sec:invalid}
To see concretely why invalid changes, in general, can cause
derivatives to produce
incorrect results, consider again |grandTotal = \ xs ys -> sum
(merge xs ys)| from~\cref{sec:motiv-example}.
Suppose a bag change |dxs| removes an element
|20| from input bag |xs|, while |dys| makes no changes to |ys|:
in this case, the output should decrease, so |dz = dgrandTotal xs dxs
ys dys| should be |-20|. However, that is only correct if
|20| is actually an element of |xs|. Otherwise, |xs `oplus` dxs|
will make no change to |xs|, hence the correct output change |dz| would be |0|
instead of |-20|. Similar but trickier issues apply with function
changes; see also \cref{sec:very-invalid}.

\subsection{Alternative environment changes}
\label{sec:envs-without-base-inputs-intro}
Environment changes can also be defined differently. We will use
this alternative definition later (in
\cref{sec:defunc-env-changes}).

A change |drho| from |rho1| to |rho2| contains a copy of |rho1|.
Thanks to this copy, we can use an environment change as
environment for the result of differentiation, that is, we can
evaluate |derive t| with environment |drho|, and
\cref{def:inc-semantics} can define |evalInc(t)| as |\rho1 drho
-> eval(derive t) drho|.

But we could adapt definitions to omit the copy of |rho1| from
|drho|, by setting

\[\Delta\Extend*{x}{\tau} = \Extend[\Delta\Gamma]{\D
    x}{\Delta\tau}\]

\noindent and adapting other definitions. Evaluating |derive(t)|
still requires base inputs; we could then set |evalInc(t) = \rho1
drho -> eval(derive t) (rho1, drho)|, where |rho1, drho| simply
merges the two environments appropriately (we omit a formal
definition). This is the approach taken by
\citet{CaiEtAl2014ILC}. When proving \cref{thm:derive-correct},
using one or the other definition for environment changes makes
little difference; if we embed the base environment in
environment changes, we reduce noise because we need not define
environment meging formally.

Later (in \cref{sec:defunc-env-changes}) we will deal with
environment explicitly, and manipulate them in programs. Then we
will use this alternative definition for environment changes,
since it will be convenient to store base environments separately
from environment changes.

\subsection{Capture avoidance}
\label{sec:derive-binding-issues}
Differentiation generates new names, so a correct implementation
must prevent accidental capture. Till now we have ignored this problem.

\paragraph{Using de Bruijn indexes}
Our mechanization has no capture
issues because it uses de Bruijn indexes. Change context just
alternate variables for base inputs and input changes. A context
such as |Gamma = x : Int, y : Bool| is encoded as |Gamma = Int,
Bool|; its change context is |Dt^Gamma = Int, Dt^Int, Bool,
Dt^Bool|. This solution is correct and robust, and is the one we
rely on.

Alternatively, we can mechanize ILC using separate syntax for change terms |dt|
that use separate namespaces for base variables and change variables.

\begin{code}
  ds , dt   ::=  dc
            |    \ (x : sigma) (dx : Dt^sigma) -> dt
            |    ds t dt
            |    dx
\end{code}

In that case, change variables live in a separate namespace. Example context
|Gamma = Int, Bool| gives rise to a different sort of change context, |Dt^Gamma
= Dt^Int, Dt^Bool|. And a change term in context |Gamma| is evaluted with
separate environments for |Gamma| and |Dt^Gamma|.
This is appealing, because it allows defining differentiation and proving it
correct without using weakening and applying its proof of soundness.
We still need to use weakening to convert change terms to their equivalents in
the base language, but proving that conversion correct is more straightforward.

\paragraph{Using names}
Next, we discuss issues in implementing this transformation with
names rather than de Bruijn indexes. Using names rather than de
Bruijn indexes makes terms more readable; this is also why in
this thesis we use names in our on-paper formalization.

Unlike the rest of this chapter, we keep this discussion informal, also
because we have not mechanized any definitions using names (as it
may be possible using nominal logic), nor attempted formal proofs.
The rest of the thesis does
not depend on this material, so readers might want to skip to
next section.

Using names introduces the risk of capture, as it is common for
name-generating
transformations~\citep{Erdweg2014captureavoiding}. For instance,
differentiating term |t = \x -> f dx| gives |derive(t) = \x dx
-> df dx ddx|. Here, variable |dx| represents a base input and is
free in |t|, yet it is incorrectly captured in |derive(t)| by the
other variable |dx|, the one representing |x|'s change.
Differentiation gives instead a
correct result if we $\alpha$-rename |x| in |t| to any other
name (more on that in a moment).

A few workarounds and fixes are possible.
\begin{itemize}
\item As a workaround, we can forbid names starting with the letter |d| for
  variables in base terms, as we do in our examples; that's
  formally correct but pretty unsatisfactory and inelegant. With
  this approach, our term |t = \x -> f dx| is simply forbidden.
\item As a better workaround, instead of prefixing variable names
  with |d|, we can add change variables as a separate construct
  to the syntax of variables and forbid differentiation on terms
  that containing change variables. This is a variant of the earlier approach
  using separate change terms.
  While we used this approach
  in our prototype implementation in
  Scala~\citep{CaiEtAl2014ILC}, it makes our output language
  annoyingly non-standard. Converting to a standard language using names (not
  de Bruijn indexes) raises again capture issues.
  % A slight downside is that
  % this unnecessarily prevents attempting iterated
  % differentiation, as in |derive(derive(t))|.

  % which other
  % approaches to finite differencing rely on~\citep{Koch10IQE}.%
  % \footnote{We explain in }
  % \footnote{This restriction is
  %   still unnecessary and slightly unfortunate, since other
  %   approaches to finite differencing on database languages require
  %   iterated differentiation~\citep{Koch10IQE}.

  %   In fact,
  %   we never iterate differentiation, but t

  %   We discuss later~\cref{sec:finite-diff}.}
\item We can try to $\alpha$-rename \emph{existing} bound
  variables, as in the implementation of capture-avoiding
  substitution. As mentioned, in our case, we can rename bound
  variable |x| to |y| and get |t' = \y -> f dx|. Differentiation
  gives the correct result |derive(t') = \y dy -> df dx ddx|. In
  general we can define |derive(\x -> t) = \y dy -> derive(t[x :=
  y])| where neither |y| nor |dy| appears free in |t|; that is,
  we search for a fresh variable |y| (which, being fresh, does
  not appear anywhere else) such that also |dy| does not appear
  free in |t|.

  This solution is however subtle: it reuses ideas from
  capture-avoiding substitution, which is well-known to be
  subtle. We have not attempted to formally prove such a solution
  correct (or even test it) and have no plan to do so.
\item Finally and most easily we can $\alpha$-rename \emph{new}
  bound variables, the ones used to refer to changes, or rather,
  only pick them fresh. But if we pick, say, fresh variable |dx1|
  to refer to the change of variable |x|, we \emph{must} use
  |dx1| consistently for every occurrence of |x|, so that
  |derive(\x -> x)| is not |\dx1 -> dx2|. Hence, we extend
  |derive(param)| to also take a map from names to names as
  follows:
\begin{align*}
  |derive(\(x: sigma) -> t, m)| &= |\(x: sigma) (dx : Dt^sigma) -> derive(t, (m[x -> dx]))| \\
  |derive(s t, m)| &= |derive(s, m) t (derive(t, m))| \\
  |derive(x, m)| &= |m^(x)| \\
  |derive(c, m)| &= |deriveConst(c)|
\end{align*}
where |m^(x)| represents lookup of |x| in map |m|,
|dx| is now a fresh variable that does not appear in |t|,
and |m[x -> dx]| extend |m| with a new mapping from |x| to |dx|.

  But this approach, that is using a map from base variables to change
  variables, affects the interface of differentiation. In
  particular, it affects which variables are free in output terms, hence we must
  also update the definition of |Dt^Gamma| and derived typing rule
  \textsc{Derive}.
  With this approach, if term |s| is closed then |derive(s, emptyMap)| gives a result
  $\alpha$-equivalent to the old |derive(s)|, as long
  as |s| triggers no capture issues. But if instead |s| is open, invoking
  |derive(s, emptyMap)| is not meaningful: we must
  pass an initial map |m| containing mappings from |s|'s free variables to fresh
  variables for their changes. These change variables appear free in |derive(s,
  m)|, hence we must update typing rule \textsc{Derive}, and modify |Dt ^ Gamma|
  to use |m|.

  We define $\Delta_m \Gamma$ by adding |m| as a parameter to
  |Dt^Gamma|, and use it in a modified rule \textsc{Derive'}:
\begin{align*}
  \Delta_m\EmptyContext &= \EmptyContext \\
  \Delta_m\Extend*{x}{\tau} &= \Extend[\Extend[\Delta_m\Gamma]{x}{\tau}]{m(x)}{\Delta\tau}\text{.}
\end{align*}
  \begin{typing}
    \Rule[Derive']
    {|Gamma /- t : tau|}
    {\Delta_m \Gamma| /- derive(t, m) : Dt ^ tau|}
  \end{typing}
  We conjecture that \textsc{Derive'} holds and that |derive(t, m)| is correct,
  but we have attempted no formal proof.
\end{itemize}

\section{Plugin requirement summary}
For reference, we repeat here plugin requirements spread through the chapter.

\baseBasicChangeStructures*
\baseChangeTypes*
\constDifferentiation*
\deriveConstCorrect*

\section{Chapter summary}
In this chapter, we have formally defined changes for values and environments of
our language, and when changes are valid. Through these definitions, we have explained
that |derive(t)| is correct, that is, that it maps changes to the input
environment to changes to the output environment. All of this assumes, among
other things, that language plugins define valid changes for their base types
and derivatives for their primitives.

In next chapter we discuss operations we provide to construct and use
changes. These operations will be especially useful to provide derivatives of
primitives.
