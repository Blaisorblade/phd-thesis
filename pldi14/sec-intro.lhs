% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

% \section{Introduction}
\label{sec:intro}

Incremental computation (or incrementalization) has a long-standing history in
computer science~\citep{Ramalingam93}.
Often, a program needs to update the output of some nontrivial function $f$
when the input to the computation changes.
Programmers typically have to choose between a few undesirable options.
\begin{itemize}
\item They can call again function $f$ on the updated input and
  repeat the computation from scratch. This choice guarantees
  correct results and is easy to implement, but typically wastes
  computation time. Often, if the updated input is close to the
  original input, the same result can be computed much faster.
\item They can write by hand a new function $df$ that updates the
  output based on input changes, using various techniques.
  Depending on the complexity of $f$, their ability and effort,
  this choice can be much more efficient, but takes significant
  developer time. Moreover, this choice introduces significant
  potential for bugs, because writing $df$ is hard and because it
  must be updated when $f$ changes. In actual applications, this
  complicates code maintenance tasks
  significantly~\citep{Salvaneschi13reactive}.
\item They can write the function of interest using
  domain-specific languages that support incrementalization.
  Build scripts and associated domain-specific languages are one
  example. Database query languages are another one.\pg{Mention here limits?}
\item They can attempt using general-purpose techniques for
  incrementalizing programs, such as \emph{self-adjusting
    computation} and variants. Self-adjusting computation applies
  to arbitrary purely functional programs and has been extended
  to imperative programs; however, it only guarantees efficient
  incrementalization for base programs designed for efficient
  incrementalization.
\end{itemize}

\pg{Continue discussing dependencies minimization and the
  relation with parallelism. Build scripts might be a good
  example.}

Since no approach guarantees efficient incrementalization for
arbitrary programs, we propose to design domain-specific
functional languages whose programs can be incrementalized by
transformation. We will discuss later why we favor this approach.\pg{where?}

\section{A motivating example}
\label{sec:motiv-example}
In this section, we illustrate informally incrementalization on a
small example program, shown in Haskell notation. We give a more precise presentation in
\cref{sec:correct-derive} after recalling some background on
our object language in \cref{sec:intro-stlc}.

In the following program, |grand_total xs ys| sums numbers in
input collections |xs| and |ys|. We also compute an initial
output |output1| on initial inputs |xs1| and |ys1|:

\begin{code}
  grand_total xs ys = sum (merge xs ys)
  output1           = grand_total xs1 ys1
                    = sum {{1, 2, 3, 4}} = 10
\end{code}

We have called |grand_total| on initial inputs |xs1 = {{1, 2, 3}}| and |ys1 = {{4}}|
to obtain initial output |output1|. Here |{{...}}| denotes a multiset
or \emph{bag} containing the elements among braces. A bag is an
unordered collection (like a set) where elements are allowed to appear more
than once (unlike a set).

This example uses small inputs for simplicity, but in practice they
are typically much bigger; we use |n|
to denote the input size. In this case the asymptotic complexity of computing
|grand_total| is |Theta(n)|.

Consider computing updated output |output2| from updated inputs |xs2 = {{1, 1, 2, 3}}|
and |ys2 = {{4, 5}}|. We could recompute |output2| from scratch as
\begin{code}
  output2      = grand_total xs2 ys2
               = sum {{1, 1, 2, 3, 4, 5}} = 16
\end{code}
But if the size of the updated inputs is |Theta(n)|, recomputation also
takes time |Theta(n)|, and we would like to obtain our result asymptotically faster.

To compute the updated output |output2| faster, we assume the changes to the
inputs have a description of size |dn| that is asymptotically smaller than the
input size |n|, that is |dn = o(n)|. All approaches to incrementalization
require small input changes. Incremental computation will then process the input
changes, rather than just the new inputs.

In our approach to incrementalization we also describe changes to values as new
values. We call such description simply \emph{changes}. Each change |dx| has a
source |x1| and a destination |x2|. There is an operator |`oplus`| that computes
the destination of a change |x2| given its source |x1| and and the change
itself, so that in general |x2 = x1 `oplus` dx|. For now, a change |das| to a
bag |as1| simply contains all elements to be added to the base bag |as1| to
obtain the updated bag |as2| (we'll ignore removing elements for this section
and discuss it later). In our example, the change from |xs1| (that is |{{1, 2,
    3}}|) to |xs2| (that is |{{1, 1, 2, 3}}|) is |dxs = {{1}}|, while the change
from |ys1| (that is |{{4}}|) to |ys2| (that is |{{4, 5}}|) is |dys = {{5}}|. To
represent the output change |doutput| from |output1| to |output2| we need
integer changes. For now, we represent integer changes as integers, and define
|`oplus`| on integers as addition: |x1 `oplus` dx = x1 + dx|.

We propose to compute the output change |doutput| from |output1| to |output2| by
calling a new function |dgrand_total|, the \emph{derivative} of |grand_total| on
base inputs and their respective changes. We can then compute the updated output
|output2| as the old output |output1| updated by change |doutput|. Below we give
the derivative of |grand_total| and show our approach gives the correct result
in this example.

\begin{code}
  dgrand_total xs dxs ys dys = sum (merge dxs dys)
  doutput                    = dgrand_total xs1 dxs ys1 dys =
                             = sum {{1, 5}} = 6
  output2                    = output1 `oplus` doutput = output1 + doutput = 10 + 6 = 16
\end{code}

The goal is that a derivative is asymptotically faster than a
base program. Here, derivative |dgrand_total| simply
\emph{ignores} base inputs, so its time complexity depends only
on the size of changes |dn|. The complexity of |dgrand_total| is
in particular |Theta(dn) = o(n)|.

Moreover, we propose to generate derivatives by a program
transformation |derive(param)| on base terms |t|, assuming that
we already have derivatives for primitive functions they use.

We call this program transformation \emph{differentiation} (or,
sometimes, simply \emph{derivation}); we write |derive(t)| to
denote the result of this transformation on a term |t|.
Informally, |derive(t)| describes how |t| changes, that is,

\begin{slogan}
|derive(t)| evaluates to a change from |t|
evaluated on old inputs to |t| evaluated on new inputs.
\end{slogan}

In our
example, we can apply |derive(param)| to |grand_total|'s body to
produce |dgrand_total|'s body. After simplifying the result, we get
\[ |derive(sum (merge xs ys)) `cong` sum (merge dxs dys)|.\]
where `cong` denotes program equivalence. Correctness of |derive(param)| guarantees
that |sum (merge dxs dys)| evaluates to a change from
|sum (merge xs ys)| evaluated on old inputs |xs1, ys1| to
|sum (merge xs ys)| evaluated on new inputs |xs2, ys2|.

Here,
a derivative of |grand_total| is a function in the same language as
|grand_total|, that accepts changes from initial inputs |xs1| and |ys1| to
updated inputs |xs2| and |ys2| and evaluates to the change from the base result
|grand_total xs1 ys1| to the updated result |grand_total xs2 ys2|.

More in general, for a unary function |f|, a derivative |df|
takes an input |x| and a change |dx| for |x| and produces a
change from base output |f x| to updated output |f (x `oplus`
dx)|. Symbolically we write
\begin{code}
  f x `oplus` df x dx `cong` f (x `oplus` dx)
\end{code}

For functions |f| of multiple arguments, a derivative |df| takes
all base inputs of |f| together with changes to each of them, and
produces a change from the base output to the updated output. We
will make this more formal in next section.

In this section, we have sketched the meaning of differentiation
informally. However, we have neither actully defined it, nor
discussed what it does on higher-order terms. To answer these questions

% To make things concrete we show
% \begin{code}
  % xs1          = {{1}}
  % dxs          = {{1}}
  % xs2          = {{1, 1}}

  % ys1          = {{2, 3, 4}}
  % dys          = {{5}}
  % ys2          = {{2, 3, 4, 5}}

  % output1      = grand_total xs1 ys1
  %              = sum {{1, 2, 3, 4}} = 10
  % output2      = grand_total xs2 ys2
  %              = sum {{1, 1, 2, 3, 4, 5}} = 16
  % dgrand_total = \ xs dxs ys dys -> sum (merge dxs dys)
  % doutput      = dgrand_total xs1 dxs ys1 dys =
  %              = sum {{1, 5}} = 6
  % output2      = outpu1 + doutput
% \end{code}

% To clarify notation:
% \begin{itemize}
% \item |{{...}}| denotes a multiset or \emph{bag} containing the
%   elements among braces. A bag is an unordered collection (like a
%   set) where elements are allowed to appear more than once
%   (unlike a set).
% \item Function |grand_total| is given in Haskell-like notation;
%   it merges the two input bags, and sums all elements to compute
%   its result.
% \item Change |dxs| is a value describing the change from base input |xs1| to updated input |xs2|. For now changes to bags simply list elements to insert, so that |dxs = {{1}}| means ``insert element |1| from base input |xs1| to obtain updated input |xs2|''.
%   Similarly, |dys = {{5}}| means ``insert |5| into base input |ys1| to obtain updated input |ys2|''.
% \end{itemize}

% In this case, |dgrand_total| would compute the output change
% |doutput = dgrand_total xs1 dxs ys1 dys = 6|, which can then
% be used to update the original output |10| to yield the updated
% result |16|.

% In this example incremental computation doesn't seem to save much
% time, but that's only because base inputs are small. Usually
% inputs are instead much bigger than changes. The time complexity
% of recomputation, |grand_total xs2 ys2|, is linear in the sizes
% of |xs2| and |ys2|, while the time complexity of |dgrand_total
% xs1 dxs ys1 dys| only depends on the sizes of |dxs| and |dys|.

% A derivative is a function in the
% same language as |grand_total|, that accepts changes to all inputs  and producing changes, which
% are simple first-class values of this language.
%

\section{Our object language}
\label{sec:intro-stlc}
We will define differentiation as a recursive program transformation on terms.
To be able to define the transformation and state the invariant it satisfies, we
need to first recall the object language we develop the transformation in.

\ILC\ considers as object language a strongly-normalizing
simply-typed $\Gl$-calculus (STLC). To prove that
incrementalization preserves the final results of our
object-language programs, we need to specify a semantics for
STLC. To this end we use a denotational semantics. Since STLC is
strongly normalizing~\citep[Ch. 12]{Pierce02TAPL} we need not
handle partiality in our semantics, in particular we can eschew
using domain theory. The domains for our denotational semantics
are simply Agda types, and semantic values are Agda values---in
other words, we give a denotational semantics in terms of type
theory.\footnote{Alternatively, some would call such a semantics
  a definitional interpreter~\citep{Amin2017}.}
%
Using denotational semantics allows us to state the specification
of differentiation directly in the semantic domain, and take
advantage of Agda's support for equational reasoning for proving
equalities between Agda functions.

\input{pldi14/fig-lambda-calc}

We recall syntax, typing rules and denotational semantics of STLC in
\cref{fig:lambda-calc}; for a more proper introduction to STLC (but not to
denotational semantics) we refer the reader to \citet[Ch. 9]{Pierce02TAPL}.

\subsection{Language plugins}
Our STLC is parameterized by \emph{language plugins} (or just plugins).
A plugin defines:
\begin{itemize}
\item
  a set of base types $\iota$, base constants $c$ and their
  semantics $\EvalConst{c}$, in the usual sense;
\item a representation for changes for each base type, and a
  derivative for each primitive;
\item proofs of correctness for its components.
\end{itemize}

Once a plugin
specifies the primitives and their respective derivatives,
and
\ILC\ can glue together these simple derivatives in such a way
that derivatives for arbitrary STLC expressions
using these primitives can be computed.

Our |grand_total| example requires a plugin that provides a types for integers
and bags and primitives such that we can implement |sum| and
|merge|.\pg{Elaborate.}

% Our first implementation and our first correctness proof are
% explicitly modularized to be parametric in the plugins, to
% clarify precisely the interface that plugins must satisfy.

\section{Differentiation and its meaning}
\label{sec:correct-derive}

In this section, we introduce differentiation formally. We
claimed differentiation turns input changes into output changes.
We also formalize and prove this claim, and explain what it means
on higher-order programs.

To support incrementalization, we also motivate and introduce in
this section (a) a description of changes, and operations on
changes, parameterized by types; (b) a definition of which
changes are valid; (c) a compositional term-to-term
transformation called differentiation and written |derive(t)|
that produces incremental programs.

Before stating how these concepts are actually implemented, we
explain how they fit together. The definitions are collected
together in \cref{fig:differentiation}.

\begin{figure}
  \small
  \centering
  \FramedSignature{\Delta\Gt}
\begin{align*}
  |Dt ^ iota| &= \ldots\\
  |Dt ^ (sigma -> tau)| &= |Dt ^ sigma -> tau -> Dt ^ tau|
\end{align*}

  \FramedSignature{\Delta\Gamma}
\begin{align*}
  \Delta\EmptyContext &= \EmptyContext \\
  \Delta\Extend{x}{\tau} &= \Extend{\Extend[\Delta\Gamma]{x}{\tau}}{\D x : \Delta\tau} \\
\end{align*}
  \FramedSignature{|derive(t)|}
\begin{code}
  derive(\x -> t) = \x dx -> derive(t)
  derive(s t) = derive(s) t (derive(t))
  derive(x) = dx
  derive(c) = ...
\end{code}

  If |Gamma /- t : tau| then |Dt ^ Gamma /- derive(t) : Dt ^ tau|.

  \FramedSignature{|fromto tau v1 dv v2|\text{ with }|v1, v2 : eval(tau), dv : eval(Dt^tau)|}
\begin{align*}
  |fromto iota v1 dv v2| &= \ldots \\
  |fromto (sigma -> tau) f1 df f2| &=
  |forall a1 a2 : eval(sigma), da : eval(Dt ^ sigma) .| \\
  &\text{if }|fromto (sigma) a1 da a2| \text{ then }
    |fromto (tau) (f1 a1) (df a1 da) (f2 a2)|
\end{align*}


  \FramedSignature{|fromto Gamma rho1 drho rho2|}
\begin{typing}
  \Axiom
  {\validfromto{\EmptyContext}{\EmptyContext}{\EmptyContext}{\EmptyContext}}
  \Rule{|fromto Gamma rho1 drho rho2|\\
    |fromto tau a1 da a2|}{
  \validfromto{\Extend{x}{\tau}}
  {\ExtendEnv*[\rho_1]{x}{a_1}}
  {\ExtendEnv*[\ExtendEnv[\D\rho]{x}{a_1}]{dx}{\D{a}}}
  {\ExtendEnv*[\rho_2]{x}{a_2}}}
\end{typing}

  If |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |fromto tau (eval(t) rho1) (eval(derive(t)) drho) (eval(t) rho2)|.

  \caption{Defining differentiation.}
  \label{fig:differentiation}
\end{figure}

For each type |tau|, we define a change type |Dt^tau|. We refer
to values of change types as \emph{change values}. A change value
|dv : eval(Dt^tau)| describes the difference between two values
|v1, v2 : eval(tau)|. To describe changes to the inputs of a
term, we also introduce change contexts |Dt^Gamma| and
environment changes |drho : eval(Dt^Gamma)|; an environment
change from |rho1 : eval(Gamma)| to |rho2: eval(Gamma)| is simply
an environment containing a change for each environment entry.

Later we will define operator |`oplus`|, such that |v1
`oplus` dv = v2| whenever |dv| is a change between |v1| and |v2|.

Roughly, our goal is that evaluating |derive(t)| (where |t| is a
well-typed term) maps an environment change |drho| from |rho1| to
|rho2| into a result change |eval(derive(t)) drho|, going from
|eval(t) rho1| to |eval(t) rho2|. To this end, we first constrain
the static semantics of |derive(t)|, that is its typing, so that
|derive(t)| maps changes to |t|'s inputs to changes to |t|'s
output:

\begin{lemma}[Typing of |derive(param)|]
  \label{lem:derive-typing}
  If |Gamma /- t : tau| then |Dt ^ Gamma /- derive(t) : Dt ^ tau|.
\end{lemma}

Next, we constraint |derive(t)|'s dynamic semantics, that is the
result of evaluating it. we might hope for the following
correctness statement to hold:

\begin{theorem}[Incorrect correctness statement]
If |Gamma /- t : tau| and |rho1 `oplus` drho = rho2| then
|(eval(t) rho1) `oplus` (eval(derive(t)) drho) = (eval(t) rho2)|.
\end{theorem}

This statement is not quite right: we can only prove correctness
if we restrict the statement to input changes |drho| that are
\emph{valid}, in a sense we'll define. Moreover, to prove this
statement by induction we need to strengthen its conclusion: we
require that the output change |eval(derive(t)) drho| is also
valid. To see why, consider |(\x -> s) t|: Here the output of |t|
is an input of |s|. Similarly, in |derive((\x -> s) t)|, the
output of |derive(t)| become input changes for subterm
|derive(t)|, and |derive(s)| behaves correctly only if only if
|derive(t)| produces a valid change.

Formally, validity is a logical relation |fromto tau v1 dv v2|,
relating a change value |dv : eval(Dt^tau)|, a source value |v1 :
eval(tau)| and a target value |v2 : eval(tau)|. We read |fromto
tau v1 dv v2| as ``|dv| is valid change from |v1| to
|v2|''.

As mentioned, to discuss input changes we also extend these
definitions to environments, defining |Dt^Gamma| and |fromto
Gamma rho1 drho rho2|.
A valid environment change |drho|, valid from |rho1| to |rho2|,
extends environment |rho1| with valid changes for each entry.

Once we define these notions, we can fix |derive(param)|'s correctness statement.
Evaluating |derive(param)| on a well-typed term |t| maps a valid
environment change |drho| from |rho1| to |rho2| into a valid
result change |eval(derive(t)) drho|, going
from |eval(t) rho1| to |eval(t) rho2|. Formally we have:
\begin{theorem}[Correctness of |derive(param)|]
  \label{thm:correct-derive}
  If |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |fromto tau (eval(t) rho1) (eval(derive(t)) drho) (eval(t) rho2)|.
\end{theorem}

% We will later also show change types
% containing invalid changes.

% % As we will see, change types contain changes that are not valid,
% % yet |`oplus`| is typically defined also on invalid changes.

% To fix this statement, we need to define
% which changes are \emph{valid}.
% Validity restricts
% As we'll see, correctness of
% differentiation requires changes to satisfy some invariants, but
% change types contain changes that violate them.
%
% which are not encoded by change types
% and are not checked by
% |`oplus`|; to formalize these invariants, so that incremental
% programs might rely on such invariants, we will introduce the
% notion of \emph{validity}.
% The above correctness statement does not require
% input changes to be valid, so it does not hold. Moreover, it does
% not claim that the output of differentiation gives a valid
% change, so it is too weak to prove: if |s| is a subterm of |t|,
% using this statement we do not know that |eval(derive(s)) drho|
% evaluates to a valid change.
%
Typically, change types
contain values that invalid in some sense, but incremental
programs will \emph{preserve} validity. In particular, valid
changes between functions are in turn functions that take valid input
changes to valid output changes. Hence, we
formalize validity as a logical relation.

A first-class function can close over free variables that can
change, hence functions values can change themselves; hence, we
introduce \emph{function changes} to describe these changes.
For instance, term |t = \x. x + y| is a function that closes over
|y|, so if |y| goes from |v1 = 5| to |v2 = 6|, |f1 = eval(t)
(emptyRho, y = v1)| is different from |f2 = eval(t) (emptyRho, y
= v2)|.
In general,
a valid function change from |f1| to |f2| (where |f1, f2
: eval(sigma -> tau)|) is in turn a function |df| that takes an
input |a1| and a change |da|, valid from |a1| to |a2|, to a valid
change from |f1 a1| to |f2 a2|. Function changes do not take
updated input |a2| as explicit argument; the value |a2| is implied by
|a1| and |da|, since it can be computed as |a1 `oplus` da|. Formally we define:
\begin{align*}
  |Dt ^ iota| &= \ldots\\
  |Dt ^ (sigma -> tau)| &= |Dt ^ sigma -> tau -> Dt ^ tau|\\
  |fromto (sigma -> tau) f1 df f2| &=
  |forall a1 a2 : eval(sigma), da : eval(Dt ^ sigma) .| \\
  &\text{if }|fromto (sigma) a1 da a2| \text{ then }
    |fromto (tau) (f1 a1) (df a1 da) (f2 a2)|
\end{align*}

As mentioned, to discuss input changes we also extend these
definitions to environments, defining |Dt^Gamma| and |fromto
Gamma rho1 drho rho2|.
A valid environment change |drho|, valid from |rho1| to |rho2|, extends environment |rho1| with valid changes for each entry.
\begin{align*}
  \Delta\EmptyContext &= \EmptyContext \\
  \Delta\Extend{x}{\tau} &= \Extend{\Extend[\Delta\Gamma]{x}{\tau}}{\D x : \Delta\tau} \\
\end{align*}
%
\begin{typing}
  \Axiom
  {\validfromto{\EmptyContext}{\EmptyContext}{\EmptyContext}{\EmptyContext}}
  \Rule{|fromto Gamma rho1 drho rho2|\\
    |fromto tau a1 da a2|}{
  \validfromto{\Extend{x}{\tau}}
  {\ExtendEnv*[\rho_1]{x}{a_1}}
  {\ExtendEnv*[\ExtendEnv[\D\rho]{x}{a_1}]{dx}{\D{a}}}
  {\ExtendEnv*[\rho_2]{x}{a_2}}}
\end{typing}

We write differentiation as |derive(t)|. We first give its
definition and typing.
The transformation is defined by:
\begin{code}
  derive(\x -> t) = \x dx -> derive(t)
  derive(s t) = derive(s) t (derive(t))
  derive(x) = dx
\end{code}
  % derive(^^let x = t1 in t2) =
  %   let  x = t1
  %        dx = derive(t1)
  %   in   derive(t2)


\begin{proof}[Proof of \cref{lem:derive-typing}]
  The thesis can be proven by induction on the typing derivation
  |Gamma /- t : tau|.
\end{proof}

To illustrate correctness statement \cref{thm:correct-derive}, it
is helpful to look first at its proof. Readers familiar with
logical relations proofs should be able to reproduce this proof
on their own, as it is rather standard, once one uses the given
definitions. Nevertheless, we spell it out, and use it to
motivate how |derive(param)| is defined.

\pg{Motivate inside the proof the definitions given for the various cases of derive.}
\begin{proof}[Proof of \cref{thm:correct-derive}]
  By induction on typing derivation |Gamma /- t : tau|.
  \begin{itemize}
  \item Case |Gamma /- x : tau|.
    \pg{State the thesis and motivate the pick for |derive(x)|.}
    The thesis follows |fromto tau
    (eval(x) rho1) (eval(dx) drho) (eval(x) rho2)| because the
    environment entry for |dx| is a valid change for the
    environment entry for |x|.
  \item Case |Gamma /- s t : tau|.
    By inversion of typing, there is some type |sigma| such that |Gamma /- s : sigma -> tau| and
    |Gamma /- t : sigma|.

    In essence, to prove the thesis, you can show by induction on
    |s|, |eval(derive(s)) drho| is a validity-preserving function
    change |df|, and use induction on |t| to produce a valid
    input to |df|. The thesis follows by validity preservation,
    and calculations showing the change has the right source and destination.

    In detail, our thesis is
    \[|fromto tau (eval(s t) rho1) (eval(derive(s t)) drho) (eval(s t) rho2)|,\]
    %
    where |eval(s t) rho = (eval(s) rho) (eval(t) rho)| (for any |rho : eval(Gamma)|)and
    \begin{equational}
      \begin{code}
   eval(derive(s t)) drho
=  eval(derive(s) t (derive(t))) drho
=  (eval(derive(s)) drho) (eval(t) drho) (eval(derive(t)) drho)
=  (eval(derive(s)) drho) (eval(t) rho1) (eval(derive(t)) drho)
      \end{code}%
    \end{equational}%
    The last step relies on |eval(t) drho = eval(t) rho1|.
    That follows by soundness of weakening:
    |drho : eval(Dt^Gamma)| extends |rho1 : eval(Gamma)|, and |t|
    can be typed in context |Gamma|.

    Our thesis becomes
    \[|fromto tau ((eval(s) rho1) (eval(t) rho1)) ((eval(derive(s)) drho) (eval(t) rho1) (eval(derive(t)) drho)) ((eval(s) rho2) (eval(t) rho2))|.\]

    By the inductive
    hypothesis on |s| and |t| we have
    \begin{gather*}
      |fromto (sigma -> tau) (eval(s) rho1) (eval(derive(s)) drho) (eval(s) rho2)| \\
      |fromto sigma (eval(t) rho1) (eval(derive(t)) drho) (eval(t) rho2)|.
    \end{gather*}
    Since |s| has function type, its validity means:
\begin{align*}
  |fromto (sigma -> tau) (eval(s) rho1) (eval(derive(s)) drho) (eval(s) rho2)| &=
  |forall a1 a2 : eval(sigma), da : eval(Dt ^ sigma) .|
  \text{ if }|fromto (sigma) a1 da a2| \text{ then }\\
    &|fromto (tau) ((eval(s) rho1) a1) ((eval(derive(s)) drho) a1 da) ((eval(s) rho2) a2)|
\end{align*}
Instantiating in this statement |fromto (sigma) a1 da a2| by |fromto sigma (eval(t)
rho1) (eval(derive(t)) drho) (eval(t) rho2)| gives the thesis.

  \item Case |Gamma /- \x -> t : sigma -> tau|. By inversion of typing,
    |Gamma , x : sigma /- t : tau|.
    We need to deduce the thesis
    \[|fromto (sigma -> tau) ((\a1 -> eval(t) (rho1, x = a1))) (\a1 da -> eval(derive(t)) (drho, x = a1, dx = da)) ((\a2 -> eval(t) (rho2, x = a2)))|.\]
    That is, for any |a1, a2, da| such that |fromto sigma a1 da a2|, we must have
    \[|fromto tau (eval(t) (rho1, x = a1)) (eval(derive(t))
      (drho, x = a1, dx = da)) (eval(t) (rho2, x = a2))|.\]

    To do so, take the inductive hypothesis on |t|. Since appropriate environment for |t| must match typing context |Gamma , x : sigma|, the hypothesis can be written as requiring that whenever
    $
      \validfromto{\Extend{x}{\sigma}}
  {\ExtendEnv*[\rho_1]{x}{a_1}}
  {\ExtendEnv*[\ExtendEnv[\D\rho]{x}{a_1}]{dx}{\D{a}}}
  {\ExtendEnv*[\rho_2]{x}{a_2}}$, that is |fromto Gamma rho1 drho rho2| and |fromto sigma a1 da a2|,
    we have
    \[|fromto tau (eval(t) (rho1, x = a1)) (eval(derive(t))
      (drho, x = a1, dx = da)) (eval(t) (rho2, x = a2))|.\]

    If we pick the same contexts and context change |fromto Gamma
    rho1 drho rho2|, the inductive hypothesis reduces to the
    thesis.
  \end{itemize}
\end{proof}

Next, we will introduce formally operator |`oplus`| and relate it
to validity. In particular, we will prove that |fromto tau v1 dv
v2| implies |v1 `oplus` dv = v2|, and explain why the converse is not true.


To understand why invalid changes cause derivatives to produce
incorrect results, consider again |grand_total = \ xs ys -> sum
(merge xs ys)|. Suppose a bag change |dxs| removes an element
|20| from input bag |xs|, while |dys| makes no changes to |ys|:
in this case, the output should decrease, so |dgrand_total xs dxs
ys dys| should return |-20|. However, that is only correct if
|20| is actually an element of |xs|. Otherwise, |xs `oplus` dxs|
will make no change to |xs|. Similar issues apply with function
changes.\pg{elaborate}

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
% to output |u2 `in` eval(tau1)|, and soon.

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


\subsection{Differentiation on our example}
\pg{This example is still a bit too complex as written; I'm skipping too many steps.}

To help fix ideas for later discussion, let us show
how the derivative of |grand_total|
looks like.

\begin{code}
grand_total  = \ xs ys -> sum (merge xs ys)
output       = grand_total {{1}} {{2, 3, 4}} = 11
\end{code}
We define derivation as a compositional program transformation,
so we first compute |derive(merge xs ys)|. To compute its change
we simply call the derivative of |merge|, that is |dmerge|, and
apply it to the base inputs and their changes: hence we write
\[|derive(merge xs ys) = dmerge xs dxs ys dys|.\]
As we'll
better see later, we can define function |dmerge| as
\[|dmerge = \xs dxs ys dys -> merge dxs dys|,\]
%
so |derive(merge xs ys)| can be simplified by $\beta$-reduction
to |merge dxs dys|:
\begin{code}
          derive(merge xs ys)
=         dmerge xs dxs ys dys
`betaeq`  (\xs dxs ys dys -> merge dxs dys) xs dxs ys dys
`betaeq`  merge dxs dys
\end{code}

Let's next derive |sum (merge xs ys)|. First, like above, the
derivative of |sum zs| would be |dsum zs dzs|, which depends on
base input |zs| and its change |dzs|. As we'll see, |dsum zs dzs|
can simply call |sum| on |dzs|, so |dsum zs dzs = sum dzs|. To
derive |sum (merge xs ys)|, we must call the derivative of |sum|,
that is |dsum|, on its base argument and its change, so on |merge
xs ys| and |derive(merge xs ys)|. We can later simplify again by
$\beta$-reduction and obtain
\begin{code}
          derive(sum (merge xs ys))
=         dsum (merge xs ys) (derive(merge xs ys))
`betaeq`  sum (derive(merge xs ys))
=         sum (dmerge xs dxs ys dys)
`betaeq`  sum (merge dxs dys)
\end{code}

Here we see the output of differentiation is defined in a bigger
typing context: while |merge xs ys| only depends on base inputs
|xs| and |ys|, |derive(merge xs ys)| also depends on their
changes. This property extends beyond the examples we just saw:
if a term |t| is defined in context |Gamma|, then the output of
derivation |derive(t)| is defined in context |Gamma, Dt ^ Gamma|,
where |Dt ^ Gamma| is a context that binds a change |dx| for each
base input |x| bound in the context |Gamma|.

Next we must transform |derive(\ xs ys -> sum (merge xs ys))|. Since |derive(sum (merge xs ys))| is defined (ignoring later optimizations) in a context binding |xs, dxs, ys, dys|, deriving |\ xs ys -> sum (merge xs ys)| must bind all those variables.

\begin{code}
          derive(\ xs ys -> sum (merge xs ys))
=         \xs dxs ys dys -> derive(sum (merge xs ys))
`betaeq`  \xs dxs ys dys -> sum (merge dxs dys)
\end{code}

Next we need to transform the binding of |grand_total2| to its body |b = \ xs ys -> sum (merge xs ys)|. We copy this binding and add a new additional binding from |dgrand_total2| to the derivative of |b|.

\begin{code}
grand_total   = \ xs      ys      ->  sum  (merge  xs   ys)
dgrand_total  = \ xs dxs  ys dys  ->  sum  (merge  dxs  dys)
\end{code}

Finally, we need to transform the binding of |output| and its body. By iterating similar steps,
in the end we get:\pg{fill missing steps}
\begin{code}
grand_total   = \ xs      ys      ->  sum  (merge  xs   ys)
dgrand_total  = \ xs dxs  ys dys  ->  sum  (merge  dxs  dys)
output         = grand_total   {{1, 2, 3}}              {{4}}
doutput        = dgrand_total  {{1, 2, 3}} {{1}} {{4}} {{5}}
\end{code}


\paragraph{Self-maintainability}
Differentiation does not always produce efficient derivatives
without further program transformations; in particular,
derivatives might need to recompute results produced by the base
program. In the above example, if we don't inline derivatives and
use $\beta$-reduction to simplify programs, |derive(sum (merge xs
ys))| is just |dsum (merge xs ys) (derive(merge xs ys))|. A
direct execution of this program will compute |merge xs ys|,
taking time linear in the base inputs. \pg{Point out this is
  self-maintainable!}

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

\subsection{The meta-language of our proofs}
In this subsection we describe the meta-language used in our
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

\paragraph{Type theory versus set theory for our purposes}
The differences
between set theory and type theory, and the two presentations of
our formalization, are mostly cosmetic for our purposes:
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

We postulate not only functional extensionality, but also a few
standard axioms on the implementation of bags, to avoid proving
correct an implementation of bags, or needing to account for
different values representing the same bag (such different values
typically arise when implementing bags as search tree).

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
