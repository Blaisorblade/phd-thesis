% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Changes and differentiation, formally}
\label{ch:derive-formally}
\input{pldi14/fig-differentiation}

To support incrementalization, in this chapter we introduce
differentiation and state and prove its correctness, making our
previous discussion precise. We discuss consequences of
correctness in \cref{ch:change-theory}.

% We also elaborate on the effect of
% differentiation on higher-order programs.
\section{Changes and validity}
\label{sec:changes-formally}
In this section we introduce formally (a) a description of
changes and operations on changes; (b) a definition of which
changes are valid. We have already introduced informally in
\cref{ch:static-diff-intro} the different notions and how they
fit together. We next define the same notions formally, and
deduce their key properties. We collect the complete definitions
and crucial facts in \cref{fig:differentiation}. Language plugins
extend these definitions for base types and constants they
provide.

We define valid changes in two steps: we (a) define a type
|Dt^tau| of changes, that we call \emph{change type}, and (b)
define a relation that picks valid changes out of all elements of
change types.

\begin{definition}[Change types]
  The change type |Dt^tau| of a type |tau| is defined in
  \cref{fig:change-types}.
\end{definition}
We refer to values of change types as \emph{change values}.

Then, we define \emph{validity} as a family of ternary \emph{logical relations},
indexed by types and relating changes with their sources and
destinations.
In a typical logical relation, \emph{functions} must map related input to
related outputs. Here, in a twist, it's \emph{function changes} that must map
related inputs to related outputs.
\begin{definition}[Validity]
We say that |dv| is valid change from |v1| to |v2| (at type |tau|), and write
|fromto tau v1 dv v2|, if |dv : eval(Dt^tau)|, |v1, v2 :
eval(tau)| and |dv| is a ``valid'' description of the difference
from |v1| to |v2|, as we define in \cref{fig:validity}.
\end{definition}

Both definitions place requirements on language plugins:
\begin{restatable}[Base change types]{requirement}{baseChangeTypes}
  \label{req:base-change-types}
  For each base type |iota|, the plugin defines a change type
  |Dt^iota|.
\end{restatable}
\begin{restatable}[Validity on base types]{requirement}{baseValidity}
  \label{req:base-validity}
  For each base type |iota|, the plugin defines validity.
\end{restatable}
In \cref{ex:valid-bag-int,ex:invalid-nat} we exemplified
informally change types and validity on naturals, integers and
bags.\pg{revise if we add more examples.}

Next, we explain the definitions of change types and validity for
function type |sigma -> tau|.
%
Take function values |f1, f2 : eval(sigma -> tau)|. As sketched,
valid function changes map valid input changes to valid output
changes. A bit more precisely, |df| is a valid function change
from |f1| to |f2| if, for all |a1, a2 : eval(sigma)| and for all
valid changes |da : eval(Dt^sigma)| from |a1| to |a2|, |df a1 da|
is a valid change from |f1 a1| to |f2 a2|. Formally, we define
change types and validity for function types as:
\begin{align*}
  |Dt^(sigma -> tau)| &= |sigma -> Dt ^ sigma -> Dt ^ tau|\\
  |fromto (sigma -> tau) f1 df f2| &=
  |forall a1 a2 : eval(sigma), da : eval(Dt ^ sigma) .| \\
  &\text{if }|fromto (sigma) a1 da a2| \text{ then }
    |fromto (tau) (f1 a1) (df a1 da) (f2 a2)|
\end{align*}

To describe changes to the inputs of a term, we now also
introduce change contexts |Dt^Gamma| environment changes |drho :
eval(Dt^Gamma)|, and validity for environment changes |fromto
Gamma rho1 drho rho2|.

A valid environment change from |rho1 : eval(Gamma)| to |rho2:
eval(Gamma)| is an environment |drho : eval(Dt^Gamma)| that
extends environment |rho1| with valid changes for each entry. We
first define the shape of change environments through
\emph{change contexts}:

\begin{definition}[Change contexts]
  For each context |Gamma| we define change context |Dt^Gamma| as
  follows:
\begin{align*}
  \Delta\EmptyContext &= \EmptyContext \\
  \Delta\Extend*{x}{\tau} &= \Extend[\Extend[\Delta\Gamma]{x}{\tau}]{\D x}{\Delta\tau}\text{.}
\end{align*}
\end{definition}

Then, we describe validity of change
environments via a judgment.
\begin{definition}[Valid environment changes]
We define judgment |fromto Gamma rho1 drho rho2|, pronounced
``|drho| is a valid environment change between |rho1| and
|rho2|'', where |rho1, rho2 : eval(Gamma), drho :
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

\section{Correctness of differentiation}
\label{sec:correct-derive}
In this section we state and prove correctness of
differentiation, a term-to-term transformation written
|derive(t)| that produces incremental programs. We recall that
all our results apply only to well-typed terms (since we
formalize no other ones).

We previously sketched |derive(param)|'s through
\cref{slogan:derive}, which we repeat for reference:
%
\sloganDerive*

A bit more formally, the input of a term |Gamma /- t : tau| is an
environment for |Gamma|. So evaluating |derive(t)| must map an
environment change |drho| from |rho1| to |rho2| into a valid
result change |eval(derive(t)) drho|, going from |eval(t) rho1|
to |eval(t) rho2|.\footnote{If |tau| is a function type, |df =
  eval(derive(t)) drho| accepts further inputs; since |df| must
  be a valid function change, it will also map them to valid
  outputs as required by our slogan.}
That is, |derive(t)| must be a \emph{correct
  change} for |t| as defined next:
\begin{definition}[Correct change]
  We say a term |dt| is a correct change for term |t|, and write
  |correct dt t|, if there exists a context |Gamma| and a type
  |tau| such that |Gamma /- t : tau|, |Dt ^ Gamma /- dt :
  Dt^tau|, and |eval(dt) drho| is a valid change from |eval(t)
  rho1| to |eval(t) rho2| whenever |fromto Gamma rho1 drho rho2|.
\end{definition}
In other words, |eval(dt)| must be a function that takes changes
|drho| from old to new inputs of |t|, and maps them to changes
from old to new outputs of |t|.

% Next, we constrain |derive(t)|'s dynamic semantics, that is the
% result of evaluating it.
%
% Recall that we'll define operator |`oplus`|, such that |v1
% `oplus` dv = v2| holds whenever |dv| is a valid change between
% |v1| and |v2|.

At this point, our slogan becomes |derive(param)|'s correctness
statement:
  \deriveCorrect

That theorem only makes sense if |derive(param)| has the right
static semantics:

\begin{restatable}[Typing of |derive(param)|]{lemma}{deriveTyping}
  \label{lem:derive-typing}
  Rule
  \begin{typing}
    \Rule[Derive]
    {|Gamma /- t : tau|}
    {|Dt ^ Gamma /- derive(t) : Dt ^ tau|}
  \end{typing}
  is a derived typing rule.
\end{restatable}

After we'll define |`oplus`|, in next chapter, we'll be able to relate |`oplus`|
to validity, by proving \cref{thm:valid-oplus}, which we state in advance here:
\begin{restatable*}[|`oplus`| agrees with validity]{lemma}{validOplus}
  \label{thm:valid-oplus}
  If |fromto tau v1 dv v2| then |v1 `oplus` dv = v2|.
\end{restatable*}

Hence, updating base result |eval(t) rho1| by change
|eval(derive(t)) drho| via |`oplus`| gives the updated result
|eval(t) rho2|.
\begin{restatable*}[|derive(param)| is correct, corollary]{corollary}{deriveCorrectOplus}
  \label{thm:derive-correct-oplus}
  If |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |eval(t) rho1 `oplus` eval(derive(t)) drho = eval(t) rho2|.
\end{restatable*}
We anticipate the proof of this corollary:
\begin{proof}
  First, differentiation is correct (\cref{thm:derive-correct}), so under the hypotheses
  \[|fromto tau (eval(t) rho1) (eval(derive(t)) drho) (eval(t) rho2)|;\]
  that judgement implies the thesis \[|eval(t) rho1 `oplus` eval(derive(t)) drho = eval(t) rho2|\]
  because |`oplus`| agrees with validty (\cref{thm:valid-oplus}).
\end{proof}

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

\subsection{Plugin requirements}
Differentiation is extended by plugins on constants, so plugins
must prove their extensions correct.

\begin{restatable}[Typing of |deriveConst(param)|]{requirement}{constDifferentiation}
  \label{req:const-differentiation}
  For all |c| such that $\ConstTyping{c}{\tau}$, the plugin defines
  |deriveConst(c)| satisfying |/- deriveConst(c) :
  Dt^tau| .
\end{restatable}

\begin{restatable}[Correctness of |deriveConst(param)|]{requirement}{deriveConstCorrect}
  \label{req:correct-derive-const}
  For all |c| such that $\ConstTyping{c}{\tau}$, |deriveConst(c)|
  is a correct change for |c|, that is, |fromto tau (evalConst c)
  (eval(deriveConst(c)) emptyRho) (evalConst c)|.
\end{restatable}

\subsection{Proofs}
We next recall |derive(param)|'s definition and prove it satisfies
its correctness statement \cref{thm:derive-correct}.
%After stating on |derive(param)|, we define |derive(param)| and prove the requirements hold.
\deriveDef*

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
abstraction theorem or relational parametricity (as given by \citet[Sec.
6]{Wadler1989theorems} or by \citet[Sec. 3.3, Theorem
3]{Bernardy2011realizability}) and the proof of the fundamental theorem of
logical relations by \citet{Statman1985logical}.

Nevertheless, we spell this proof out, and use it to motivate how
|derive(param)| is defined, more formally than we did in
\cref{sec:informal-derive}. For each case, we first give a short proof sketch,
and then redo the proof in more detail to make the proof easier to follow.

\deriveCorrect*
\begin{proof}
  By induction on typing derivation |Gamma /- t : tau|.
  \begin{itemize}
  \item Case |Gamma /- x : tau|. The thesis is that |derive(x)|
    is a correct change for |x|, that is |fromto tau (eval(x)
    rho1) (eval(derive(x)) drho) (eval(x) rho2)|. We claim the
    correct change for |x| is |dx|, hence define |derive(x) =
    dx|. Indeed, |drho| is a valid environment change
    from |rho1| to |rho2|, so |eval(dx) drho| is a valid change
    from |eval(x) rho1| to |eval(x) rho2|, as required by our
    thesis.
  \item Case |Gamma /- s t : tau|.
    %
    The thesis is that |derive(s t)| is a correct change for |s t|, that is
    |fromto tau (eval(s t) rho1) (eval(derive(s t)) drho) (eval(s t) rho2)|.
    %
    By inversion of typing, there is some type |sigma| such that
    |Gamma /- s : sigma -> tau| and |Gamma /- t : sigma|.

    To prove the thesis, in short, you can apply the inductive
    hypothesis to |t| and |s| on the same |rho1, drho, rho2|,
    obtaining respectively that |derive t| and |derive s|
    are correct changes for |s| and |t|. In particular, |derive s|
    evaluates to a validity-preserving function change.
    Term |derive (s t)|, that is |(derive s) t (derive t)|, applies
    validity-preserving function |derive s| to |t| and valid
    input change |derive t|, and this produces a correct change for
    |s t| as required.

    In detail, our thesis is
    \[|fromto tau (eval(s t) rho1) (eval(derive(s t)) drho) (eval(s t) rho2)|,\]
    %
    where |eval(s t) rho = (eval(s) rho) (eval(t) rho)| (for any |rho : eval(Gamma)|) and
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
    \[|fromto tau ((eval(s) rho1) (eval(t) rho1)) ((eval(derive(s)) drho) (eval(t) rho1) (eval(derive(t)) drho)) ((eval(s) rho2) (eval(t) rho2))|.\]

    By the inductive
    hypothesis on |s| and |t| we have
    \begin{gather*}
      |fromto (sigma -> tau) (eval(s) rho1) (eval(derive(s)) drho) (eval(s) rho2)| \\
      |fromto sigma (eval(t) rho1) (eval(derive(t)) drho) (eval(t) rho2)|.
    \end{gather*}
    Since |s| has function type, its validity means:
\begin{align*}
  |fromto (sigma -> tau) (^&^ eval(s) rho1) (eval(derive(s)) drho) (eval(s) rho2)|
  =\\
    &|forall a1 a2 : eval(sigma), da : eval(Dt ^ sigma)|\\
  &\text{ if }|fromto (sigma) a1 da a2| \\
  & \text{ then }
    |fromto (tau) ((eval(s) rho1) a1) ((eval(derive(s)) drho) a1 da) ((eval(s) rho2) a2)|
\end{align*}
Instantiating in this statement the hypothesis |fromto (sigma) a1 da a2| by |fromto sigma (eval(t)
rho1) (eval(derive(t)) drho) (eval(t) rho2)| (and |a1, da, a2| as needed) gives the thesis.

  \item Case |Gamma /- \x -> t : sigma -> tau|. By inversion of typing,
    |Gamma , x : sigma /- t : tau|.

    In short, our thesis is that |derive(\x -> t)| is a correct
    change for |\x -> t|. By induction on |t| we know that
    |derive(t)| is a correct change for |t|.
    %
    We show that our thesis, that is correctness of |derive(\x ->
    t)|, is equivalent to correctness of |derive(t)|, because we
    pick |derive(\x -> t) = \x dx -> derive(t)|. By
    typing of |derive(param)| you can show that |Dt^Gamma, x :
    sigma, dx : Dt^sigma /- derive(t): Dt^tau|. Now, |eval(\x dx
    -> derive(t))| is just a curried version of
    |eval(derive(t))|; to wit, observe their meta-level types:
    \begin{align*}
    |eval(derive(t)) : eval(Dt ^ Gamma , x : sigma,
      dx : Dt^sigma) -> eval(Dt^tau)| \\
      |eval(\x dx -> derive(t)) : eval(Dt^Gamma)
      -> eval(sigma) -> eval(Dt^sigma) -> eval(Dt^tau)|
    \end{align*}
    Curried functions have equivalent behavior, so both ones give
    a correct change for |t|, going from |eval(t) rho1| to |eval(t)
    rho2|, once we apply them to inputs for context
    |Gamma , x : sigma| and corresponding valid changes.

    More in detail, we need to deduce the thesis that |derive(\x
    -> t)| is a correct change for |\x -> t|.
    %
    By the definition of correctness, the thesis is that for all
    |drho, rho1, rho2| such that |fromto (Gamma, x : sigma) rho1
    drho rho2| we have
    \[|fromto (sigma -> tau) (eval(\x -> t) rho1) (eval(derive(\x -> t)) drho) (eval(\x -> t) rho2)|\]
%
    Simplifying, we get
    % We can simplify the hypothesis |fromto (Gamma, x : sigma)
    % rho1 drho rho2| using the definition of validity on
    % environments. This
    \begin{multline*}
      |fromto (sigma -> tau) (^^^(\a1 -> eval(t) (rho1, x = a1))) (\a1 da -> eval(derive(t)) (drho, x = a1, dx = da)) ((\a2 -> eval(t) (rho2, x = a2)))|.
    \end{multline*}
    %
    By definition of validity of function type, the thesis means
    that for any |a1, a2, da| such that |fromto sigma a1 da a2|,
    we must have
    \[|fromto tau (eval(t) (rho1, x = a1)) (eval(derive(t))
      (drho, x = a1, dx = da)) (eval(t) (rho2, x = a2))|.\]

    To prove the rewritten thesis, take the inductive hypothesis on |t|. Since
    appropriate environment for |t| must match typing context
    |Gamma , x : sigma|, we know by the inductive hypothesis that
    if
    %
    \[
      \validfromto{\Extend{x}{\sigma}}
      {\ExtendEnv*[\rho_1]{x}{a_1}}
      {\ExtendEnv*[\ExtendEnv[\D\rho]{x}{a_1}]{dx}{\D{a}}}
      {\ExtendEnv*[\rho_2]{x}{a_2}},\]
    %
    that is |fromto Gamma rho1
    drho rho2| and |fromto sigma a1 da a2|, then we have
    \[|fromto tau (eval(t) (rho1, x = a1)) (eval(derive(t))
      (drho, x = a1, dx = da)) (eval(t) (rho2, x = a2))|.\]

    If we pick the same contexts and context change |fromto Gamma
    rho1 drho rho2|, the inductive hypothesis reduces to the
    thesis.
  \item Case |Gamma /- c : tau|. In essence, since weakening
    preserves meaning, we can rewrite the thesis to match
    \cref{req:correct-derive-const}.

    In more detail, the thesis is that |deriveConst(c)| is a
    correct change for |c|, that is, if |fromto Gamma rho1 drho
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
\paragraph{The correctness statement}
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

\paragraph{Invalid input changes}
To see concretely why invalid changes, in general, can cause
derivatives to produce
incorrect results, consider again |grand_total = \ xs ys -> sum
(merge xs ys)|. Suppose a bag change |dxs| removes an element
|20| from input bag |xs|, while |dys| makes no changes to |ys|:
in this case, the output should decrease, so |dgrand_total xs dxs
ys dys| should return |-20|. However, that is only correct if
|20| is actually an element of |xs|. Otherwise, |xs `oplus` dxs|
will make no change to |xs|. Similar issues apply with function
changes.\pg{elaborate}

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

\paragraph{Using de Brujin indexes}
Our mechanization has no capture
issues because it uses deBrujin indexes. Change context just
alternate variables for base inputs and input changes. A context
such as |Gamma = x : Int, y : Bool| is encoded as |Gamma = Int,
Bool|; its change context is |Dt^Gamma = Int, Dt^Int, Bool,
Dt^Bool|. This solution is correct and robust, and is the one we
rely on.

\paragraph{Using names}
Next, we discuss issues in implementing this transformation with
names rather than deBrujin indexes. Using names rather than de
Brujin indexes makes terms more readable; this is also why in
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
  that containing change variables. While we used this approach
  in our prototype implementation in
  Scala~\citep{CaiEtAl2014ILC}, it makes our output language
  annoyingly non-standard.
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

  But this change affects the interface of differentiation, in
  particular, which variables are free in output terms. With this
  change, |derive(s, emptyMap)| gives a result
  $\alpha$-equivalent to |derive(s)| if term |s| is closed and
  triggers no capture issues. But if |s| is open, we must
  initialize |m| with mappings from |s|'s free variables to fresh
  variables for their changes. Such variables appear free in |derive(s,
  m)|, so we must modify
  Hence
  hence we must also use modify |Dt ^ Gamma| to use |m| to
  keep rule \textsc{Derive} valid.

  Hence we define $\Delta_m \Gamma$ by adding |m| as a parameter to
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

\baseChangeTypes*
\baseValidity*
\constDifferentiation*
\deriveConstCorrect*

\section{Chapter summary}
\pg{tenses?}

In this chapter, we have formally defined changes for values and environments of
our language, when they are valid. Through these definitions, we have explained
that |derive(t)| is correct, that is, that it maps changes to the input
environment to changes to the output environment. All of this assumes, among
other things, that language plugins define valid changes for their base types
and derivatives for their primitives.

In next chapter, we will discuss operations we provide to construct and use
changes. These operations will be especially useful to provide derivatives of
primitives.
