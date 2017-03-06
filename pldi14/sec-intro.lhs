% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

% \section{Introduction}
\chapter{Introduction to static differentiation}
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
functional languages whose programs can be incrementalized by a
transformation that we call \emph{differentiation}. We will
discuss later why we favor this approach.\pg{where?}

We build our domain-specific functional languages based on
simply-typed $\lambda$-calculus (STLC), extended with \emph{language plugins} to define the domain-specific parts, as discussed in \cref{sec:intro-stlc}.
We show a motivating example for our approach in
\cref{sec:motiv-example}. We define differentiation, state and
prove its correctness theorem in \cref{sec:correct-derive}.

% \section{Our object language: STLC}
% \label{sec:intro-stlc}

% We will define differentiation as a recursive program transformation on terms.
% To be able to define the transformation and state the invariant it satisfies, we
% need to first recall the object language we develop the transformation in.


\section{Generalizing the calculus of finite differences}
%format f_d = "\Delta f"
%format `dot` = "\cdot"
% Revise terminology.
Our theory generalizes an existing field of mathematics called
the \emph{calculus of finite difference}: If |f| is a real
function, one can define its \emph{finite difference}, that is a
function |f_d| such that |f_d a da = f (a + da) - f a|. Readers
might notice the similarity with the derivative of |f|, since it
is defined as $f'(a) = \lim_{da \to 0} (f (a + da) - f(a)) / da$.

The calculus of finite differences provides theorems that in many
cases allow computing a closed formula for |f_d| given a closed
formula for |f|. For instance, if function |f| is defined by |f x
= 2 `dot` x|, one can verify its finite difference is |f_d x dx =
2 `dot` (x + dx) - 2 `dot` x = 2 `dot` dx|.

We consider finite differences helpful for incrementalization
because they allow computing functions on updated inputs based on
results on base inputs, if we know how inputs change. Taking
again |f x = 2 `dot` x|, if |x| is a base input and |x + dx| is
an updated input, we can compute |f (x + dx) = f x + f_d x dx|.
Here, the input change is |dx| and the output change is |f_d x
dx|.

However, the calculus of finite differences is usually defined
for real functions. Since it is based on operators |+| and |-|,
it can be directly extended to commutative groups.
Incrementalization based on finite differences for groups and
first-order programs has already been
researched~\citep{Paige82FDC,GlucheGrust97Incr}, most recently and
spectacularly with DBToaster by
\citet{Koch10IQE} and \citet{Koch2016incremental}.

But it is not immediate how to generalize it beyond groups.
On the other hand, many useful types do not form a
group: for instance, lists of integers don't form a group but
only a monoid. Moreover, it's hard to represent list changes
simply through a list: how do we specify which elements were
inserted (and where), which were removed and which were subjected
to change themselves?

In ILC, we generalize the calculus of finite differences by
using distinct types for base values and changes, and adapting
the surrounding theory.

\section{A motivating example}
\label{sec:motiv-example}
In this section, we illustrate informally incrementalization on a
small example program. We give a more
precise presentation in \cref{sec:correct-derive}.

In the following program, term |grand_total xs ys| sums numbers in
input collections |xs| and |ys|. We also compute an initial
output |output1| on initial inputs |xs1| and |ys1|:

\begin{code}
  grand_total xs ys  = sum (merge xs ys)
  output1            = grand_total xs1 ys1
                     = sum {{1, 2, 3, 4}} = 10
\end{code}

We have called |grand_total| on initial inputs |xs1 = {{1, 2, 3}}| and |ys1 = {{4}}|
to obtain initial output |output1|. Here |{{...}}| denotes a multiset
or \emph{bag} containing the elements among braces. A bag is an
unordered collection (like a set) where elements are allowed to appear more
than once (unlike a set).
In this example, we assume a language plugin that adds support
both integers and bags.

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

To talk about how the differences between old values and new
values, we introduce a few concepts, for now without full definitions.
In our approach to
incrementalization, we describe changes to values as values
themselves: We call such descriptions simply \emph{changes}. Just
like in STLC we have terms (programs) that evaluates to values,
we also have \emph{change terms}, that evaluate to \emph{change
  values}. We require that going from old values to new values
preserves types: That is, if an old value |v1| has type |tau|,
then also its corresponding new value |v2| must have type |tau|.
To each type |tau| we associate a type of changes or change type
|Dt^tau|: a change between |v1| and |v2| must have type |Dt^tau|.

Not all descriptions of changes are meaningful,
so we also talk about \emph{valid} changes.
%
A value |dv| can be a valid change from |v1| to |v2|. We also
call |v1| the source of |dv| and |v2| the destination of |dv|.

We also introduce an operator |`oplus`| on values and changes: if
|dv| is a valid change from |v1| to |v2|, then |v1 `oplus` dv|
(read as ``|v1| updated by |dv|'') is guaranteed to return |v2|.
However, we later show that often |v1 `oplus` dv| can be defined
even if |dv| is not a valid change from |v1| to |v1 `oplus` dv|;
in fact, |`oplus`| is overloaded over types, and for each type
|tau| it has an overload of signature |tau -> Dt ^ tau -> tau|.

To show how incrementalization affects our example, we next
describe valid changes for bags and integers. For now, a change |das|
to a bag |as1| simply contains all elements to be added to the
base bag |as1| to obtain the updated bag |as2| (we'll ignore
removing elements for this section and discuss it later). In our
example, the change from |xs1| (that is |{{1, 2, 3}}|) to |xs2|
(that is |{{1, 1, 2, 3}}|) is |dxs = {{1}}|, while the change
from |ys1| (that is |{{4}}|) to |ys2| (that is |{{4, 5}}|) is
|dys = {{5}}|. To represent the output change |doutput| from
|output1| to |output2| we need integer changes. For now, we
represent integer changes as integers, and define |`oplus`| on
integers as addition: |v1 `oplus` dv = v1 + dv|. For both bags and integers, a
change |dv| is always valid between |v1| and |v2 = v1 `oplus`
dv|; for other changes, however, validity will be more
restrictive.

After introducing these notions, we describe how, in our
approach, we incrementalize our example. We propose to compute
the output change |doutput| from |output1| to |output2| by
calling a new function |dgrand_total|, the \emph{derivative} of
|grand_total| on base inputs and their respective changes. We can
then compute the updated output |output2| as the old output
|output1| updated by change |doutput|. We have successfully
incrementalized our program |grand_total| if not only we get the
correct result for |output2|, but if we also get it faster than
by just calling |grand_total xs2 ys2|.

Below we give the derivative of |grand_total| and show our
approach gives the correct result in this example.

\begin{code}
  dgrand_total xs dxs ys dys  = sum (merge dxs dys)
  doutput                     = dgrand_total xs1 dxs ys1 dys =
                              = sum {{1, 5}} = 6
  output2                     = output1 `oplus` doutput = output1 + doutput
                              = 10 + 6 = 16
\end{code}


Our approach requires a derivative that is asymptotically faster
than its base program. Here, derivative |dgrand_total| simply
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
|derive(t)| evaluates on base inputs and valid inputs changes to a change from |t|
evaluated on old inputs to |t| evaluated on new inputs.
\end{slogan}

In our
example, we can apply |derive(param)| to |grand_total|'s body to
produce |dgrand_total|'s body. After simplifying the result, we get
\[ |derive(sum (merge xs ys)) `cong` sum (merge dxs dys)|.\]
where |`cong`| denotes program equivalence. Correctness of |derive(param)| guarantees
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
informally. Next, we discuss incrementalization on higher-order
terms in \cref{sec:higher-order-intro}, before defining
differentiation in \cref{sec:correct-derive}.

\subsection{Function changes}
\label{sec:higher-order-intro}
A first-class function can close over free variables that can
change, hence functions values can change themselves; hence, we
introduce \emph{function changes} to describe these changes.
For instance, term |tf = \x -> x + y| is a function that closes over
|y|, so if |y| goes from |v1 = 5| to |v2 = 6|, then |f1 = eval(t)
(emptyRho, y = v1)| is different from |f2 = eval(t) (emptyRho, y
= v2)|.
%
Moreover, consider a program |t| that applies |tf| to an input
|x| that varies from |v1 = 1| to |v2 = 2|. Term |derive(tf x)|
needs to compute a change from |f1 v1| to |f2 v2|. We do so using
a change from |v1| to |v2| and a function change from |f1| to
|f2| by defining function changes suitably.

So, we require that a valid function change from |f1| to |f2|
(where |f1, f2 : eval(sigma -> tau)|) is in turn a function |df|
that takes an input |a1| and a change |da|, valid from |a1| to
|a2|, to a valid change from |f1 a1| to |f2 a2|.
\paragraph{Discussion}
It would be more symmetric to make function changes also take
updated input |a2|, that is, have |df a1 da a2| computes a change
from |f1 a1| to |f2 a2|. However, passing |a2| explicitly adds no
information: the value |a2| can be computed from |a1| and |da| as
|a1 `oplus` da|. Indeed, in various cases a function change can
compute its required output without actually computing |a1
`oplus` da|. Finally, if the size of |a1| and |a2| is
asymptotically larger than |da|, actually computing |a2| could be
expensive. Hence, we stick to our asymmetric form of function
changes. We will discuss other alternatives later.\pg{Where?}

% To answer these
% questions precisely, we next recall definitions of our object
% language, simply-typed $\lambda$-calculus.

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

\section{Differentiation and its meaning}
\label{sec:correct-derive}

In this section, we make our previous discussion precise: we
introduce differentiation and state and prove its correctness. We
also elaborate on its effect on higher-order programs.

To support incrementalization, we also motivate and introduce in
this section (a) a description of changes and operations on
changes; (b) a definition of which changes are valid; (c) a
compositional term-to-term transformation called differentiation
and written |derive(t)| that produces incremental programs. We
have already mentioned the different concepts and how they fit
together. We next explain definitions and show key equations. We
collect the complete definitions and crucial lemmas in
\cref{fig:differentiation}.

First, we define for each type |tau| when |dv| is a valid change
from |v1| to |v2|, where |v1| and |v2| are values of type |tau|.
We first introduce, for for each type |tau|, a type |Dt^tau| that
we call a \emph{change type} (as defined in \cref{fig:change-types}).
We require |dv| to belong to
|eval(Dt^tau)|.
%
Then, we define \emph{validity} as a family of ternary relations,
indeed by types and relating changes with their sources and
destinations.
%
We say that |dv| is valid change from |v1| to |v2|, and write
|fromto tau v1 dv v2|, if |dv : eval(Dt^tau)|, |v1, v2 :
eval(tau)|, if |dv| is a ``valid'' description of the difference
from |v1| to |v2|, as we define in \cref{fig:validity}.
%
We refer
to values of change types as \emph{change values}.

Next, we explain the definitions of change types and validity for
function type |sigma -> tau|.
%
Take function values |f1, f2 : eval(sigma -> tau)|. As discussed
informally, a valid function change |df| from |f1| to |f2| must
take as arguments (a) a base input |v1 : eval(sigma)| and (b) a valid
input change |dv| from |v1| to updated input |v2 : eval(sigma)|.
The result of this application, |df v1 dv|, must give a change
from |f1 v1| to |f2 v2|. We
formalize this requirement as the definition of validity for
functions changes. Hence, we define change type |Dt^(sigma ->
tau)| as |sigma -> Dt ^ sigma -> Dt ^ tau|, and we define
validity on function types as:
\begin{align*}
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
first define the shape of change environments by defining change
contexts |Dt^Gamma| as follows:
\begin{align*}
  \Delta\EmptyContext &= \EmptyContext \\
  \Delta\Extend{x}{\tau} &= \Extend{\Extend[\Delta\Gamma]{x}{\tau}}{\D x : \Delta\tau}\text{.}
\end{align*}
Then, we describe validity of change
environments via a judgment.
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

Finally, we define when a change term is a correct change for a
base term. We say a term |dt| is a correct change for term |t|
(at type |tau|), and write |correct(tau) dt t|, if there exists a
context |Gamma| such that |Gamma /- t : tau|, |Dt ^ Gamma /- dt :
Dt^tau|, and |eval(dt) drho| is a valid change from |eval(t)
rho1| to |eval(t) rho2| whenever |fromto Gamma rho1 drho rho2|.
In other words, |eval(dt)| must map changes from old to new
inputs to changes from old to new outputs, where we refer to
inputs and outputs of |t|.

\subsection{Correctness of differentiation}
Roughly, our goal is that evaluating |derive(t)| (where |t| is a
well-typed term) maps an environment change |drho| from |rho1| to
|rho2| into a result change |eval(derive(t)) drho|, going from
|eval(t) rho1| to |eval(t) rho2|. That is, |derive(t)| must be a
correct change for |t|.

Hence |derive(param)| must have the right static semantics (that
is, the right typing), so that |derive(t)| maps changes to |t|'s
inputs to changes to |t|'s output. That is, we require it to
satisfy the following derived typing rule:

\begin{restatable}[Typing of |derive(param)|]{lemma}{deriveTyping}
  \label{lem:derive-typing}
  Transformation |derive(param)| satisfies derived typing rule:
  \begin{typing}
    \Rule[Derive]
    {|Gamma /- t : tau|}
    {|Dt ^ Gamma /- derive(t) : Dt ^ tau|}
  \end{typing}
\end{restatable}

Next, we constrain |derive(t)|'s dynamic semantics, that is the
result of evaluating it.
%
Recall that we'll define operator |`oplus`|, such that |v1
`oplus` dv = v2| holds whenever |dv| is a valid change between
|v1| and |v2|.

Once we define these notions, we can state |derive(param)|'s true
correctness statement: whenever |t| is well-typed, |derive(t)| is
a correct change for |t|. Formally we have:
\begin{restatable}[Correctness of |derive(param)|]{theorem}{deriveCorrect}
  \label{thm:correct-derive}
  If |Gamma /- t : tau|, then |derive(t)| is a correct change for |t|.
  That is, if |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |fromto tau (eval(t) rho1) (eval(derive(t)) drho) (eval(t) rho2)|.
\end{restatable}

Once we define |`oplus`| we'll be able to relate it to validity. The statement we'll prove is
\begin{restatable}[Valid changes update correctly]{lemma}{validOplus}
  \label{thm:valid-oplus}
  If |fromto tau v1 dv v2| then |v1 `oplus` dv = v2|.
\end{restatable}

And as a corollary of \cref{thm:correct-derive,thm:valid-oplus}, we can deduce that
updating base result |eval(t) rho1| by change |eval(derive(t)) drho| via |`oplus`|
gives the updated result |eval(t) rho2|.
\begin{restatable}[Correctness of |derive(param)|, corollary]{corollary}{deriveCorrectOplus}
  \label{thm:correct-derive-oplus}
  If |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |eval(t) rho1 `oplus` eval(derive(t)) drho = eval(t) rho2|.
\end{restatable}

\input{pldi14/fig-differentiation}

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

After stating these requirements, we define |derive(param)| and prove the requirements hold.
The transformation is defined by:
\begin{code}
  derive(\x -> t) = \x dx -> derive(t)
  derive(s t) = derive(s) t (derive(t))
  derive(x) = dx
  derive(c) = ...
\end{code}
  % derive(^^let x = t1 in t2) =
  %   let  x = t1
  %        dx = derive(t1)
  %        in   derive(t2)



Now we can characterize |derive(param)|'s static semantics:
\deriveTyping*
\begin{proof}
  The thesis can be proven by induction on the typing derivation
  |Gamma /- t : tau|.
\end{proof}

To illustrate correctness statement \cref{thm:correct-derive}, it
is helpful to look first at its proof. Readers familiar with
logical relations proofs should be able to reproduce this proof
on their own, as it is rather standard, once one uses the given
definitions. Nevertheless, we spell it out, and use it to
motivate how |derive(param)| is defined. For each case, we first
give a short proof sketch, and then redo the proof in more
detail to make the proof easier to follow.
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
  |fromto (sigma -> tau) (^&^ eval(s) rho1) (eval(derive(s)) drho) (eval(s) rho2)|
  =\\
    &|forall a1 a2 : eval(sigma), da : eval(Dt ^ sigma)|\\
  &\text{ if }|fromto (sigma) a1 da a2| \\
  & \text{ then }
    |fromto (tau) ((eval(s) rho1) a1) ((eval(derive(s)) drho) a1 da) ((eval(s) rho2) a2)|
\end{align*}
Instantiating in this statement |fromto (sigma) a1 da a2| by |fromto sigma (eval(t)
rho1) (eval(derive(t)) drho) (eval(t) rho2)| gives the thesis.

  \item Case |Gamma /- \x -> t : sigma -> tau|. By inversion of typing,
    |Gamma , x : sigma /- t : tau|.

    In short, our thesis is that |derive(\x -> t)| is a correct
    change for |\x -> t|. By induction on |t| we know that
    |derive(t)| is a correct change for |t|. We show these two
    correctness claims mean the same thing since we pick
    |derive(\x -> t) = \x dx -> derive(t)|. By |derive(param)|'s
    typing you can show that |Dt^Gamma, x : sigma, dx : Dt^sigma
    /- derive(t): tau|. Now, |eval(\x dx -> derive(t))| is just a
    curried version of |eval(derive(t))|; to wit, observe their
    meta-level types:
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
    -> t)| is a correct change for |\x -> t|. By the definition
    of correctness, and of validity of function type, the thesis
    means
    \begin{multline*}
      |fromto (sigma -> tau) (^^^(\a1 -> eval(t) (rho1, x = a1))) (\a1 da -> eval(derive(t)) (drho, x = a1, dx = da)) ((\a2 -> eval(t) (rho2, x = a2)))|.
    \end{multline*}
      That is, for any |a1, a2, da| such that |fromto sigma a1 da a2|, we must have
    \[|fromto tau (eval(t) (rho1, x = a1)) (eval(derive(t))
      (drho, x = a1, dx = da)) (eval(t) (rho2, x = a2))|.\]

    To do so, take the inductive hypothesis on |t|. Since
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
  \end{itemize}
\end{proof}

\subsection{Discussion}
\pg{In this section we clarify a few points... about what?}
%
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

\paragraph{Deriving closed terms of function type}
If we differentiate a closed term |/- t : tau|, we get a change
term |derive(t)| from |t| to itself\pg{Lexicon not introduced for
  terms.}: |fromto tau (eval(t)
emptyRho) (eval(derive(t)) emptyRho) (eval(t) emptyRho)|. We call such changes nil changes;
they're important for two reasons. First, we will soon see that a
unit element for |`oplus`| has its uses. Second, nil changes at
function type are even more useful. A nil function change for
function |f| takes an input |v1| and input change |dv| to a
change from |f v1| and |f (v1 `oplus` dv)|. In other words, a nil
function change for |f| is a \emph{derivative} for |f|!

\pg{Define nil changes?}
\paragraph{Constraining |`oplus`| on functions}
Next, we discuss how |`oplus`| should be defined on functions.
We show that we must set |f1 `oplus` df = \v -> f1 x `oplus` df v
(nil v)|.

We know that a valid function change |valid (sigma -> tau) df f1
f2| takes valid input changes |valid sigma dv v1 v2| to a valid
output change |valid tau (df v1 dv) (f1 v1) (f2 v2)|. We require
that |`oplus`| agrees with validity, so |f2 = f1 `oplus` df|, |v2
= v1 `oplus` dv| and |f2 v2 = (f1 `oplus` df) (v1 `oplus` dv) =
f1 v1 `oplus` df v1 dv|. Replacing |dv| with |nil v| gives
|(f1 `oplus` df) v1 = f1 v1 `oplus` df v1 (nil v)|.

It also follows that |f1 v1 `oplus` df v1 dv = (f1 `oplus` df)
(v1 `oplus` dv) = f1 (v1 `oplus` dv) `oplus` df (v1 `oplus` dv)
(nil (v1 `oplus` dv))|. It turns out that this equation, together
with a weaker form of validity preservation, characterizes
function changes.

\paragraph{Updating values by changes with |`oplus`|}
Next, we will introduce formally operator |`oplus`| and relate it
to validity. In particular, we will prove that |fromto tau v1 dv
v2| implies |v1 `oplus` dv = v2|, and explain why the converse is
not true.

\validOplus*

\deriveCorrectOplus*


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
