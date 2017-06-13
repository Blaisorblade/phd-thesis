% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Introduction}
\label{sec:intro}
\label{ch:static-diff-intro}

Incremental computation (or incrementalization) has a long-standing history in
computer science~\citep{Ramalingam93}.
Often, a program needs to update quickly the output of some nontrivial function $f$
when the input to the computation changes. In this scenario, we assume we have
computed |y1 = f x1| and we need to compute |y2| that equals |f x2|.
In this scenario, programmers typically have to choose between a few undesirable
options.
\begin{itemize}
\item Programmers can call again function |f| on the updated input |x2| and
  repeat the computation from scratch. This choice guarantees
  correct results and is easy to implement, but typically wastes
  computation time. Often, if the updated input is close to the
  original input, the same result can be computed much faster.
\item Programmers can write by hand a new function |df| that updates the
  output based on input changes, using various techniques.
  Running a hand-written function |df| can be much more efficient than rerunning
  |f|, but writing |df| requires significant developer effort, is
  error-prone, and requires updating |df| by hand to keep it consistent with |f|
  whenever |f| is modified. In practice, this complicates code maintenance
  significantly~\citep{Salvaneschi13reactive}.
\item Programmers can write |f| using domain-specific languages that
  support incrementalization, for tasks where such languages are
  available. For instance, build scripts (our |f|) are written in
  domain-specific languages that support (coarse-grained)
  incremental builds. Database query languages also have often
  support for incrementalization. \pg{Mention here limits?}
\item Programmers can attempt using general-purpose techniques for
  incrementalizing programs, such as \emph{self-adjusting
    computation} and variants such as \emph{Adapton}. Self-adjusting
  computation applies to arbitrary purely functional programs and
  has been extended to imperative programs; however, it only
  guarantees efficient incrementalization when applied to base
  programs that are \emph{designed} for efficient
  incrementalization.\pg{Citations}
  Nevertheless, self-adjusting computation allowed incrementalizing programs
  that had never been incrementalized by hand before.
\end{itemize}


\pg{Resume and readd this text.}
% To understand how to compute |f| incrementally, we can summarize the key idea
% behing many incrementalization approaches.\pg{self-adjusting computation.}\pg{?}
% Let us assume, for simplicity, our function |f| is written in a purely
% functional language. During a computation such as |y = f x1|, each computation
% step produce an output using some inputs. The new output can in turn be used as
% input by further steps. We can record these computation steps as a directed
% acyclic graph (DAG) representing dependencies: each node is either an initial
% input or the output of some computation steps, and each output node has incoming
% edges from all

\pg{Continue discussing dependencies minimization and the
  relation with parallelism. Build scripts might be a good
  example.}

No approach guarantees automatic efficient incrementalization for arbitrary
programs.
We propose instead to design domain-specific languages
(DSLs) that can be efficiently incrementalized, that we call \emph{incremental}
DSLs (IDSLs).
An incremental DSL is a higher-order purely functional language, composed of a
$\lambda$-calculus core extended with base types and primitives.
To incrementalize such programs, we use a transformation that we call
\emph{differentiation}. Differentiation produces programs in the same language,
that can be optimized further and compiled to efficient code.
For primitives, IDSL designers must specify the result of
differentiation: IDSL designers are to choose primitives that encapsulate
efficiently incrementalizable computation schemes, while IDSL users are to
express their computation using the primitives provided by the IDSL.
We propose that IDSLs be higher-order, so that primitives can be parameterized
over functions and hence highly flexible.\pg{why not
  defunctionalize/closure convert/...?}

\pg{actually argue for higher-order collection DSLs over relational databases;
  we didn't do that in the cited thesis section.}
%
Our primary example will be DSLs for operations on collections:
as discussed earlier (\cref{sec:aosd13-intro}), we favor
higher-order collection DSLs over relational databases.
% moving data to relational databases requires transforming them to
% a rather different metamodel
%
\pg{ What I'm saying... should also hopefully apply to data
  layout transformations used in databases.
Flattening? Nested data? Sharding?
  And data layout transformations *are*
  available in LMS... but not in GPLs?}
% We will discuss later why we favor this
% approach.\pg{where?}

We build our incremental DSLs based on
simply-typed $\lambda$-calculus (STLC), extended with
\emph{language plugins} to define the domain-specific parts, as
discussed in \cref{sec:intro-stlc}. We call our approach
\emph{ILC} for \emph{Incremental Lambda Calculus}.

The rest of this chapter is organized as follows.
In \cref{sec:generalize-fin-diff} we explain that 
differentiation generalizes the calculus of finite differences, a relative of
differential calculus.
In \cref{sec:motiv-example} we show a motivating example for
our approach.
In \cref{sec:change-intro} we introduce informally 
the concept of \emph{changes} as values, and in \cref{sec:higher-order-intro} we
introduce \emph{changes to functions}.
In \cref{sec:informal-derive} we define differentiation and motivate it
informally.
In \cref{sec:derive-example} we apply differentiation to our motivating example.

Correctness of ILC is far from obvious. In
\cref{ch:derive-formally,ch:change-theory}, we introduce a formal theory of
changes, and we use it to formalize differentiation and prove it correct.
\pg{check later this TOC}

\section{Generalizing the calculus of finite differences}
\label{sec:generalize-fin-diff}
%format f_d = "\Delta f"
%format `dot` = "\cdot"
% Revise terminology.
Our theory of changes generalizes an existing field of mathematics called
the \emph{calculus of finite difference}: If |f| is a real
function, one can define its \emph{finite difference}, that is a
function |f_d| such that |f_d a da = f (a + da) - f a|. Readers
might notice the similarity (and the differences) between the
finite difference and the derivative of |f|, since the latter is
defined as
\[f'(a) = \lim_{\Varid{da} \to 0} \frac{f (a + \Varid{da}) - f(a)}{\Varid{da}}.\]

The calculus of finite differences helps computing a closed
formula for |f_d| given a closed formula for |f|. For instance,
if function |f| is defined by |f x = 2 `dot` x|, one can prove
its finite difference is |f_d x dx = 2 `dot` (x + dx) - 2 `dot` x
= 2 `dot` dx|.

Finite differences are helpful for incrementalization because
they allow computing functions on updated inputs based on results
on base inputs, if we know how inputs change. Take again for
instance |f x = 2 `dot` x|: if |x| is a base input and |x + dx|
is an updated input, we can compute |f (x + dx) = f x + f_d x
dx|. If we already computed |y = f x| and reuse the result, we
can compute |f (x + dx) = y + f_d x|. Here, the input change is
|dx| and the output change is |f_d x dx|.

However, the calculus of finite differences is usually defined
for real functions. Since it is based on operators |+| and |-|,
it can be directly extended to commutative groups.
Incrementalization based on finite differences for groups and
first-order programs has already been
researched~\citep{Paige82FDC,GlucheGrust97Incr}, most recently and
spectacularly with DBToaster~\citep{Koch10IQE,Koch2016incremental}.

But it is not immediate how to generalize finite differencing
beyond groups. And many useful types do not form a group: for
instance, lists of integers don't form a group but only a monoid.
Moreover, it's hard to represent list changes simply through a
list: how do we specify which elements were inserted (and where),
which were removed and which were subjected to change themselves?

In ILC, we generalize the calculus of finite differences by
using distinct types for base values and changes, and adapting
the surrounding theory. ILC generalizes operators |+| and |-| as operators
|`oplus`| (pronounced ``oplus'' or ``update'') and |`ominus`| (pronounced
``ominus'' or ``difference''). We show how ILC subsumes groups in
\cref{sec:change-structure-groups}.

%format s1
%format s2
\section{A motivating example}
\label{sec:motiv-example}
In this section, we illustrate informally incrementalization on a
small example.

In the following program, |grand_total xs ys| sums integer numbers in
input collections |xs| and |ys|.

\begin{code}
  grand_total        :: Bag Int -> Bag Int -> Int
  s                  :: Int

  grand_total xs ys  = sum (merge xs ys)
  s                  = grand_total xs ys
\end{code}

This program computes output |s| from input collections |xs| and
|ys|. These collections are multisets or \emph{bags}, that is,
collections that are unordered (like sets) where elements are
allowed to appear more than once (unlike sets). In this example,
we assume a language plugin that supports a base type of integers
|Int| and a family of base types of bags |Bag tau| for any type
|tau|.

We can run this program on specific inputs |xs1 = {{1, 2, 3}}|
and |ys1 = {{4}}| to obtain output |s1|. Here, double braces
|{{...}}| denote a bag containing the elements among the double
braces.

\begin{code}
  s1                 = grand_total xs1 ys1
                     = sum {{1, 2, 3, 4}} = 10
\end{code}

This example uses small inputs for simplicity, but in practice they
are typically much bigger; we use |n|
to denote the input size. In this case the asymptotic complexity of computing
|s| is |Theta(n)|.

Consider computing updated output |s2| from updated inputs |xs2 = {{1, 1, 2, 3}}|
and |ys2 = {{4, 5}}|. We could recompute |s2| from scratch as
\begin{code}
  s2           = grand_total xs2 ys2
               = sum {{1, 1, 2, 3, 4, 5}} = 16
\end{code}
But if the size of the updated inputs is |Theta(n)|, recomputation also
takes time |Theta(n)|, and we would like to obtain our result asymptotically faster.

To compute the updated output |s2| faster, we assume the changes to the
inputs have a description of size |dn| that is asymptotically smaller than the
input size |n|, that is |dn = o(n)|. All approaches to incrementalization
require small input changes. Incremental computation will then process the input
changes, rather than just the new inputs.

\section{Introducing changes}
\label{sec:change-intro}
To talk about how the differences between old values and new
values, we introduce a few concepts, for now without full definitions.
In our approach to
incrementalization, we describe changes to values as values
themselves: We call such descriptions simply \emph{changes}. Just
like in STLC we have terms (programs) that evaluates to values,
we also have \emph{change terms}, which evaluate to \emph{change
  values}. We require that going from old values to new values
preserves types: That is, if an old value |v1| has type |tau|,
then also its corresponding new value |v2| must have type |tau|.
To each type |tau| we associate a type of changes or \emph{change type}
|Dt^tau|: a change between |v1| and |v2| must be a value of type |Dt^tau|.

Not all descriptions of changes are meaningful,
so we also talk about \emph{valid} changes.
%
A change value |dv| can be a valid change from |v1| to |v2|. We
can also consider a valid change as an edge from |v1| to |v2| in
a graph associated to |tau| (where the vertexes are values of
type |tau|), and we call |v1| the source of |dv| and |v2| the
destination of |dv|. We only talk of source and destination for valid changes:
so a change from |v1| to |v2| is (implicitly) valid.
We'll discuss examples of valid and invalid
changes in \cref{ex:valid-bag-int,ex:invalid-nat}. \pg{What about
  changes with multiple valid sources?}

We also introduce an operator |`oplus`| on values and changes: if
|dv| is a valid change from |v1| to |v2|, then |v1 `oplus` dv|
(read as ``|v1| updated by |dv|'') is guaranteed to return |v2|.
However, we later show that often |v1 `oplus` dv| can be defined
even if |dv| is not a valid change from |v1| to |v1 `oplus` dv|.
Again, if |dv| is not valid from |v1| to |v1 `oplus` dv|, then we do not talk of
the source and destination of |dv|.

We also introduce operator |`ominus`|: given two values |v1, v2|
for the same type, |v2 `ominus` v1| is a valid change from |v1|
to |v2|.

Finally, we introduce change composition: if |dv1| is a valid
change from |v1| to |v2| and |dv2| is a valid change from |v2| to
|v3|, then |ocompose dv1 dv2| is a valid change from |v1| to
|v3|.

Change operators are overloaded over different types.
Coherent definitions of validity and of operators |`oplus`, `ominus`| and
|`ocompose`| for a type |tau| form a \emph{change structure} over values of type
|tau| (\cref{def:change-structure}).
For each type |tau| we'll define a change structure (\cref{def:chs-types}),
and operators will have types |`oplus` : tau -> Dt ^ tau -> tau|, |`ominus` :
tau -> tau -> Dt ^ tau|, |`ocompose` : Dt^tau -> Dt^tau -> Dt^tau|.

\begin{example}[Changes on integers and bags]
  \label{ex:valid-bag-int}
  \label{ex:chs-int}
 \pg{changes on bags?}
To show how incrementalization affects our example, we next
describe valid changes for integers and bags.
%
For now, a change
|das| to a bag |as1| simply contains all elements to be added to
the initial bag |as1| to obtain the updated bag |as2| (we'll ignore
removing elements for this section and discuss it later). In our
example, the change from |xs1| (that is |{{1, 2, 3}}|) to |xs2|
(that is |{{1, 1, 2, 3}}|) is |dxs = {{1}}|, while the change
from |ys1| (that is |{{4}}|) to |ys2| (that is |{{4, 5}}|) is
|dys = {{5}}|.
%
To represent the output change |ds| from
|s1| to |s2| we need integer changes. For now, we
represent integer changes as integers, and define |`oplus`| on
integers as addition: |v1 `oplus` dv = v1 + dv|.
\end{example}

For both bags and integers, a change |dv| is always valid between
|v1| and |v2 = v1 `oplus` dv|; for other changes, however,
validity will be more restrictive.
\begin{example}[Changes on naturals]
  \label{ex:invalid-nat}
For instance, say we want to
define changes on a type of natural numbers, and we still want to
have |v1 `oplus` dv = v1 + dv|. A change from |3| to |2| should
still be |-1|, so the type of changes must be |Int|. But the
result of |`oplus`| should still be a natural, that is an integer
|>= 0|: to ensure that |v1 `oplus` dv >= 0| we need to require
that |dv >= -v1|. We use this requirement to define validity on
naturals: |fromto Nat v1 dv (v1 + dv)| is defined as equivalent to
|dv >= -v1|. We can guarantee equation |v1 `oplus` dv = v1 + dv|
not for all changes, but only for valid changes. Conversely, if a
change |dv| is invalid for |v1|, then |v1 + dv < 0|. We then
define |v1 `oplus` dv| to be |0|, though any other definition on
invalid changes would work.\footnote{In fact, we could leave
  |`oplus`| undefined on invalid changes. Our original
  presentation~\citep{CaiEtAl2014ILC}, in essence, restricted
  |`oplus`| to valid changes through dependent types, by ensuring
  that applying it to invalid changes would be ill-typed. Later,
  \citet{Huesca2015incrementality}, in similar developments,
  simply made |`oplus`| partial on its domain instead of
  restricting the domain, achieving similar results.}
\end{example}
\pg{bags with removals? where?}

\subsection{Incrementalizing with changes}
After introducing changes and related notions, we describe how we incrementalize
our example program.

We consider again the scenario of \cref{sec:motiv-example}: we need to compute
the updated output |s2|, the result of calling our program |grand_total| on
updated inputs |xs2| and |ys2|. And we have the initial output |s1| from calling our
program on initial inputs |xs1| and |ys1|. In this scenario we can compute |s2|
\emph{non-incrementally} by calling |grand_total| on the updated inputs, but
we would like to obtain the same result faster.
Hence, we compute |s2| \emph{incrementally}: that is, we first compute the
\emph{output change} |ds| from |s1| to |s2|; then we update the old output |s1|
by change |ds|. Successful incremental computation must compute the correct |s2|
asymptotically faster than non-incremental computation. This speedup is possible
because we take advantage of the computation already done to compute |s1|.

To compute the output change |ds| from |s1| to |s2|, we propose to transform our
\emph{base program} |grand_total| to a new program |dgrand_total|, that we call
the \emph{derivative} of |grand_total|, and call |dgrand_total| on initial inputs
and their respective changes.
Unlike other approaches to incrementalization, |dgrand_total| is a regular
program in the same language as |grand_total|, hence can be further optimized
with existing technology.

Below, we give the code for |dgrand_total| and show that in this example
incremental computation computes |s2| correctly.

For ease of reference, we recall inputs, changes and outputs:
\begin{code}
  xs1                         = {{1, 2, 3}}
  dxs                         = {{1}}
  xs2                         = {{1, 1, 2, 3}}
  ys1                         = {{4}}
  dys                         = {{5}}
  ys2                         = {{4, 5}}
  s1                          = grand_total xs1 ys1
                              = 10
  s2                          = grand_total xs2 ys2
                              = 16
\end{code}
Incremental computation uses the following definitions to compute |s2| correctly
and with fewer steps, as desired.
\begin{code}
  dgrand_total xs dxs ys dys  = sum (merge dxs dys)
  ds                          = dgrand_total xs1 dxs ys1 dys =
                              = sum {{1, 5}} = 6
  s2                          = s1 `oplus` ds = s1 + ds
                              = 10 + 6 = 16
\end{code}

Incremental computation should be asymptotically faster than non-incremental
computation; hence, the derivative we run should be asymptotically faster than
the base program.
Here, derivative |dgrand_total| is faster simply because it \emph{ignores} initial
inputs altogether. Therefore, its time complexity depends only on the total size
of changes |dn|. In particular, the complexity of |dgrand_total| is |Theta(dn) =
o(n)|.

We generate derivatives through a program transformation from terms to terms,
which we call \emph{differentiation} (or, sometimes, simply \emph{derivation}).
We write |derive t| for the result of
differentiating term |t|. We apply |derive| on terms of our non-incremental
programs or \emph{base terms}, such as |grand_total|. To define differentiation,
we assume that we already have derivatives for primitive functions they use; we
discuss later how to write such derivatives by hand.
%
\pg{Move this below, after we explain the case for functions.}
Differentiation only produces derivatives on closed terms of function type, in short
``functions'', but it is defined as a structurally recursive program
transformation, hence it is also defined on open terms.

A derivative of a function can be applied to initial inputs and changes from initial
inputs to updated inputs, and returns a change from an initial output to an
updated output. For instance, for derivative |dgrand_total|, initial inputs
|xs1| and |ys1|, and changes |dxs| and |dys| from initial inputs to updated
inputs, change |dgrand_total xs1 dxs ys1 dys| (that is |ds|) goes from initial
output |grand_total xs1 ys1| (that is |s1|) to updated output |grand_total xs2
ys2| (that is |s2|).
We often just say that a derivative
of function |f| maps changes to the inputs of |f| to changes to the outputs of
|f|, leaving the initial inputs implicit. In short:
\begin{restatable}{slogan}{sloganDerive}
  \label{slogan:derive}
  \emph{Term |derive(t)| maps input changes to output changes.}
  That is, |derive(t)| applied to initial base inputs and valid \emph{input changes}
  (from initial inputs to updated inputs) gives a valid \emph{output change} from |t|
  applied on old inputs to |t| applied on new inputs.
\end{restatable}

Since |ds| is a valid change from |s1| to |s2|, it follows as a corollary that
|s2 = s1 `oplus` ds|, and this equation justifies incrementalization. For a
generic unary function |f|, this corollary can be stated as:
\begin{equation}
  % \label{eq:derivative-requirement}
  \label{eq:correctness}
  |f a2 `cong` f a1 `oplus` (derive f) a1 da|
\end{equation}
or as
\begin{equation}
  % \label{eq:derivative-requirement}
  \label{eq:correctness-alt}
  |f (a1 `oplus` da) `cong` f a1 `oplus` (derive f) a1 da|
\end{equation}
where we use |`cong`| to mean denotational equality (that is, |t1
`cong` t2| if and only if |eval(t1) = eval(t2)|), and where |da| is a valid
change from |a1| to |a2| (and |f, a1, a2| have compatible types).
But |(derive f) a1 da| is also a valid change, a fact not captured by these equations.
We will prove these equations as a consequence of \cref{thm:derive-correct}.\pg{where?}\pg{resume}

% Informally, |derive t| maps changes to the inputs of |t| to changes to the
% outputs of |t|. Take |t = grand_total|: as discussed,
% |dgrand_total xs1 dxs ys1 dxs| computes the change in |grand_total|'s output |s|
% based on the changes to inputs |xs| and |ys|. In short, we say that
% |dgrand_total|, that is |derive grand_total|, maps input changes to output
% changes.

\pg{Moved from here.}

% In next chapter we define this
% invariant formally; we
% prove that |derive| satisfies this invariant in 
% For now, we just anticipate what this means in a few classes of examples.
% Recall that we can evaluate |t| to its value |eval t rho|
% if we have an environment |rho|; for closed terms this environment will be
% empty. Then, if |t| has function type, |eval t rho| will accept other inputs.
% Analogously,
% for any term |t|, |eval (derive t) drho| produces a
% change from |eval t rho1| to |eval t rho2| when |drho| is a change from |rho1|
% to |rho2|.
% If |t| is a unary function, then |eval (derive t) drho a1 da| is a change from
% |eval t rho1 a1| to |eval t rho2 a2| if |drho| is a change from |rho1| to |rho2|
% and |da| is a change from |a1| to |a2|.
% If |t| is a binary function, like |grand_total|, then |eval (derive t) drho a1
% da b1 db| is a change from |eval t rho1 a1 b1| to |eval t rho2 a2 b2| if |drho|
% is a change from |rho1| to |rho2|, |da| is a change from |a1| to |a2| and |db|
% is a change from |b1| to |b2|. And so on for ternary, ...,  |n|-ary functions.

% We sum up the previous paragraph with the following slogan:

% \begin{restatable}{slogan}{sloganDerive}
%   \label{slogan:derive}
%   Term |derive(t)| maps input changes to output changes.
%   That is, |derive(t)| applied to old base inputs and valid \emph{input changes}
%   (from old inputs to new inputs) gives a valid \emph{output change} from |t|
%   applied on old inputs to |t| applied on new inputs.
% \end{restatable}


% What's more, we define |derive(param)| \emph{compositionally}:
% |derive(t)| is defined in terms of |derive(param)| applied to
% subterms of |t|.

\pg{So we still need to say ``a derivative'', not ``the derivative''.}
In our example, we have applied |derive(param)| to
|grand_total|, and simplify the result via
$\beta$-reduction to produce |dgrand_total|, as we show in \cref{sec:derive-example-merge}.
%\pg{drop?}
Correctness of |derive(param)| guarantees
that |sum (merge dxs dys)| evaluates to a change from
|sum (merge xs ys)| evaluated on old inputs |xs1, ys1| to
|sum (merge xs ys)| evaluated on new inputs |xs2, ys2|.

% \pg{rerevise and drop}
% Here, a derivative of |grand_total| is a function in the same language as
% |grand_total|, that accepts changes from initial inputs |xs1| and |ys1| to
% updated inputs |xs2| and |ys2| and evaluates to the change from the base result
% |grand_total xs1 ys1| to the updated result |grand_total xs2 ys2|.

% \pg{rerevise and drop}
% More in general, for a unary function |f|, a derivative |df|
% takes an input |a| and a change |da| for |a| and produces a
% change from base output |f a| to updated output |f (a `oplus`
% da)|. Symbolically we write
% %   \label{eq:correctness}
% % \begin{equation}
% %   \label{eq:derivative-requirement}
% %   |f (a `oplus` da) `cong` f a `oplus` df a da|
% % \end{equation}
% where we use |`cong`| to mean denotational equality (that is, |t1
% `cong` t2| if and only if |eval(t1) = eval(t2)|).

% \pg{rerevise and drop}
% We claim that differentiation produces derivatives. Hence, we can
% take \cref{eq:derivative-requirement}, replace |df| by
% |derive(f)|, and obtain as a corollary the following equation:
% \begin{equation}
%   \label{eq:correctness}
%   |f (a `oplus` da) `cong` (f a) `oplus` (derive(f) a da)|
% \end{equation}
% We will prove this equation as a consequence of \cref{thm:derive-correct}.\pg{resume} 

% \pg{rerevise and drop}
% For functions |f| of multiple arguments, a derivative |df| takes
% all base inputs of |f| together with changes to each of them, and
% produces a change from the base output to the updated output. We
% will make this more formal in next section.

In this section, we have sketched the meaning of differentiation
informally. We discuss incrementalization on higher-order
terms in \cref{sec:higher-order-intro}, and actually define
differentiation in \cref{sec:informal-derive}.

% \pg{Why show a change structure in Haskell terms?}
% We already sketch, preliminarly, how a change structure
% can be represented in Haskell terms: a change structure is
% encoded as a \emph{type class} named |ChangeStruct t|, where change type
% |Dt^tau| is defined as an associated type |Dt^t|, and operations
% |`oplus`|, |`ominus`| and |`ocompose`| are defined as methods.
% \begin{code}
% class ChangeStruct t where
%   type Dt t
%   oplus :: t -> Dt t -> t
%   ominus :: t -> t -> Dt t
%   (`ocompose`) :: Dt t -> Dt t -> Dt t
% \end{code}
% We'll come back to this definition and refine it,
% describing the laws it satisfies, in \cref{sec:change-struct-tc}.

%format y1
%format y2
%format tf = "t_f"
%format dtf = "\Varid{dt}_f"
\section{Function changes}
\label{sec:higher-order-intro}
We now look at |derive|'s behavior more in general.
functions themselves can change.

% \subsection{Open terms}
The value of an open term |Gamma /- t : tau| depends on the environment |rho :
eval(Gamma)|. If we evaluate |t| against two suitable different environments
|rho1, rho2 : eval(Gamma)|, we will typically compute different results
|v1 = eval t rho1| and |v2 = eval t rho2|.
We can compute an output change (going from |v1| to |v2|) using |derive|.
As promised informally by our slogan, evaluating our derivative via |eval
(derive t)| maps an ``input change'' |drho| (in this case, an environment
change, describing changes to each element of the environment) to an output
change |dv| from |v1| to |v2|.
%
If |tau| is a function type, |dv| will be a \emph{function change}.

Since the concept of function changes can be surprising, we examine it more
closely next.

\subsection{Producing function changes}

A first-class function can close over free variables that can
change, hence functions values themselves can change; hence, we
introduce \emph{function changes} to describe these changes.

% Mapping from variables to values:
% x -> a
% y -> v

For instance, term |tf = \x -> x + y| is a function that closes
over |y|, so different values |v| for |y| give rise to different
values for |f = eval(tf) (y = v)|. Take a change |dv| from |v1
= 5| to |v2 = 6|; different inputs |v1| and |v2| for |y| give
rise to different outputs |f1 = eval(tf) (y = v1)| and |f2 =
eval(tf) (y = v2)|.
%
We describe the difference between outputs |f1| and |f2| through a function
change |df| from |f1| to |f2|.

Consider again \cref{slogan:derive} and how it applies to term
|f|:
%
\sloganDerive*
%
Since |y| is free in |tf|, the value for |y| is an input of
|tf|. So, continuing our example, |dtf = derive(tf)| must map
a valid input change |dv| from |v1| to |v2| for variable |y| to
a valid output change |df| from |f1| to |f2|; more precisely, we must
have |df = eval(dtf) (y = v1, dy = dv)|.

\subsection{Consuming function changes}
Function changes can not only be produced but also be consumed in
programs obtained from |derive(param)|. We discuss next how.

As discussed, we consider the value for |y| as an input to |tf =
\x -> x + y|.
%
However, we also choose to consider the argument for |x| as an
input (of a different sort) to |tf = \x -> x + y|, and we require
our \cref{slogan:derive} to apply to input |x| too. While this
might sound surprising, it works out well.
Specifically,
since |df = eval(derive(tf))| is a change from |f1| to |f2|, we
require |df a1 da| to be a change from |f1 a1| to |f2 a2|, so
|df| maps base input |a1| and input change |da| to output change
|df a1 da|, satisfying the slogan.

More in general, any valid function change |df| from |f1| to |f2|
(where |f1, f2 : eval(sigma -> tau)|) must in turn be a function
that takes an input |a1| and a change |da|, valid from |a1|
to |a2|, to a valid change |df a1 da| from |f1 a1| to |f2 a2|.

This way, to satisfy our slogan on application |t = tf x|, we can
simply define |derive(param)| so that |derive(tf x) = derive(tf)
x dx|. Then
\[|eval(derive(tf x)) (y = v1, dy = dv, x = a1, dx =
  da) = eval(derive(tf)) a1 da = df a1 da|.\]
As required, that's a
change from |f1 a1| to |f2 a2|.

\pg{Maybe this is too steep now.}
Overall, valid function changes preserve validity, just like |derive(t)| in
\cref{slogan:derive}, and map valid input changes to valid output changes. In
turn, output changes can be function changes; since they are valid, they in turn
map valid changes to their inputs to valid output changes (as we'll see in
\cref{lem:validity-binary-functions}). We'll later formalize this and define
validity by recursion on types, that is, as a \emph{logical relation} (see
\cref{sec:validity-logical}).

\subsection{Differentiation and function changes}
According to our slogan, if term |t| is a closed unary functions, |derive t| map
input changes to output changes.
But our slogan extends beyond closed unary functions---|derive t| maps input
changes to output changes for arbitrary terms |t|. But in general we must
consider different sorts of inputs to |t|:
(a) Evaluating an open term takes an environment as input.
(b) Evaluating a closed function term gives a function that takes arguments as
inputs.
(c) Evaluating an open function term |t| takes both sorts of inputs: evaluating |t|
takes an environment, and the result takes in turn arguments.
(d) Evaluating a closed term that is not a function gives a value directly,
without taking any inputs.
In all those cases, |derive t| maps input changes to output changes. In general,
if |Gamma /- t : tau|, evaluating term |derive t| requires as input a
\emph{change environment} |drho| containing changes from the \emph{initial
environment} |rho1| to the \emph{updated environment} |rho2|.
The (environment) input change |drho| is mapped by |derive t| to output change
|dv = eval (derive t) drho|, a change from \emph{initial output} |eval t
rho1| to \emph{updated output} |eval t rho2|. If |t| is a function,
|dv| maps in turn changes to the function arguments to changes to the function result.

While the behavior of |derive t| might seem confusing, it parallels the behavior
of |t|, because |t| maps inputs to outputs just like |derive(t)| maps valid
input changes to valid output changes.

We formalize this guarantee as \cref{thm:derive-correct} in next chapter.



% x -> u
% y -> v
% z -> w

% Continuing our example, consider for instance term |t = tf z|,
% where |tf = \x -> x + y| like above. As discussed, |y| undergoes
% change |dv| from |v1| to |v2|, so |tf|'s value undergoes change
% |df| from |f1| to |f2|. Moreover, assume variable |z| undergoes
% change |dw| from |w1| to |w2|. Again, variables |y| and |z| are
% inputs to |t|, so by our slogan |derive(t)| needs to map their
% changes to a change from old |t|'s output |f1 w1| to new |t|'s
% output |f2 w2|.

% We require that a valid function change from |f1| to |f2| (where
% |f1, f2 : eval(sigma -> tau)|) is in turn a function |df| that
% takes an input |a1| and a change |da|, valid from |a1| to |a2|,
% to a valid change from |f1 a1| to |f2 a2|.

% Thanks to this invariant, we can define |derive(param)| so that
% |derive(t) = derive(tf) v dv|.

% Then, |eval(derive(t)) (y = y1, dy
% = dy, v = v1, dv = dv) = eval(derive(tf)) v1 dv|

%% We do so using a change
%% from |v1| to |v2| and a function change from |f1| to |f2| by
%% defining function changes suitably.
%
%%
%% We want to define |derive(param)| \emph{compositionally}. To this end,
%% we define function changes so that they enable computing the
%% change to their output from the change to their input.
%
%% To see why that's needed, consider term |t = f v|, where again |f
%% = \x -> x + y|.

\subsection{Pointwise function changes}
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

\subsection{Passing change targets}
It would be more symmetric to make function changes also take
updated input |a2|, that is, have |df a1 da a2| computes a change
from |f1 a1| to |f2 a2|. However, passing |a2| explicitly adds no
information: the value |a2| can be computed from |a1| and |da| as
|a1 `oplus` da|. Indeed, in various cases a function change can
compute its required output without actually computing |a1
`oplus` da|. Finally, since we expect the size of |a1| and |a2|
is asymptotically larger than |da|, actually computing |a2| could
be expensive.
Hence, we stick to our asymmetric form of function
changes.
% We will discuss other alternatives later in \cref{?}.
\pg{Discuss alternatives?}

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
\section{Differentiation, informally}
\label{sec:informal-derive}
Next, we define differentiation and explain informally why it
does what we want. We then give an example of how differentiation
applies to our example. A formal proof will follow soon in
\cref{sec:correct-derive}, justifying more formally why this
definition is correct, but we proceed more gently.

\begin{restatable}[Differentiation]{definition}{deriveDef}
  \label{def:derive}
Differentiation is the following term transformation:
\deriveDefCore
where |deriveConst(c)| defines differentiation on primitives and
is provided by language plugins (see \cref{sec:lang-plugins}),
and |dx| stands for a variable generated by prefixing |x|'s
name with |d|, so that |derive(y) = dy| and so on.%
\end{restatable}
If |t| contains occurrences of both (say) |x| and |dx|, capture issues arise in
|derive(t)|. We defer these issues to \cref{sec:derive-binding-issues}.

This transformation might seem deceptively simple. Indeed, pure
$\lambda$-calculus only handles binding and higher-order
functions, leaving ``real work'' to primitives. Similarly, our
transformation incrementalizes binding and higher-order
functions, leaving ``real work'' to derivatives of primitives.
However, our support of $\lambda$-calculus allows to \emph{glue}
primitives together. We'll discuss later how we add support to
various primitives and families of primitives.

Now we try to motivate the transformation informally. We claimed
that |derive(param)| must satisfy \cref{slogan:derive}, which reads
%
\sloganDerive*

Let's analyze the definition of |derive(param)| by case analysis
of input term |u|. In each case we assume that our slogan applies
to any subterms of |u|, and sketch why it applies to |u| itself.
\begin{itemize}
\item if |u = x|, by our slogan |derive(x)| must evaluate to the
  change of |x| when inputs change, so we set |derive(x) = dx|.
\item if |u = c|, we simply delegate differentiation to
  |deriveConst(c)|, which is defined by plugins. Since plugins
  can define arbitrary primitives, they need provide their
  derivatives.
\item if |u = \x -> t|, then |u| introduces a function. Assume for
  simplicity that |u| is a closed term. Then |derive(t)|
  evaluates to the change of the result of this function |u|,
  evaluated in a context binding |x| and its change |dx|. Then,
  because of how function changes are defined, the change of |u|
  is the change of output |t| as a function of the
  \emph{base input} |x| and its change |dx|, that is |derive(u) = \x
  dx -> derive(t)|.
\item if |u = s t|, then |s| is a function. Assume for
  simplicity that |u| is a closed term. Then |derive(s)|
  evaluates to the change of |s|, as a function of |derive(s)|'s
  base input and input change. So, we apply |derive(s)| to its
  actual base input |t| and actual input change |derive(t)|, and
  obtain |derive(s t) = derive(s) t (derive t)|.
\end{itemize}

This is not quite a correct proof sketch because of many issues,
but we fix these issues with our formal treatment in
\cref{sec:correct-derive}. In particular, in the case for
abstraction |u = \x -> t|, |derive(t)| depends not only on |x|
and |dx|, but also on other free variables of |u| and their
changes. Similarly, we must deal with free variables also in the
case for application |u = s t|. But first, we apply
differentiation to our earlier example.

\section{Differentiation on our example}
\label{sec:derive-example}
\label{sec:derive-example-merge}
\pg{This example is still a bit too complex as written; I'm
  skipping too many steps. Unless it comes after the basic
  formalism is established.}

To exemplify the behavior of differentiation concretely, and help
fix ideas for later discussion, in this section we show how the derivative of
|grand_total| looks like.

\begin{code}
grand_total  = \ xs ys -> sum (merge xs ys)
s            = grand_total {{1}} {{2, 3, 4}} = 11
\end{code}
Differentiation is a structurally recursive program transformation,
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
  `eq`      dmerge xs dxs ys dys
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
  `eq`      dsum (merge xs ys) (derive(merge xs ys))
  `betaeq`  sum (derive(merge xs ys))
  `eq`      sum (dmerge xs dxs ys dys)
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
  `eq`      \xs dxs ys dys -> derive(sum (merge xs ys))
  `betaeq`  \xs dxs ys dys -> sum (merge dxs dys)
\end{code}

Next we need to transform the binding of |grand_total2| to its body |b = \ xs ys -> sum (merge xs ys)|. We copy this binding and add a new additional binding from |dgrand_total2| to the derivative of |b|.

\begin{code}
grand_total   = \ xs      ys      ->  sum  (merge  xs   ys)
dgrand_total  = \ xs dxs  ys dys  ->  sum  (merge  dxs  dys)
\end{code}

Finally, we need to transform the binding of |output| and its body. By iterating similar steps,
in the end we get:
\begin{code}
grand_total   `eq`      \ xs      ys      ->  sum  (merge  xs   ys)
dgrand_total  `eq`      \ xs dxs  ys dys  ->  sum  (merge  dxs  dys)
s             `eq`      grand_total   {{1, 2, 3}}       {{4}}
ds            `eq`      dgrand_total  {{1, 2, 3}} {{1}} {{4}} {{5}}
              `betaeq`  sum (merge {{1}} {{5}})
\end{code}

\paragraph{Self-maintainability}
Differentiation does not always produce efficient derivatives
without further program transformations; in particular,
derivatives might need to recompute results produced by the base
program. In the above example, if we don't inline derivatives and
use $\beta$-reduction to simplify programs, |derive(sum (merge xs
ys))| is just |dsum (merge xs ys) (derive(merge xs ys))|. A
direct execution of this program will compute |merge xs ys|,
taking time linear in the base inputs.%
\pg{Point out this is self-maintainable!}

\section{Chapter conclusion}
\pg{TODO: add}
