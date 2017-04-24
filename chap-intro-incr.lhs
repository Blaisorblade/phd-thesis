% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Introduction to static differentiation}
\label{sec:intro}
\label{ch:static-diff-intro}

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
  Writing |df| by hand can be much more efficient than rerunning
  |f|, but it requires significant developer effort, is
  error-prone, and requires updating |df| to keep it consistent
  with |f|. This complicates code maintenance significantly in
  practice~\citep{Salvaneschi13reactive}.
\item They can write |f| using domain-specific languages that
  support incrementalization, for tasks where such languages are
  available. For instance, build scripts (our |f|) are written in
  domain-specific languages that support (coarse-grained)
  incremental builds. Database query languages also have often
  support for incrementalization. \pg{Mention here limits?}
\item They can attempt using general-purpose techniques for
  incrementalizing programs, such as \emph{self-adjusting
    computation} and variants such as Adapton. Self-adjusting
  computation applies to arbitrary purely functional programs and
  has been extended to imperative programs; however, it only
  guarantees efficient incrementalization when applied to base
  programs that are \emph{designed} for efficient
  incrementalization.
\end{itemize}

\pg{Continue discussing dependencies minimization and the
  relation with parallelism. Build scripts might be a good
  example.}

No approach guarantees automatic efficient incrementalization for
arbitrary programs. We propose instead to design functional
domain-specific languages (DSLs) with carefully designed
primitives, so that programs in such DSLs can be incrementalized
efficiently. To incrementalize such programs, we use a
transformation that we call \emph{differentiation}. We propose
functional DSLs, so that language primitive can be parameterized
over functions and hence highly flexible.\pg{why not
  defunctionalize/closure convert/...?}

\pg{actually argue for higher-order collection DSLs over relational databases}
\pg{not in source}\pg{rewrite}\pg{find source for argument}
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

We build our domain-specific functional languages based on
simply-typed $\lambda$-calculus (STLC), extended with
\emph{language plugins} to define the domain-specific parts, as
discussed in \cref{sec:intro-stlc}. We call our approach
\emph{ILC}.\footnote{Originally, this acronym stood for
  \emph{incremental lambda calculus}, an extension of
  $\lambda$-calculus with additional operations. Such extensions
  are no more needed, so we don't have any more an incremental
  lambda calculus per se, but the name stuck, redefined as
  \emph{incrementalizing lambda calculus}.} We discuss
inspiration for differentiation in
\cref{sec:generalize-fin-diff}. We show a motivating example for
our approach in \cref{sec:motiv-example}. We introduce informally
the concept of \emph{changes} as values in
\cref{sec:change-intro}, and introduce \emph{changes to
  functions} in \cref{sec:higher-order-intro}. We define
differentiation and motivate it informally in
\cref{sec:informal-derive}. We apply differentiation to our
motivating example in \cref{sec:derive-example}.
%
\pg{check later this TOC} In \cref{ch:derive-formally}, we
introduce a formal theory of changes, and we use it to formalize
differentiation and prove it correct.

% \section{Our object language: STLC}
% \label{sec:intro-stlc}

% We will define differentiation as a recursive program transformation on terms.
% To be able to define the transformation and state the invariant it satisfies, we
% need to first recall the object language we develop the transformation in.


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
spectacularly with DBToaster by
\citet{Koch10IQE} and \citet{Koch2016incremental}.

But it is not immediate how to generalize finite differencing
beyond groups. And many useful types do not form a group: for
instance, lists of integers don't form a group but only a monoid.
Moreover, it's hard to represent list changes simply through a
list: how do we specify which elements were inserted (and where),
which were removed and which were subjected to change themselves?

In ILC, we generalize the calculus of finite differences by
using distinct types for base values and changes, and adapting
the surrounding theory.

%format s1
%format s2
\section{A motivating example}
\label{sec:motiv-example}
In this section, we illustrate informally incrementalization on a
small example. We give a more precise presentation in
\cref{sec:correct-derive}.

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
destination of |dv|. We'll discuss examples of valid and invalid
changes in \cref{ex:valid-bag-int,ex:invalid-nat}. \pg{What about
  changes with multiple valid sources?}

We also introduce an operator |`oplus`| on values and changes: if
|dv| is a valid change from |v1| to |v2|, then |v1 `oplus` dv|
(read as ``|v1| updated by |dv|'') is guaranteed to return |v2|.
However, we later show that often |v1 `oplus` dv| can be defined
even if |dv| is not a valid change from |v1| to |v1 `oplus` dv|;
in fact, |`oplus`| is overloaded over types, and for each type
|tau| it has an overload of signature |tau -> Dt ^ tau -> tau|.

We also introduce operator |`ominus`|: given two values |v1, v2|
for the same type, |v2 `ominus` v1| is a valid change from |v1|
to |v2|.

Finally, we introduce change composition: if |dv1| is a valid
change from |v1| to |v2| and |dv2| is a valid change from |v2| to
|v3|, then |ocompose dv1 v1 dv2| is a valid change from |v1| to
|v3|. This operation will be useful later.

Definitions of these operations and concepts for a type form a
\emph{change structure}. We'll define change structures more
formally later.
\pg{Why show a change structure in Haskell terms?}
We already sketch, preliminarly, how a change structure
can be represented in Haskell terms: a change structure is
encoded as a \emph{type class} named |ChangeStruct t|, where change type
|Dt^tau| is defined as an associated type |Dt^t|, and operations
|`oplus`|, |`ominus`| and |`ocompose`| are defined as methods.
\begin{code}
class ChangeStruct t where
  type Dt t
  oplus :: t -> Dt t -> t
  ominus :: t -> t -> Dt t
  (`ocompose`) :: Dt t -> t -> Dt t -> Dt t
\end{code}
We'll come back to this definition and refine it,
describing the laws it satisfies, in \cref{sec:change-struct-tc}.

\begin{example}[Changes on integers and bags]
  \label{ex:valid-bag-int}
  \label{ex:chs-int}
 \pg{changes on bags?}
To show how incrementalization affects our example, we next
describe valid changes for integers and bags.
%
For now, a change
|das| to a bag |as1| simply contains all elements to be added to
the base bag |as1| to obtain the updated bag |as2| (we'll ignore
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
After introducing these notions, we describe how, in our
approach, we incrementalize our example program. We propose to compute
the output change |ds| from |s1| to |s2| by
calling a new function |dgrand_total|, the \emph{derivative} of
|grand_total| on base inputs and their respective changes. We can
then compute the updated output |s2| as the old s
|s1| updated by change |ds|. We have successfully
incrementalized our program |grand_total| if not only we get the
correct result for |s2|, but if we also get it faster than
by just calling |grand_total xs2 ys2|.

Below we give the derivative of |grand_total| and show our
approach gives the correct result in this example.

\begin{code}
  dgrand_total xs dxs ys dys  = sum (merge dxs dys)
  ds                          = dgrand_total xs1 dxs ys1 dys =
                              = sum {{1, 5}} = 6
  s2                          = s1 `oplus` ds = s1 + ds
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

\begin{restatable}[|derive(t)| maps input changes to output changes]{slogan}{sloganDerive}
  \label{slogan:derive}
Term |derive(t)| evaluates on base inputs and valid \emph{input changes} to a valid \emph{output change} from |t|
evaluated on old inputs to |t| evaluated on new inputs.
\end{restatable}

Notice |derive(t)|'s behavior parallels the behavior of |t|,
because |t| maps inputs to outputs just like |derive(t)| maps
input changes to output changes.

% What's more, we define |derive(param)| \emph{compositionally}:
% |derive(t)| is defined in terms of |derive(param)| applied to
% subterms of |t|.

In our example, we have applied |derive(param)| to
|grand_total|'s body, and simplify the result via
$\beta$-reduction to produce |dgrand_total|'s body.
%
Correctness of |derive(param)| guarantees
that |sum (merge dxs dys)| evaluates to a change from
|sum (merge xs ys)| evaluated on old inputs |xs1, ys1| to
|sum (merge xs ys)| evaluated on new inputs |xs2, ys2|.

Here, a derivative of |grand_total| is a function in the same language as
|grand_total|, that accepts changes from initial inputs |xs1| and |ys1| to
updated inputs |xs2| and |ys2| and evaluates to the change from the base result
|grand_total xs1 ys1| to the updated result |grand_total xs2 ys2|.

More in general, for a unary function |f|, a derivative |df|
takes an input |a| and a change |da| for |a| and produces a
change from base output |f a| to updated output |f (a `oplus`
da)|. Symbolically we write
%   \label{eq:correctness}
\begin{equation}
  \label{eq:derivative-requirement}
  |f (a `oplus` da) `cong` f a `oplus` df a da|
\end{equation}
where we use |`cong`| to mean denotational equality (that is, |t1
`cong` t2| if and only if |eval(t1) = eval(t2)|).

We claim that differentiation produces derivatives. Hence, we can
take \cref{eq:derivative-requirement}, replace |df| by
|derive(f)|, and obtain as a corollary the following equation:
\begin{equation}
  \label{eq:correctness}
  |f (a `oplus` da) `cong` (f a) `oplus` (derive(f) a da)|
\end{equation}

For functions |f| of multiple arguments, a derivative |df| takes
all base inputs of |f| together with changes to each of them, and
produces a change from the base output to the updated output. We
will make this more formal in next section.

In this section, we have sketched the meaning of differentiation
informally. Next, we discuss incrementalization on higher-order
terms in \cref{sec:higher-order-intro}, before defining
differentiation in \cref{sec:correct-derive}.

%format y1
%format y2
%format tf = "t_f"
%format dtf = "\Varid{dt}_f"
\section{Function changes}
\label{sec:higher-order-intro}
\subsection{Producing function changes}
A first-class function can close over free variables that can
change, hence functions values can change themselves; hence, we
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
We describe this output difference through a function change |df|
from |f1| to |f2|.

Consider again \cref{slogan:derive} and how it applies to term
|f|:
%
\sloganDerive*
%
Since |y| is free in |tf|, |y| is an input of
|tf|. So, continuing our example, |dtf = derive(tf)| must map
from an input change |dv| from |v1| to |v2| for variable |y| to
an output change |df| from |f1| to |f2|; more precisely, we must
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

\subsubsection{Pointwise changes}
% We can also describe the difference from function |f| to function
% |f `oplus` df| as |nabla^f = \x -> f2 x `ominus` f1 x|.
\pg{Our definition of function change might seem to defy intuitions. In particular, pointwise changes might appear more intuitive. We discuss them later, too.}

We can also decompose function changes into orthogonal (and
possibly easier to understand) concepts.

The difference between |f2 a2| and |f1 a1| is due to changes to
both the function and its argument. We can compute the whole
change at once via a function change |df| as |df a1 da|. Or we
can compute separately the effects of the function change and of
the argument change. We can account for changes from |a1| to |a2|
using $f'$, a derivative of |f|: |f' a1 da = f (a1 `oplus` da)
`ominus` f a1|.\footnote{We're hiding some details here for
  simplicity; they are clarified in
  \cref{sec:change-equivalence}.}

We can account for changes from |f1| to |f2| using the
\emph{pointwise difference} of two functions, |nabla ^ f1 = \a ->
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
\begin{code}
   df a1 da
=  ocompose (f' a1 da) (f a1) (nabla ^ f (a1 `oplus` da))
\end{code}

One can also compute a pointwise change from a function change:
\begin{code}
  nabla f a = df a (nil a)
\end{code}

While some might find pointwise changes a more natural concept,
we find it easier to use our definitions of function changes,
which combines both pointwise changes and derivatives into a
single concept.

\subsubsection{Passing change targets}
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
applies to our example. A short formal proof will follow soon in
\cref{sec:correct-derive}, justifying more formally why this
definition is correct, but we proceed more gently.

We define differentiation as the following term transformation:
\begin{align*}
  |derive(\x -> t)| &= |\x dx -> derive(t)| \\
  |derive(s t)| &= |derive(s) t (derive(t))| \\
  |derive(x)| &= |dx| \\
  |derive(c)| &= |deriveConst(c)|
\end{align*}
where |deriveConst(c)| defines differentiation on primitives and
is provided by language plugins (see \cref{sec:lang-plugins}).
% \begin{code}
%   derive(\x -> t)   = \x dx -> derive(t)
%   derive(s t)       = derive(s) t (derive(t))
%   derive(x)         = dx
%   derive(c)         = deriveConst(c)
% \end{code}

Above, |dx| stands for a variable generated by prefixing |x|'s
name with |d|, so that |derive(y) = dy| and so on.

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
  is the change of |t| abstracted into a function of the
  \emph{base input} |x| and its change |dx|, so |derive(u) = \x
  dx -> derive(t)|.
\item if |u = s t|, then |s| is a function. Assume for
  simplicity that |u| is a closed term. Then |derive(s)|
  evaluates to the change of |s|, as a function of |derive(s)|'s
  base input and input change. So, we apply |derive(s)| to its
  actual base input |t| and actual input change |derive(t)|, and
  obtain |derive(s t) = derive(s) t derive(t)|.
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
in the end we get:
\begin{code}
grand_total   = \ xs      ys      ->  sum  (merge  xs   ys)
dgrand_total  = \ xs dxs  ys dys  ->  sum  (merge  dxs  dys)
s             = grand_total   {{1, 2, 3}}       {{4}}
ds            = dgrand_total  {{1, 2, 3}} {{1}} {{4}} {{5}}
               `betaeq` sum (merge {{1}} {{5}})
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

\section{A higher-order example}
\label{sec:differentiation-fold-example}
\pg{write}
% Referenced later in sec-performance.tex by saying:
% % We have seen in \cref{ssec:differentiation} that $\Derivative$
% % needlessly recomputes $\Merge\Xs\Ys$. However, the result is a
% % base input to $\FOLD'$.

\section{Nontermination}
\label{sec:non-termination}
\pg{write, and put somewhere}
