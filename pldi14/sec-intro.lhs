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
  incrementalization when applied to base programs that
  are \emph{designed} for efficient incrementalization.
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
simply-typed $\lambda$-calculus (STLC), extended with
\emph{language plugins} to define the domain-specific parts, as
discussed in \cref{sec:intro-stlc}. We show a motivating example
for our approach in \cref{sec:motiv-example}. We define
differentiation and motivate it informally in
\cref{sec:informal-derive}, apply it to our motivating example in
\cref{sec:derive-example}. Finally, in next chapter, we state and prove its
correctness theorem in \cref{sec:correct-derive}.

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
Our theory generalizes an existing field of mathematics called
the \emph{calculus of finite difference}: If |f| is a real
function, one can define its \emph{finite difference}, that is a
function |f_d| such that |f_d a da = f (a + da) - f a|. Readers
might notice the similarity (and the differences) between the
finite difference and the derivative of |f|, since the latter is
defined as $f'(a) = \lim_{da \to 0} (f (a + da) - f(a)) / da$.

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

In the following program, term |grand_total xs ys| sums integer numbers in
input collections |xs| and |ys|. We also compute an initial
output |output1| on initial inputs |xs1| and |ys1|:

\begin{code}
  grand_total        :: Bag Int -> Bag Int -> Int
  output1            :: Int

  grand_total xs ys  = sum (merge xs ys)
  output1            = grand_total xs1 ys1
                     = sum {{1, 2, 3, 4}} = 10
\end{code}

We have called |grand_total| on initial inputs |xs1 = {{1, 2,
    3}}| and |ys1 = {{4}}| to obtain initial output |output1|.
Here, double braces |{{...}}| denote a multiset or \emph{bag},
containing the elements among the double braces. A bag is an
unordered collection (like a set) where elements are allowed to
appear more than once (unlike a set). In this example, we assume
a language plugin that supports a base type of integers |Int| and
a family of base types of bags |Bag tau| for any type
|tau|.\footnote{Using |Bag tau|, a type of bags of elements of
  some \emph{type} rather than |Bag iota|, a type of bags of
  elements of some \emph{primitive type}, runs into technical
  problems during proof mechanization
  (see~\cref{sec:modularity-limits}), though those problems do
  not affect our main conclusions.}

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

\section{Introducing changes}
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
To each type |tau| we associate a type of changes or \emph{change type}
|Dt^tau|: a change between |v1| and |v2| must be a value of type |Dt^tau|.

Not all descriptions of changes are meaningful,
so we also talk about \emph{valid} changes.
%
A change value |dv| can be a valid change from |v1| to |v2|. We also
call |v1| the source of |dv| and |v2| the destination of |dv|.

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
\emph{change structure}. We'll define change structures properly
later. We already sketch, preliminarly, how a change structure
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

 \pg{changes on bags?}
To show how incrementalization affects our example, we next
describe valid changes for bags and integers. For now, a change
|das| to a bag |as1| simply contains all elements to be added to
the base bag |as1| to obtain the updated bag |as2| (we'll ignore
removing elements for this section and discuss it later). In our
example, the change from |xs1| (that is |{{1, 2, 3}}|) to |xs2|
(that is |{{1, 1, 2, 3}}|) is |dxs = {{1}}|, while the change
from |ys1| (that is |{{4}}|) to |ys2| (that is |{{4, 5}}|) is
|dys = {{5}}|. To represent the output change |doutput| from
|output1| to |output2| we need integer changes. For now, we
represent integer changes as integers, and define |`oplus`| on
integers as addition: |v1 `oplus` dv = v1 + dv|.

For both bags and integers, a change |dv| is always valid between
|v1| and |v2 = v1 `oplus` dv|; for other changes, however,
validity will be more restrictive. For instance, say we want to
define changes on a type of natural numbers, and we still want to
have |v1 `oplus` dv = v1 + dv|. A change from |3| to |2| should
still be |-1|, so the type of changes must be |Int|. But the
result of |`oplus`| should still be a natural, that is an integer
|>= 0|: to ensure that |v1 `oplus` dv >= 0| we need to require
that |dv >= -v1|. We use this requirement to define validity on
naturals: |fromto v1 dv (v1 + dv)| is defined as equivalent to
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

\subsection{Incrementalizing with changes}
After introducing these notions, we describe how, in our
approach, we incrementalize our example program. We propose to compute
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
|derive(t)| evaluates on base inputs and valid inputs changes to a valid change from |t|
evaluated on old inputs to |t| evaluated on new inputs.
\end{slogan}

In our example, we can apply |derive(param)| to |grand_total|'s
body to produce |dgrand_total|'s body. After simplifying the
result via $\beta$-reduction, we get
\[ |derive(sum (merge xs ys)) `betaeq` sum (merge dxs dys)|.\]
%
Correctness of |derive(param)| guarantees
that |sum (merge dxs dys)| evaluates to a change from
|sum (merge xs ys)| evaluated on old inputs |xs1, ys1| to
|sum (merge xs ys)| evaluated on new inputs |xs2, ys2|.

Here,
a derivative of |grand_total| is a function in the same language as
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

For functions |f| of multiple arguments, a derivative |df| takes
all base inputs of |f| together with changes to each of them, and
produces a change from the base output to the updated output. We
will make this more formal in next section.

In this section, we have sketched the meaning of differentiation
informally. Next, we discuss incrementalization on higher-order
terms in \cref{sec:higher-order-intro}, before defining
differentiation in \cref{sec:correct-derive}.

\section{Function changes}
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
changes.% We will discuss other alternatives later in \cref{?}.
\pg{Discuss alternatives?}
\pg{Our definition of function change might seem to defy intuitions. In particular, pointwise changes might appear more intuitive. We discuss them later, too.}
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

Now we try to motivate the transformation informally.
As we claimed earlier, |derive(param)| must satisfy the following
slogan:
\begin{slogan}
|derive(t)| evaluates on base inputs and valid inputs changes to a valid change from |t|
evaluated on old inputs to |t| evaluated on new inputs.
\end{slogan}

Let's analyzes each case of the definition of |derive(u)|. In
each case we assume that our slogan applies to any subterms of
|u| and show it applies to |u| itself.
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
\pg{This example is still a bit too complex as written; I'm
  skipping too many steps. Unless it comes after the basic
  formalism is established.}

To exemplify the behavior of differentiation concretely, and help
fix ideas for later discussion, in this section we show how the derivative of
|grand_total| looks like.

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
in the end we get:
\begin{code}
grand_total   = \ xs      ys      ->  sum  (merge  xs   ys)
dgrand_total  = \ xs dxs  ys dys  ->  sum  (merge  dxs  dys)
output         = grand_total   {{1, 2, 3}}       {{4}}
doutput        = dgrand_total  {{1, 2, 3}} {{1}} {{4}} {{5}}
               `betaeq` sum (merge {{1}} {{5}})
\end{code}

As expected,

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

\chapter{Differentiation and changes, formally}
\section{Differentiation and its meaning}
\label{sec:correct-derive}

In this chapter, we make our previous discussion precise: we
introduce differentiation and state and prove its correctness. We
also elaborate on its effect on higher-order programs.

To support incrementalization, we also motivate and introduce in
this section (a) a description of changes and operations on
changes; (b) a definition of which changes are valid; (c) a
compositional term-to-term transformation called differentiation
and written |derive(t)| that produces incremental programs. We
have already mentioned the different concepts and how they fit
together. We next explain definitions and key facts about them. We
collect the complete definitions and crucial facts in
\cref{fig:differentiation}.
These definitions must be extended for base types and constants
provided by the language plugin.

First, for each type |tau| and values |v1| and |v2| of type
|tau|, we define when |dv| is a valid change from |v1| to |v2|.
We define valid changes in two steps: we (a) define a type
|Dt^tau| of changes, that we call \emph{change type}, and (b)
define a relation that picks valid changes out of all elements of
change types. Both definitions are delegated to plugins on base
types. In a moment, we explain the definitions we give on
function types.

\begin{definition}[Change types]
  The change type |Dt^tau| of a type |tau| is defined in
  \cref{fig:change-types}.
\end{definition}
\begin{restatable}[Base change types]{requirement}{baseChangeTypes}
  \label{req:base-change-types}
  To each base type |iota| is associated a change type |Dt^iota|.
\end{restatable}
We refer to values of change types as \emph{change values}.

Then, we define \emph{validity} as a family of ternary relations,
indexed by types and relating changes with their sources and
destinations.
\begin{definition}
We say that |dv| is valid change from |v1| to |v2|, and write
|fromto tau v1 dv v2|, if |dv : eval(Dt^tau)|, |v1, v2 :
eval(tau)| and |dv| is a ``valid'' description of the difference
from |v1| to |v2|, as we define in \cref{fig:validity}.
\end{definition}
The definition of validity for base types is delegated to language plugins, so we state a
\begin{restatable}[Base validity definitions]{requirement}{baseValidity}
  \label{req:base-validity}
  To each base type |iota| is associated a definition of validity for |iota|.
\end{restatable}
We mentioned informally in \cref{sec:motiv-example} how validity is
defined, for instance, on integers and bags.\pg{revise if we add more examples.}

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

To state correctness of |derive(param)|
(\cref{thm:correct-derive}), we define when a change term is a
\emph{correct change} for a base term. We say a term |dt| is a
correct change for term |t| (at type |tau|), and write
|correct(tau) dt t|, if there exists a context |Gamma| such that
|Gamma /- t : tau|, |Dt ^ Gamma /- dt : Dt^tau|, and |eval(dt)
drho| is a valid change from |eval(t) rho1| to |eval(t) rho2|
whenever |fromto Gamma rho1 drho rho2|. In other words,
|eval(dt)| must be a function that takes changes |drho| from old
to new inputs of |t|, and maps them to changes from old to new
outputs of |t|.

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
\begin{restatable}[|`oplus`| agrees with validity]{lemma}{validOplus}
  \label{thm:valid-oplus}
  If |fromto tau v1 dv v2| then |v1 `oplus` dv = v2|.
\end{restatable}

And we can deduce that updating base result |eval(t) rho1| by
change |eval(derive(t)) drho| via |`oplus`| gives the updated
result |eval(t) rho2|.
\begin{restatable}[Correctness of |derive(param)|, corollary]{corollary}{deriveCorrectOplus}
  \label{thm:correct-derive-oplus}
  If |Gamma /- t : tau| and |fromto Gamma rho1 drho rho2| then
  |eval(t) rho1 `oplus` eval(derive(t)) drho = eval(t) rho2|.
\end{restatable}
For didactic reasons we anticipate the proof of this corollary:
\begin{proof}
  First, differentiation is correct (\cref{thm:correct-derive}), so under the hypotheses
  \[|fromto tau (eval(t) rho1) (eval(derive(t)) drho) (eval(t) rho2)|;\]
  that judgement implies the thesis \[|eval(t) rho1 `oplus` eval(derive(t)) drho = eval(t) rho2|\]
  because |`oplus`| agrees with validty (\cref{thm:valid-oplus}).
\end{proof}
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
\begin{align*}
  |derive(\x -> t)| &= |\x dx -> derive(t)| \\
  |derive(s t)| &= |derive(s) t (derive(t))| \\
  |derive(x)| &= |dx| \\
  |derive(c)| &= |deriveConst(c)|
\end{align*}
Transformation |deriveConst(c)| must be defined by language
plugins (as stated in \cref{req:const-differentiation}).
  % derive(^^let x = t1 in t2) =
  %   let  x = t1
  %        dx = derive(t1)
  %        in   derive(t2)



Now we can characterize |derive(param)|'s static semantics:
\deriveTyping*
\begin{proof}
  The thesis can be proven by induction on the typing derivation
  |Gamma /- t : tau|. The case for constants is delegated to plugins in
  \cref{req:const-differentiation}.
\end{proof}
\begin{restatable}[Differentiation on constants]{requirement}{constDifferentiation}
  \label{req:const-differentiation}
  For each constant |c|, if $\ConstTyping{c}{\tau}$, then
  |deriveConst(c)| is defined and satisfies |/- deriveConst(c) :
  Dt^tau|.
\end{restatable}

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

Next, we state the proof obligation that the theorem imposes on
language plugins:

\begin{restatable}[Correctness of |deriveConst(param)|]{requirement}{deriveConstCorrect}
  \label{req:correct-derive-const}
  If |/- c : tau| then |deriveConst(c)| is a correct change for
  |c|. That is, if |/- c : tau| then |fromto tau (evalConst c)
  (eval(deriveConst(c)) emptyRho) (evalConst c)|.
\end{restatable}

\subsection{Discussion}
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

\subsection{Binding issues}
\label{sec:derive-binding-issues}
Differentiation generates new names, so a correct implementation
must make sure to prevent accidental capture, but our previous
discussion ignored the problem. Our formalization has no capture
issues as it uses deBrujin indexes, and change context just
alternates variables for base inputs and input changes. A context
such as |Gamma = x : Int, y : Bool| is encoded as |Gamma = Int,
Bool|; its change context is |Dt^Gamma = Int, Dt^Int, Bool,
Dt^Bool|. This solution is correct and robust, and is the one we
rely on; we use names in this thesis only to simplify
presentation.
%

In this subsection we discuss issues in implementing this
transformation with names rather than deBrujin indexes. Unlike
the rest of this chapter, we keep this discussion informal, also
because we have not mechanized any definitions using names (as it
may be possible using nominal logic). The rest of the thesis does
not depend on this material, so readers might want to skip to
next section.

Using names introduces the risk of capture, as it is common for
name-generating
transformations~\citep{Erdweg2014captureavoiding}. For instance,
differentiating term |t = \x -> f dx|, gives |derive(t) = \x dx
-> df dx ddx|. Here variable |dx| represents a base input and is
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
  |derive(\x -> t, m)| &= |\x n -> derive(t, (m[x -> n]))| \\
  |derive(s t, m)| &= |derive(s, m) t (derive(t, m))| \\
  |derive(x, m)| &= |m^(x)| \\
  |derive(c, m)| &= |deriveConst(c)|
\end{align*}
where |m^(x)| represents lookup of |x| in map |m|,
|n| is a fresh variable that does not appear in |t|,
and |m[x -> n]| extend |m| with a new mapping from |x| to |n|.

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
  We have not proved this solution is correct, just like the
  previous one, but this time it appears intuitively obvious that
  \textsc{Derive'} holds and that |derive(t, m)| is correct.
\end{itemize}

\section{Operations on changes}
In the previous section, we have shown that evaluating the result
of differentiation produces a valid change |dv| from the old
output |v1| to the new one |v2|. We also want a way to
\emph{compute} |v2| from |v1| and |dv|, that is, we want to
\emph{define} the operator |`oplus`| that we have talked so much
about.

Moreover, it is not yet clear concretely how plugins should
define differentiation on primitives. To write derivatives on
primitives, we will need operations on changes, such as
|`oplus`|, |`ominus`|, |`ocompose`| and |nilc|, and
guarantees on their behavior. Guarantees on the behavior of
change operations will be needed to prove that programs using
change operations behave as specified. In particular, such
guarantees are required to prove that the derivatives of some
primitives are correct.

Hence, we continue exploring how changes behave, and introduce
operations (including |`oplus`|) that manipulate them. We will
define these operations both at the semantic level to operate on
change values, and on the syntactic level to use in object
programs, such as derivatives of primitives. While often the same
definitions are applicable, additional performance concerns apply
to object-level implementations.

We will summarize this section in \cref{fig:change-structures};
readers might want to jump there for the definitions. However, we
first build up to those definitions.

\subsection{Basic change structures}
First, we generalize the concept of changes. For each type |tau|
we have defined notions of change type and of valid changes; but
these notions can be defined for arbitrary sets.

\begin{definition}
  A basic change structure for set |V| is given by defining:
  \begin{subdefinition}
  \item a change set |Dt^V|
  \item a ternary relation called validity among |V|, |Dt^V| and
    |V|. If |v1, v2 `elem` V| and |dv `elem` DV|, and this relation holds, we write
    |fromto V v1 dv v2| and say that |dv| is a valid change from |v1| to |v2|.
  \end{subdefinition}
\end{definition}

We have already given the ingredients to define two families of basic change structures,
a family for types and one for contexts:
\begin{definition}
  To each type |tau| we associate a basic change structure for
  set |eval(tau)|; we do so by taking |eval(Dt^tau)| as change
  set and by reusing validity as previously defined. We keep
  writing |fromto tau v1 dv v2| rather than |fromto (eval(tau)) v1 dv v2|.
\end{definition}
\begin{definition}
  To each environment |Gamma| we associate a basic change
  structure for set |eval(Gamma)|; we do so by taking
  |eval(Dt^Gamma)| as change set and by reusing validity as
  previously defined. We keep writing |fromto Gamma rho1 drho rho2|
  rather than |fromto (eval(Gamma)) rho1 drho rho2|.
\end{definition}
Moreover, we required that language plugins must define change
types and validity for base types
(\cref{req:base-change-types,req:base-validity}). Equivalently we
can require that plugins define basic change structures on all
base types:
\begin{restatable}[Basic change structures on base
  types]{requirement}{baseBasicChangeStructures}
  \label{req:base-basic-change-structures}
  To each base type |iota| is associated a basic change structure
  for |eval(iota)|.
\end{restatable}

Basic change structures generalize validity and change sets, so
we can talk about a change set |Dt^V| for an arbitrary set |V|,
not just for the semantics of a type (|V = eval(tau)|) or the
semantics of a context (|V = eval(Gamma)|).
%
In particular, we can define a basic change structure for any
function space |A -> B| as long as we have basic change
structures for |A| and |B|.
\begin{definition}
  \label{def:basic-change-structure-funs}
  We define a basic change structure on |A -> B| whenever |A, B|
  are sets and we have a basic change structure for each of them.
  \begin{subdefinition}
  \item we define the change set |Dt^(A -> B)| as |A -> Dt^A -> Dt^B|.
  \item we define that |df| is a valid function change from |f1|
    to |f2| (that is, |fromto (A -> B) f1 df f2|) if and only if,
    for any inputs |a1, a2 : A|, input change |da : Dt^a| that is
    valid from |a1| to |a2| (|fromto A a1 da a2|), we have
    |fromto B (f1 a1) (df a1 da) (f2 a2)|.
  \end{subdefinition}
\end{definition}

In particular, we obtain a basic change structure on |eval(Gamma)
-> eval(tau)| for any |Gamma, tau|. After a new definition, we
can restate correctness of differentiation using this new basic
change structure.

\begin{definition}[Incremental semantics]
  \label{def:inc-semantics}
  We define the \emph{incremental semantics} of a well-typed term
  |Gamma /- t : tau| in terms of differentiation as:
  \[|evalInc t = (\rho1 drho -> eval(derive t) drho) : eval(Gamma)
    -> eval(Dt^Gamma) -> eval(Dt^tau)|.\]
\end{definition}

The incremental semantics of a term |evalInc t| is a function
change for |eval t|.
The definition of incremental semantics might seem surprising,
because function change |\rho1 drho -> eval(derive(t)) drho|
appears to ignore the argument for |rho1|. But this is just an
artifact: If you take a valid change |drho| from |rho1| to
|rho2|, then |drho| extends |rho1|, so we can safely ignore
|rho1|.

\begin{theorem}[|evalInc t| is a valid change from |eval t| to |eval t|]
  \label{thm:correct-derive-2}
  If |Gamma /- t : tau|, then |evalInc(t)| is a valid change from
  |eval t| to |eval t|:
  \[
    |fromto (eval Gamma -> eval tau) (eval t) (evalInc t) (eval t)|
  \]
\end{theorem}

\begin{proof}
  By expanding \cref{def:basic-change-structure-funs,def:inc-semantics}
  one can verify this is just a restatement of \cref{thm:correct-derive}.
\end{proof}

The notion of basic change structure is somewhat weak, since we
place no constraints on validity, but we are going to build on it
a more interesting notion of \emph{change structure}, which adds
operations including |`oplus`| and requirements on them.

As anticipated, we use changes to generalize the calculus of
finite differences from groups (see
\cref{sec:generalize-fin-diff}). We'll later see how change
structures generalize groups.

Moreover, now that we defined basic change structures, we can
already talk about a set |S| with different basic change
structures defined on it, and about ways to create basic change
structures.

For instance, for any set |V| we can talk about \emph{replacement
  changes} on |V|: a replacement change |dv = !u| for a value |v
: V| simply specifies directly a new value |u : V|, so that
|fromto V v (! u) u|. We read |!| as the ``bang'' operator. A
basic change structure can decide to use only replacement changes
(which might be appropriate for primitive types with values of
constant size), or to make |Dt^V| a sum type allowing both
replacement changes and other ways to describe a change (as long
as we're using a language plugin that adds sum types).

But before defining |`oplus`|, we need to introduce a few more
concepts, as we do next.

% including |`oplus`|
% but also |nilc| and |`ominus`| and

\subsection{Nil changes}
\label{sec:nil-changes-intro}
Some valid changes have the same value |v| both as source and as
destination. They are \emph{nil changes}:
\begin{definition}[Nil changes]
  A change |dv : Dt^V| is a \emph{nil change} for a value |v : V|
  if it is a valid change from |v| to itself: |fromto V v dv v|.
\end{definition}

For instance, |0| is a nil change for any integer number |n|.
However, in general a change might be nil for an element but not
for another. For instance, the replacement change |!6| is a nil
change on |6| but not on |5|.

When we define change structures, each element is going to be
associated to at least one nil change, as we're going to show later:
\begin{restatable}[Existence of nil changes]{lemma}{nilChangesExist}
  \label{lem:nilChangesExist}
  Given a change structure for |V|, to each element |v
  `elem` V| is associated a distinguished nil change that we
  denote by |nil v|.
\end{restatable}

Moreover, nil changes are a right identity element for |`oplus`|:
\begin{restatable}[Nil changes are identity elements]{corollary}{nilChangesRightId}
  \label{lem:nilChangesRightId}
  Any nil change |dv| for a value |v| is a right identity element for
  |`oplus`|, that is we have |v `oplus` dv = v| for every set |V|
  with a basic change structure, every element |v `elem` V| and
  every nil change |dv| for |v|.
\end{restatable}
\begin{proof}
  This follows from \cref{thm:valid-oplus} and the definition of
  nil changes.
\end{proof}
The converse of this theorem does not hold: there exists changes
|dv| such that |v `oplus` dv = v| yet |dv| is not a valid change
from |v| to |v|. For instance, under earlier definitions for
changes on naturals, if we take |v = 0| and |dv = -5|, we have |v
`oplus` dv = v| even though |dv| is not valid; examples of
invalid changes on functions are discussed at \cref{sec:invalid}.
However, we prefer to define ``|dv| is a nil change'' as we do,
to imply that |dv| is valid, not just a neutral element.

We can already show some values have nil changes even though we
haven't proved \cref{lem:nilChangesExist}.
\begin{examples}
  \begin{itemize}
  \item
An environment change for an empty environment |emptyRho :
eval(emptyCtx)| must be an environment for the empty context
|Dt^emptyCtx = emptyCtx|, so it must be the empty environment! In
other words, if and only if |fromto emptyCtx emptyRho drho
emptyRho|, then and only then |drho = emptyRho| and, in
particular, |drho| is a nil change.

\item If all values in an environment |rho| have nil changes,
the environment has a nil change |drho = nil(rho)| associating
each value to a nil change. Indeed, take a context |Gamma| and a
suitable environment |rho : eval(Gamma)|. For each typing
assumption |x : tau| in |Gamma|, assume we have a nil change |nil
v| for |v|. Then we define |nil rho : eval(Dt^Gamma)| by
structural recursion on |rho| as:
\begin{code}
  nil emptyRho = emptyRho
  nil (rho, x = v) = nil rho, x = v, dx = nil v
\end{code}
Then we can see that |nil rho| is indeed a nil change for |rho|,
that is, |fromto Gamma rho (nil rho) rho|.
\item We have seen in \cref{thm:correct-derive-2} that, whenever
  |Gamma /- t : tau|, |eval t| has nil change |evalInc t|.
  Moreover, if we have an appropriate nil environment change
  |fromto Gamma rho drho rho| (which we often do, as discussed
  above), then we also get a nil change |evalInc t rho drho| for
  |eval t rho|:
\[|fromto tau (eval t
  rho) (evalInc t rho drho) (eval t rho)|.\]
In particular, for all closed well-typed terms |/- t : tau| we have
\[|fromto tau (eval t
emptyRho) (evalInc t emptyRho emptyRho) (eval t emptyRho)|.\]
\end{itemize}
\end{examples}

\subsection{Nil changes on arbitrary functions}
\label{sec:nil-changes-fun-intro}
Not all functions |f : A -> B| arise as the semantics of some
term. We discuss next how to compute |nil f| anyway. Technically,
we are given an arbitrary metalanguage function |f : A -> B|,
where |A| and |B| are arbitrary sets; we assume a basic change
structure on |A -> B|, and want to find a nil change for |f|. As
discussed, if |f| is the semantics of a closed term |t| (|f =
eval(t) emptyRho|), the nil change for |f| is |df =
eval(derive(f)) emptyRho|. But in general we cannot inspect the
STLC code for |f| (which might not exist), only test its behavior
by applying it to arguments---we only know |f| extensionally, not
intensionally. Yet, by defining a few further operations, we can
still define a nil change for |f|.

We see |nil f| such that |fromto (A -> B) f (nil f) f|. That is,
whenever |fromto A a1 da a2| then |fromto B (f1 a1) (nil f a1 da)
(f2 a2)|. By \cref{thm:valid-oplus}, this means that we need to
find |nil f| such that |f1 a1 `oplus` nil f a1 da = f2 a2|, where
|a1 `oplus` da = a2|. To solve this equation, we \emph{introduce
operator |`ominus`|}, such that |a2 `ominus` a1| produces a valid
change from |a1| to |a2|, and see that |nil f| must be

\[|nil f = \a1 da -> f (a1 `oplus` da) `ominus` f a1|.\]

Definitions of |`ominus`| will be provided as part of change
structures. In particular, we define |`ominus`| on functions. And
once we define |`ominus`|, we can also define |nil v = v `ominus`
v|.
Since |f2 `ominus` f1| must produce a valid function change,
by generalizing the reasoning we just did, we obtain that
whenever |fromto A a1 da a2| then we need to have |fromto B (f1
a1) ((f2 `ominus` f1) a1 da) (f2 a2)|, and can define

\begin{equation}
  \label{eq:ominus-fun-1}
|f2 `ominus` f1 = \a1 da -> f2 (a1 `oplus` da) `ominus` f1 a1|.
\end{equation}

We have made this definition at the meta-level. We can also use
the same definition in object programs, but there we face
additional concerns. The produced function change is rather slow,
because it recomputes the old output |f1 a1|, while also computes
the new output |f2 a2| and taking the difference.

However, we can implement `ominus` using replacement changes, if
they are supported on the relevant types. If we define |`ominus`|
on set |B| as |b2 `ominus` b1 = !b2|, then \cref{eq:ominus-fun-1}
simplifies to
\[|f2 `ominus` f1 = \a1 da -> ! (f2 (a1 `oplus` da))|.\]

We could even imagine allowing replacement changes on functions
themselves. However, here the bang operator needs to be defined
to produce a function change that can be applied, hence
\[|!f2 = \a1 da -> ! (f2 (a1 `oplus` da))|.\]

Alternatively, as we'll see later in
\cref{ch:defunc-fun-changes}, we could represent function changes
not as functions but as data through \emph{defunctionalization},
and provide a function applying function changes |df : Dt^(sigma
-> tau)| to inputs |t1 : sigma| and |dt :
Dt^sigma|.\pg{reconsider}

\subsection{Constraining ⊕ on functions}
\label{sec:oplus-fun-intro}
Next, we discuss how |`oplus`| must be defined on functions, and
show informally why we must define |f1 `oplus` df = \v -> f1 x
`oplus` df v (nil v)| to prove that |`oplus`| on functions agrees
with validity (\cref{thm:valid-oplus}).

% Take functions
% |f1 `oplus` df|
% Take a value |v|.
% Assume there exists a valid nil change for |v|, and
% write it |nil v| (see \cref{lem:nilChangesExist}).

We know that a valid function change |fromto (sigma -> tau) df f1
f2| takes valid input changes |fromto sigma dv v1 v2| to a valid
output change |fromto tau (df v1 dv) (f1 v1) (f2 v2)|. We require
that |`oplus`| agrees with validity (\cref{thm:valid-oplus}), so
|f2 = f1 `oplus` df|, |v2 = v1 `oplus` dv| and
%
\[|f2 v2 = (f1 `oplus` df) (v1 `oplus` dv) = f1 v1 `oplus` df v1
  dv|.\]
%
Instantiating |dv| with |nil v| gives equation
%
\[|(f1 `oplus` df) v1 = f1 v1 `oplus` df v1 (nil v)|,\]
%
which is not only a requirement on |`oplus`| for functions but
also defines |`oplus`| effectively.

It also follows that
\[
  |f1 v1 `oplus` df v1 dv = (f1 `oplus` df) (v1 `oplus` dv) = f1
  (v1 `oplus` dv) `oplus` df (v1 `oplus` dv) (nil (v1 `oplus`
  dv))|.\]
%
We used this equation earlier \citep{CaiEtAl2014ILC}, together
with a weaker form of validity preservation, to characterize
function changes.

\section{Formally defining ⊕ and change structures}
%\subsection{Updating values by changes with ⊕}
\label{sec:change-structures-formal}
\label{sec:oplus}
\label{sec:invalid}
Next, we will introduce formally operators |`oplus`|, |`ominus`|
and |nilc| and relate them to validity. In particular, we will
prove that |fromto tau v1 dv v2| implies |v1 `oplus` dv = v2|,
and explain why the converse is not true.

\pg{resume, turn into figure}
\begin{restatable}[Base definitions of |`oplus`|]{requirement}{baseOplus}
  \label{req:base-oplus}
  For each base type |iota| we have a definition of
  |oplusIdx(iota) : iota -> Dt^iota -> iota|.
\end{restatable}

To prove that |`oplus`| agrees with validity in general
(\cref{thm:valid-oplus}), we must require definitions from
plugins to satisfy this theorem on base types:
\begin{restatable}[|`oplus`| agrees with validity on base types]{requirement}{baseValidOplus}
  \label{req:base-valid-oplus}
  If\\ |fromto iota v1 dv v2| then |v1 `oplus` dv = v2|.
\end{restatable}

\begin{definition}
  For each type |tau| we define operators |oplusIdx(tau) : tau ->
  Dt^tau -> tau|, |ominusIdx(tau) : tau -> tau -> Dt^tau|.
\end{definition}

We define then |`oplus`|, |nilc| and |`ominus`| on function spaces:
\begin{code}
  nil v = v `ominus` v
  f1 (oplusIdx(A -> B)) df = \v -> f1 v `oplus` df v (nil v)
  f2 (ominusIdx(A -> B)) f1 = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
\end{code}

In particular, when |A -> B = eval(sigma) -> eval(tau)|, it follows that
\begin{code}
  f1 (oplusIdx(sigma -> tau)) df = \v -> f1 v `oplus` df v (nil v)
  f2 (ominusIdx(sigma -> tau)) f1 = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
\end{code}

\pg{Both change structure requirements, theorems on types}
\begin{restatable}[|`ominus`| produces valid changes]{lemma}{validOminus}
  \label{thm:valid-ominus}
  |`ominus`| produces valid changes, that is |fromto tau v1 (v2
  `ominus` v1) v2| and |v1 `oplus` (v2 `ominus` v1) = v2| for any
  type |tau| and any |v1, v2 : eval(tau)|.
\end{restatable}
\validOplus*
\begin{proof}\pg{?}
\end{proof}
\begin{restatable}[|`ominus`| inverts |`oplus`|]{lemma}{oplusOminus}
  For any type |tau| and any values |v1, v2 : eval(tau)|,
  |`oplus`| inverts |`ominus`|, that is |v1 `oplus` (v2 `ominus`
  v1) = v2|.
\end{restatable}
\begin{proof}
  From \cref{thm:valid-ominus,thm:valid-oplus}.
\end{proof}
\deriveCorrectOplus*
The proof came earlier.
\nilChangesExist*
\begin{proof}\pg{?}
\end{proof}


We only need |`ominus`| to be able to define nil changes on
arbitrary functions |f : eval(sigma -> tau)|.

However, as anticipated earlier, if |f| is the semantics of a
well-typed term |t|, that is |f = eval(t) emptyRho|, we can
define the nil change of |f| through its derivative.\pg{See
  before}
% no, we need full abstraction, unless the term is closed.

\pg{figure}
% \NewDocumentCommand{\RightFramedSignatureML}{m}
% {\vbox{\hfill\fbox{\(
%         #1
% \)
%     }}}

\begin{figure}
  \pg{change structures}
  \[|nil v = v `ominus` v |\]
\begin{subfigure}[c]{0.6\textwidth}
  \RightFramedSignature{|oplusIdx(A): A -> Dt^A -> A|}
  \RightFramedSignature{|ominusIdx(A): A -> A -> Dt^A|}
\begin{code}
  f1 (oplusIdx(A -> B)) df = \v -> f1 v `oplus` df v (nil v)
  f2 (ominusIdx(A -> B)) f1 = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
\end{code}
\caption{Change structures for function spaces}
\end{subfigure}
\begin{subfigure}[c]{0.6\textwidth}
  \RightFramedSignature{|oplusIdx(tau): eval(tau -> Dt^tau -> tau)|}
  \RightFramedSignature{|ominusIdx(tau): eval(tau -> tau -> Dt^tau)|}
\begin{code}
  f1 (oplusIdx(sigma -> tau))   df = \v -> f1 v `oplus` df v (nil v)
  v1 (oplusIdx iota)            dv = ...
  f2 (ominusIdx(sigma -> tau))  f1 = \v dv -> f2 (v `oplus` dv) `ominus` f1 v
  v2 (ominusIdx iota)           v1 = ...
\end{code}
\caption{|`oplus`| and |`ominus`| on semantic domains}
\end{subfigure}
\begin{subfigure}[c]{0.7\textwidth}
  \RightFramedSignature{|oplusIdx(Gamma): eval(Gamma -> Dt^Gamma -> Gamma)|}
  \RightFramedSignature{|ominusIdx(Gamma): eval(Gamma -> Gamma -> Dt^Gamma)|}
\begin{code}
  emptyRho `oplus` emptyRho                    = emptyRho
  (rho, x = v) `oplus` (drho, x = v, dx = dv)  = (rho `oplus` drho, x = v `oplus` dv)
  emptyRho `ominus` emptyRho                   = emptyRho
  (rho2, x = v2) `ominus` (rho1, x = v1)       = (rho2 `ominus` rho1, x = v1, dx = v2 `ominus` v1)
\end{code}
  % nil emptyRho = emptyRho
  % nil (rho, x = v) = nil rho, x = v, dx = nil v
\caption{|`oplus`| and |`ominus`| on environments}
\end{subfigure}
\validOplus*
  \deriveCorrectOplus*
  \nilChangesExist*

  \caption{Defining change structures.}
  \label{fig:change-structures}
\end{figure}

% \subsection{Derivatives are nil changes}
% \pg{This now goes earlier?}
% When we introduced derivatives, we claimed we can compute them by
% applying differentiation to function bodies.
% In fact, we can
% compute the derivative of a closed lambda abstraction by
% differentiating the whole abstraction!

% To see why, let's first consider an arbitrary closed term |t|,
% such that |/- t : tau|.

% If we differentiate a closed term |/- t : tau|, we get a change
% term |derive(t)| from |t| to itself\pg{Lexicon not introduced for
%   terms.}: |fromto tau (eval(t)
% emptyRho) (eval(derive(t)) emptyRho) (eval(t) emptyRho)|. We call such changes nil changes;
% they're important for two reasons. First, we will soon see that a
% identity element for |`oplus`| has its uses. Second, nil changes at
% function type are even more useful. A nil function change for
% function |f| takes an input |v1| and input change |dv| to a
% change from |f v1| and |f (v1 `oplus` dv)|. In other words, a nil
% function change for |f| is a \emph{derivative} for |f|!

% %\pg{steps}
% To sum up, if |f| is a closed function |derive(f)| is its
% derivative. So, if |f| is unary, \cref{eq:derivative-requirement}
% becomes in particular:
% \begin{equation}
%   \label{eq:correctness}
%   |f (a `oplus` da) `cong` (f a) `oplus` (derive(f) a da)|
% \end{equation}

\pg{move back in, readd, ...}

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
% to output |u2 `elem` eval(tau1)|, and soon.

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
