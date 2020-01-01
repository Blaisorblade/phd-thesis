% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Related work}
\label{sec:rw}
\label{ch:incr-rw}

Existing work on incremental computation can be divided into two
groups: Static incrementalization and dynamic incrementalization.
Static approaches analyze a program statically and generate an incremental
version of it. Dynamic approaches create dynamic dependency graphs while
the program runs and propagate changes along these graphs.

The trade-off between the two is that static approaches have the potential
to be faster because no dependency tracking at runtime is needed, whereas
dynamic approaches can support more expressive programming languages.
%
\ILC\ is a static approach, but compared to the other static
approaches it supports more expressive languages.

In the remainder of this section, we analyze the relation to the
most closely related prior works. \Citet{Ramalingam93}, \citet{Gupta99MMV}
and \citet{Acar06} discuss further related work.
Other related work, more closely to cache-transfer style, is
discussed in \cref{sec:cts-rw}.

\section{Dynamic approaches}
One of the most advanced dynamic approach to incrementalization is
self-adjusting computation, which has been applied to Standard ML
and large subsets of C~\citep{Acar09,Hammer11}.
In this approach, programs execute on the original
input in an enhanced runtime environment that tracks the
dependencies between values in a \emph{dynamic
  dependence graph}~\citep{Acar06}; intermediate results are
memoized.
Later, changes to the input propagate through
dependency graphs from changed inputs to results,
updating both intermediate and final results;
this processing is often more efficient than recomputation.

However, creating dynamic
dependence graphs imposes a large constant-factor overhead during
runtime, ranging from 2 to 30 in reported
experiments~\citep{Acar09EAS,Acar10TDT}, and affecting the
initial run of the program on its base input.
\citet{Acar10TDT} show how to support high-level data
types in the context of self-adjusting computation; however, the
approach still requires expensive runtime bookkeeping during the initial run.
Our approach, like other static ones, uses a standard runtime
environment and has no overhead
during base computation, but may be less efficient when processing
changes. This pays off if the initial input is
big compared to its changes.


\citet{Chen11} have developed a static transformation for purely
functional programs, but this transformation just provides a superior interface to use
the runtime support with less boilerplate, and does not reduce
this performance overhead. Hence, it is still a dynamic approach, unlike
the transformation this work presents.

Another property of self-adjusting computation
is that incrementalization is only efficient if the program has a suitable
computation structure. For instance, a program
folding the elements of a bag with a left or right fold will not
have efficient incremental behavior; instead, it's necessary that
the fold be shaped like a balanced tree. In general,
incremental computations become efficient only if they are \emph{stable}~\citep{Acar05}.
Hence one may need to massage the program to make it efficient. Our methodology is
different: Since we do not aim to incrementalize arbitrary programs written in standard
programming languages, we can select primitives that have efficient derivatives and thereby require
the programmer to use them.

Functional reactive programming \citep{Elliott:1997:FRA:258948.258973}
can also be seen as a dynamic approach to incremental computation;
recent work by \citet{Maier2013} has
focused on speeding up reactions to input changes by making them
incremental on collections. \citet{Willis08} use dynamic techniques
 to incrementalize JQL queries.

\section{Static approaches}
Static approaches analyze a program at compile-time and produce an
incremental version that efficiently updates the output
of the original program according to changing inputs.

Static approaches have the potential to be more efficient than dynamic approaches,
because no bookkeeping at runtime is required. Also, the computed incremental
versions can often be optimized using standard compiler techniques
such as constant folding or inlining.
However, none of them support first-class functions; some
approaches have further restrictions.

Our aim is to apply static incrementalization to more expressive languages;
in particular, \ILC\ supports first-class functions and an open
set of base types with associated primitive operations.

\citet{Sundaresh91} propose to incrementalize programs using
partial evaluation: given a partitioning of program inputs in parts
that change and parts that stay constant,
\citeauthor{Sundaresh91} partially evaluates a given program relative
to the constant input parts, and combine the result with the
changing inputs.

\subsection{Finite differencing}
\label{sec:finite-diff}
\citet{Paige82FDC} present derivatives for a first-order language
with a fixed set of primitives.
\citet{Blakeley:1986:EUM} apply these ideas to a class of relational queries.
The database community extended
this work to queries on relational data, such as in \emph{algebraic
  differencing}~\citep{Gupta99MMV}, which inspired our work and
terminology. However, most of this work does not apply to nested
collections or algebraic data types, but only to relational
(flat) data, and no previous approach handles first-class
functions or programs resulting from defunctionalization or
closure conversion. Incremental support is typically designed
monolithically for a whole language, rather than piecewise.
Improving on algebraic differencing, DBToaster (\citet{Koch10IQE,Koch14})
\emph{guarantees} asymptotic speedups with a compositional query
transformation and delivers huge speedup in realistic benchmarks,
though still for a first-order database language.
\pg{continue with new work, discuss why we don't do iterated differentiation.}

More general (non-relational) data types are considered in the work by \citet{GlucheGrust97Incr};
our support for bags and the use of groups is inspired by their work,
but their architecture is still rather restrictive: they lack
support for function changes and restrict incrementalization to
self-maintainable views, without hinting at a possible solution.

It seems possible to transform higher-order functional programs
to database queries, using a variety of approaches
\citep{Grust:2009:FDP:1559845.1559982,Cheney2013practical}, some
of which support first-class functions via closure conversion
\citep{Grust2013first,Grust2013functions}, and incrementalize the
resulting programs using standard database technology. Such a
solution would inherit limitations of database incrementalization
approaches: in particular, it appears that database
incrementalization approaches such as DBToaster can handle the
insertion and removal of entire table rows, not of smaller
changes. Nevertheless, such an alternative approach might be
worth investigating.

Unlike later approaches to higher-order differentiation, we do
not restrict our base types to
groups unlike \citet{Koch2016incremental}, and transformed programs we
produce do not require further runtime
transformation unlike \citet{Koch2016incremental} and \citet{Huesca2015incrementality},
as we discuss further next.

\newcommand{\ldiff}{\TitleLambda--diff}
\subsection{\TitleLambda{}--diff and partial differentials}
\label{sec:rw-partial-differentials}
In work concurrent with \citet{CaiEtAl2014ILC}, \citet{Huesca2015incrementality}
introduces an alternative formalism, called \ldiff, for incremental computation
by program transformation. While \ldiff{} has some appealing features, it
currently appears to require program transformations at
runtime. Other systems appear to share this
feature~\citep{Koch2016incremental}. Hence, this section
discusses the reason in some detail.

Instead of differentiating a term |t| relative to all inputs (free
variables and function arguments) via |derive t|, like ILC,
\ldiff{} differentiates terms
relative to one input variable, and writes
$\sfrac{\partial t}{\partial x, d_x}$
for the result of differentiating $t$
relative to $x$, a term that computes the change in $t$ when the
value for $x$ is updated by change $d_x$. The formalism also uses
pointwise function changes, similarly to what we discussed in
\cref{ssec:pointwise-changes}.

Unfortunately, it is not known how to define such a
transformation for a $\lambda$-calculus with a standard
semantics, and the needed semantics appear to require runtime
term transformations, which are usually considered problematic
when implementing functional languages.
In particular, it appears necessary to introduce a new term
constructor |D t|, which evaluates |t| to a function value |\y ->
u|, and then evaluates to $\lambda (y, d_y) \to \sfrac{\partial
t}{\partial y, d_y}$, which differentiates |t| at runtime
relative to its head variable |y|. As an indirect consequence, if the
program under incrementalization contains function term |Gamma /-
t : sigma -> tau|, where |Gamma| contains |n| free variables, it
can be necessary in the worst-case to differentiate |t| over any
subset of the |n| free variables in |Gamma|. There are $2^n$ such
subsets. To perform all term transformations before runtime, it
seems hence necessary in the worst case to precompute $2^n$
partial derivatives for each function term |t|, which appears
unfeasible.
On the other hand, it is not clear how often this worst-case is
realized, or how big |n| grows in typical programs, or if it is
simply feasible to perform differentiation at runtime, similarly
to JIT compilation. Overall, an efficient implementation of
\ldiff{} remains an open problem.
It appears also \citet{Koch2016incremental}
suffer similar problems, but a few details appear simpler since
they restrict focus to functions over groups.

To see why \ldiff{} need introduce |D t|, consider
differentiating $\sfrac{\partial s\;t}{\partial x, d_x}$, that is,
the change $d$ of $s\;t$ when $x$x is updated by change $d_x$.
Change $d$ depends (a) on the change of $t$ when $x$ is updated
by $d_x$, that is
$\sfrac{\partial t}{\partial x, d_x}$;
(b) on how $s$ changes when its input $t$ is updated by
$\sfrac{\partial t}{\partial x, d_x}$; to express this change, \ldiff{}
expresses this via $|(D s) t|\; \sfrac{\partial t}{\partial x, d_x}$;
(c) on the change of $s$ (applied to the updated $t$) when $x$ is
updated by $d_x$, that is $\sfrac{\partial t}{\partial x, d_x}$.
To compute component (b), \ldiff{} writes |D s| to
differentiate |s| not relative to |x|, but relative to the still unknown head
variable of |s|.
If |s| evaluates to |\y -> u|, then |y| is the head variable of |s|, and |D s|
differentiates |u| relative to |y| and evaluates to $\lambda (y, d_y) \to
\sfrac{\partial u}{\partial y, d_y}$.
% Hence, \citeauthor{Huesca2015incrementality} adds term |D t| to
% the syntax of $\lambda$-calculus; evaluating

Overall, the rule for differentiating application in $\lambda$-diff is
\[
  \frac{\partial s\;t}{\partial x, d_x} = (D s)\left(t, \frac{\partial t}{\partial x,
d_x}\right) \circledcirc \frac{\partial s}{\partial x, d_x}\left(t \oplus \frac{\partial
t}{\partial x, d_x}\right).
  \]

This rule appears closely related to \cref{eq:pointwise-rewrite},
hence we refer to its discussion for clarification.

On the other hand, differentiating a term relative to all its
inputs introduces a different sort of overhead. For instance, it
is much more efficient to differentiate |map f xs| relative to
|xs| than relative to |f|: if |f| undergoes a non-nil change
|df|, |derive(map f xs)| must apply |df| to each elements in the
updated input |xs|. Therefore, in our practical implementations
|derive(map f xs)| tests whether |df| is nil and uses a more
efficient implementation. In \cref{sec:applying}, we detect at
compile time whether |df| is guaranteed to be nil. In
\cref{sec:incr-nest-loop}, we instead detect at runtime whether |df| is
nil. In both cases, authors of derivatives must implement this
optimization by hand. Instead, \ldiff{} hints at a more general
solution.

\subsection{Static memoization}
\label{ssec:staticmemo}
\citeauthor{Liu00}'s work~\citep{Liu00} allows to incrementalize a first-order base
program $f(\Old{x})$ to compute $f(\New{x})$, knowing how
$\New{x}$ is related to $\Old{x}$. To this end, they transform
$f(\New{x})$ into an incremental program which reuses the
intermediate results produced while computing $f(\Old{x})$, the
base program. To this end, (i) first the base program is
transformed to save all its intermediate results, then (ii) the
incremental program is transformed to reuse those intermediate
results, and finally (iii) intermediate results which are not
needed are pruned from the base program. However, to reuse
intermediate results, the incremental program must often be
rearranged, using some form of equational reasoning, into some
equivalent program where partial results appear literally. For
instance, if the base program $f$ uses a left fold to sum the
elements of a list of integers $\Old{x}$, accessing them from the
head onwards, and $\New{x}$ prepends a new element $h$ to the
list, at no point does $f(\New{x})$ recompute the same results.
But since addition is commutative on integers, we can rewrite
$f(\New{x})$ as $f(\Old{x}) + h$. The author's CACHET system will
try to perform such rewritings automatically, but it is not
guaranteed to succeed. Similarly, CACHET will try to synthesize
any additional results which can be computed cheaply by the base
program to help make the incremental program more efficient.

Since it is hard to fully automate such reasoning, we move
equational reasoning to the plugin design phase. A
plugin provides general-purpose higher-order primitives for which
the plugin authors have devised efficient derivatives (by using
equational reasoning in the design phase). Then, the
differentiation algorithm computes incremental
versions of user programs without requiring further user intervention.
It would be useful to combine \ILC\ with some form of static
caching to make the computation of derivatives which
are not self-maintainable more efficient. We plan to do so
in future work.
%Our approach is instead fully automatic, and will always produce
%a result, which in the worst case will merely be slow;
%% they can also fail and then 'produce a slow program'.
%
%we envision the use of directed rewrite rules for further
%optimization of programs, instead of undirected search.
%% Not so important.
