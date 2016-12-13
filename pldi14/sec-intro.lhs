% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

% \section{Introduction}
\label{sec:intro}

Incremental computation has a long-standing history in computer
science~\citep{Ramalingam93}. Often, a program needs to update its
output efficiently to reflect input
changes~\citep{Salvaneschi13reactive}. Instead of rerunning such a
program from scratch on its updated input, incremental
computation research looks for alternatives that are cheaper in a common scenario:
namely, when the input change is much smaller than the input itself.

\section{A motivating example}
To understand incrementalization better, consider the $\Program$ program (presented in
Haskell-like notation), which calculates the sum of all numbers
in collections |xs| and |ys|:
\begin{code}
grand_total  = \ xs ys -> fold (+) 0 (merge xs ys)
output       = grand_total {{1, 1}} {{2, 3, 4}} = 11
\end{code}
With |{{...}}| we represent a multiset or \emph{bag}, that is an unordered collection (like a set)
where elements are allowed to appear more than once (unlike a set).
Now assume that the input |xs| changes from |{{1,1}}| to
|{{1}}|, and |ys| changes from |{{2, 3, 4}}| to |{{2, 3, 4, 5}}|.
Instead of recomputing |output| from scratch, we could also compute it incrementally. If we have a
representation for the changes to the inputs (say,
|dxs = {{Remove 1}}| and |dys = {{Add 5}}|), we can compute the new
result through a function |dgrand_total| that takes the old inputs
|xs = {{1,1}}| and |ys = {{2, 3, 4}}| and the changes |dxs| and |dys|
to produce the output change.
In this case, it would compute the change
|dgrand_total xs dxs ys dys = Plus 4|,
which can then be used to update the original output |11|
%
to yield the updated result |15|. We call |dgrand_total| the \emph{derivative} of |grand_total|.
It is a function in the
same language as |grand_total|, accepting and producing changes, which
are simple first-class values of this language.
%
If we increase the size of the original inputs |xs| and |ys|, the time
complexity of |grand_total xs ys| increases linearly, while the time complexity
of |dgrand_total xs dxs ys dys| only depends on the sizes of |dxs| and |dys|,
which under our assumptions are smaller (just like in our example).

\section{A program transformation}
To support automatic incrementalization, in the next chapters we introduce the \ILC\
(incrementalizing $\Gl$-calculi) framework. We define
an automatic program transformation $\DERIVE$
that \emph{differentiates} programs, that is, computes their
derivatives; $\DERIVE$ guarantees that
\begin{equation}
  \label{eq:correctness}
  |f (a `oplus` da) `cong` (f a) `oplus` (derive(f) a da)|
\end{equation}
where
$\cong$ is denotational equality,
|da| is a change on |a| and |a `oplus` da| denotes |a|
updated with change |da|, that is, the updated input of |f|.
\pg{Non-sequitur, this is not proven to be an optimization, not
  by this equation.}
Hence, when the derivative is faster than
recomputation, we can optimize programs by replacing the
left-hand side, which recomputes the output from scratch, with
the right-hand side, which computes the output incrementally
using derivatives, while preserving the program result.

To understand this equation we must also formalize changes for
functions. That's because \ILC\ applies to higher-order
languages, where functions can be inputs or outputs. This makes
\cref{eq:correctness} less trivial to state and prove.

To simplify the formalization we consider, beyond derivatives of
programs, also derivatives of pure mathematical functions (\cref{sec:1st-order-changes}). We
distinguish programs and mathematical functions as in
denotational semantics.%
\footnote{We avoid however using domain theory. To this end, we
  restrict attention in our theory to strongly normalizing
  calculi.}
%
We define those with an analogue of
\cref{eq:correctness}: function |df| is a derivative of |f| if
and only if
\begin{equation}
  \label{eq:correctness-math-funs}
  |f (a `oplus` da) = (f a) `oplus` (df a da)|
\end{equation}
Once we establish a theory of changes and derivatives for
mathematical functions, we will be able to lift that to programs:
conceptually, a program function |df| is a derivative of |f| if
the semantics of |df|, that is |eval(df)|, is the derivative of
the semantics of |f|, giving us \cref{eq:correctness} from
\cref{eq:correctness-math-funs}.

\ILC\ considers as object language a simply-typed $\Gl$-calculus
parameterized by \emph{language plugins} (or just plugins). A plugin
defines
%
(a) base types and primitive operations, and
%
(b) a change representation for each base type, and an
incremental version for each primitive. In other words, the plugin
specifies the primitives and their respective derivatives, and
\ILC\ can glue together these simple derivatives in such a way
that derivatives for arbitrary simply-typed $\Gl$-calculus expressions
using these primitives can be computed. Both our implementation and our correctness proof 
is parametric in the plugins, hence it is easy to support (and prove correct)
new plugins.


% Our Agda formalization, Scala implementation and benchmark
% results are available at the URL
% \url{http://inc-lc.github.io/}.
% All lemmas and theorems presented
% in this chapter have been proven in Agda.
% In the chapter, we present an overview of
% the formalization in more human-readable form, glossing over some
% technical details.
