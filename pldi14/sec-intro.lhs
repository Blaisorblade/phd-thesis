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

For instance, consider the $\Program$ program (presented in
Haskell-like notation), which calculates the sum of all numbers
in collections |xs| and |ys|.
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
of |dgrand_total xs dxs ys dys| only depends on the size of |dxs| and |dys|,
which is smaller both in our example and in general.

To support automatic incrementalization, in this chapter we introduce the \ILC\
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
Hence, we can optimize programs by replacing the left-hand side,
which recomputes the output from scratch, with the right-hand
side, which computes the output incrementally using derivatives.
% KO: I think this forward references confuses more than it helps.
%Our approach relates to \emph{finite differencing} but has a more
%general theory and support for first-class functions (see
%\cref{sec:finite-diff}).

\ILC\ is based on a simply-typed $\Gl$-calculus
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

This chapter makes the following contributions:
\begin{itemize}
\item We present a novel mathematical theory of changes and derivatives, which is more
  general than other work in the field because changes are
  first-class entities, they are distinct from base values and
  they are defined also for functions (\cref{sec:1st-order-changes}).
  %KO: I think the next sentence cannot be understood at this point.
  %We introduce changes for complex types, defined compositionally.
%
\item We present the first approach to incremental computation for
pure $\lambda$-calculi by a source-to-source transformation, $\DERIVE$, that requires no run-time
support. The transformation produces an incremental program in the same language;
all optimization techniques for the original program are
applicable to the incremental program as well.
%KO: commented this out. I think the purity is not important enough
%to deserve another sentence here, since we only vaguely hint
%at "further research".
%Since our incremental programs use no impure features, they are
%especially amenable to further optimizations, making this approach
%very suitable for further research.
%
% KO: Let's have one bullet point per section. Also, a conjecture
% sounds like a rather weak contribution
%\item We argue that incrementalization is efficient on
%  \emph{self-maintainable programs}, and discuss how further research on
%  static or dynamic memoization can speed up a larger class of programs (\cref{sec:performance-cons}).
%  \pg{This contribution references text which is now commented
%    out. I believe the text should be brought back in.}
%
We prove that our incrementalizing transformation $\DERIVE$
is correct~(\cref{eq:correctness})
by a machine-checked formalization in Agda~\citep{agda-head}.
The proof gives insight into the definition of $\DERIVE$: we
first construct the derivative $\EvalInc{-}$ of the denotational
semantics of a simply-typed $\lambda$-calculus term, that is, its
\emph{change semantics}.
%
Then, we show that $\DERIVE$ is produced by erasing
$\EvalInc{-}$ to a simply-typed program (\cref{sec:correctness}).

\item While we focus mainly on the theory of changes
and derivatives, we also perform a performance case study.
We implement the derivation transformation in Scala,
with a plug-in architecture that can be extended with new base
types and primitives. We define a plugin with support for
different collection types and use the plugin to 
incrementalize a variant of the MapReduce programming model~\citep{Lammel07}.
  Benchmarks show that on this program,
  incrementalization can reduce asymptotic complexity and can turn $O(n)$
  performance into $O(1)$, improving running time by over 4
  orders of magnitude on realistic inputs (\cref{sec:applying}).

\end{itemize}

% KO: We said all that is in this paragraph before.
% Our formalization is generic in the set of base types and the set
% of primitives that operate on these base types. That is, we
% present only the core of the formalization that deals with
% function types, lambda abstraction, application and variable
% references. Base types and primitives on base types have to be
% added as plugins. The interface between the core formalization
% and the plugins is formalized as well. It consists of the sets,
% operations, and lemmas that a plugin has to provide in order to
% fit into the core formalization. We hope that the generic
% formalization allows us and other researchers to experiment with
% different choices of base types, and different incrementalization
% strategies for these base types.

%We mechanized the formalization, including the separation between
%core and plugins, in the dependently typed programming language
%Agda~\cite{agda-head}.
Our Agda formalization, Scala implementation and benchmark
results are available at the URL
\url{http://inc-lc.github.io/}.
All lemmas and theorems presented
in this chapter have been proven in Agda.
In the chapter, we present an overview of
the formalization in more human-readable form, glossing over some
technical details.

% KO: Old stuff which contains snippets to be integrated in other sections, in 
% particular Related Work.
