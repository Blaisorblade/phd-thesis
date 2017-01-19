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
To understand incrementalization better, consider the |grand_total| program (presented in
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
representation for the changes to the inputs (say, for now,
|dxs = {{Remove 1}}| and |dys = {{Add 5}}|), we can compute the new
result through a function |dgrand_total| that takes the old inputs
|xs = {{1,1}}| and |ys = {{2, 3, 4}}| and the changes |dxs| and |dys|
to produce the output change.
In this case, it would compute the change
|dgrand_total xs dxs ys dys = Plus 4|,
which can then be used to update the original output |11|
%
to yield the updated result |15|. We call |dgrand_total| the \emph{derivative} of |grand_total|, and we call the program transformation producing |dgrand_total| \emph{differentiation} (or, sometimes, simply \emph{derivation}).
A derivative is a function in the
same language as |grand_total|, accepting and producing changes, which
are simple first-class values of this language.
%
If we increase the size of the original inputs |xs| and |ys|, the time
complexity of |grand_total xs ys| increases linearly, while the time complexity
of |dgrand_total xs dxs ys dys| only depends on the sizes of |dxs| and |dys|,
which under our assumptions are smaller (just like in our example).

\subsection{Differentiation}
\pg{This example is still a bit too complex as written; I'm skipping too many steps.}

To help fix ideas for later discussion, let us show on a simpler
variant of |grand_total| how the derivative of |grand_total|
looks like.

For now we consider the
following program:
\begin{code}
grand_total2  = \ xs ys -> sum (merge xs ys)
output       = grand_total2 {{1, 1}} {{2, 3, 4}} = 11
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
grand_total2   = \ xs      ys      ->  sum  (merge  xs   ys)
dgrand_total2  = \ xs dxs  ys dys  ->  sum  (merge  dxs  dys)
\end{code}

Finally, we need to transform the binding of |output| and its body. By iterating similar steps
In the end we get:\pg{fill missing steps}
\begin{code}
grand_total2   = \ xs      ys      ->  sum  (merge  xs   ys)
dgrand_total2  = \ xs dxs  ys dys  ->  sum  (merge  dxs  dys)
output         = grand_total2   {{1, 1}}              {{2, 3, 4}}
doutput        = dgrand_total2  {{1, 1}} {{Remove 1}} {{2, 3, 4}} {{Add 5}}
\end{code}

\pg{Integrate this.}
The transformation is defined by:
\begin{code}
  derive(\x -> t) = \x dx -> derive(t)
  derive(s t) = derive(s) t (derive(t))
  derive(x) = dx
  derive(let x = t1 in t2) =
    let  x = t1
         dx = derive(t1)
    in   derive(t2)
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
intuitively, a program function |df| is a derivative of |f| if
the semantics of |df|, that is |eval(df)|, is the derivative of
the semantics of |f|, giving us \cref{eq:correctness} from
\cref{eq:correctness-math-funs}.\footnote{A few technical details
  complicate the picture, but we'll discuss them later.}

\subsection{Our language}
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

Of note, our language is strongly normalizing.

\subsection{The meta-language of our proofs}
In this subsection we describe the meta-language used in our
correctness proof.
To prove the correctness of \ILC, we provide a mechanized proof
in Agda~\citep{agda-head}. Agda is an implementation of
intensional Martin-Löf type theory.

To make our proofs more accessible, we present them in terms of
set theory, though for convenience we still use (informally)
dependently-typed type signatures where useful. The differences
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

To prove that incrementalization preserves the final results of
our object-language programs, we need to give it a semantics. To
this end we use a denotational semantics. Since our object
language (simply-typed $\Gl$-calculus) is strongly
normalizing~\citep[Ch. 12]{Pierce02TAPL} and since we do not add
computational effects, we can eschew use of domain theory or any
other technique to handle partiality or other effects: The
domains for our denotational semantics are simply Agda types, and
semantic values are Agda values---in other words, we give a
denotational semantics in terms of type
theory.\footnote{Alternatively, some would call such a semantics
  a definitional interpreter~\citep{Amin2017}}
%
Using denotational semantics allows us to state the specification
of differentiation directly in the semantic domain, and take
advantage of Agda's support for equational reasoning for proving
equalities between Agda functions.

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
