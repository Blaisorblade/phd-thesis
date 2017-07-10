% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes-popl.fmt

\section{Introduction}

Incremental computation is often desirable: after computing an output from some
input, we often need to produce new outputs corresponding to changed inputs. One
can simply rerun the same \emph{base program} on the new input; but instead,
incremental computation transforms the input change to an output change. This
can be desirable because more efficient.

Incremental computation could also be desirable because the changes themselves
are of interest: Imagine a typechecker explaining how some change to input
source propagates to changes to the typechecking result. More generally, imagine
a program explaining how some change to its input propagates through a
computation into changes to the output.

ILC (Incremental $\lambda$-Calculus)~\citep{CaiEtAl2014ILC} is
a recent approach to incremental computation for higher-order languages.
ILC represents changes from an old value |v1| to an updated value |v2| as a
first-class value written |dv|. ILC also transforms statically \emph{base programs}
to \emph{incremental programs} or \emph{derivatives}: derivatives produce
output changes from changes to all their inputs. Since functions are first-class
values, ILC introduces a notion of function changes.

However, as mentioned by \citeauthor{CaiEtAl2014ILC} and as we explain below,
ILC as currently defined does not allow reusing intermediate results created by the
base computation during the incremental computation. That restricts ILC to
supporting efficiently only \emph{self-maintainable computations}, a rather
restrictive class: for instance, mapping self-maintainable functions on a sequence is
self-maintainable, but dividing numbers isn't! In this paper, we remove this
limitation.

% non-blinded
% In this paper, we address this restriction as we promised in previous work.
%In keeping with our approach, we try to avoid forcing unnecessary overhead onto
%the computation.

To remember intermediate results, many incrementalization approaches rely on
forms of memoization: one uses hashtables to memoize function results, or
dynamic dependence graphs~\citep{Acar05} to remember the computation trace.
However, such data structures often remember results that might not be reused;
moreover, the data structures themselves (as opposed to their values) occupy
additional memory, looking up intermediate results has a cost in time, and
typical general-purpose optimizers cannot predict results from memoization
lookups. Instead, ILC aims to produce purely functional programs that are
suitable for further optimizations.

We eschew memoization: instead, we transform programs to
\emph{cache-transfer style (CTS)}, following ideas from \citet{Liu95}. CTS functions
output \emph{caches} of intermediate results along with their primary results. Caches
are just nested tuples whose structure is derived from code, and accessing them
does not involve looking up keys depending on inputs. We also extend
differentiation to produce \emph{CTS derivatives}, which can extract from caches
any intermediate results they need.
%\pg{they can also extract inputs, but I can't explain it here.}
This approach was inspired and pioneered by \citeauthor{Liu95} for untyped
first-order functional languages, but we integrate
it with ILC and extend it to higher-order typed languages.

% \pg{we don't!}
%and then use program transformation techniques to eliminate unneeded state.
%
While CTS functions still produce additional intermediate data structures,
produced programs can be subject to further optimizations.
We believe static analysis of a CTS function and its CTS derivative can identify
and remove unneeded state (similar to what has been done by \citeauthor{Liu95}),
as we discuss in \cref{sec:cache-pruning}.
We leave a more careful analysis to future work.

We prove most of our formalization correct in Coq
To support non-simply-typed programs, all our proofs
are for untyped $\lambda$-calculus, while previous ILC correctness proofs were
restricted to simply-typed $\lambda$-calculus.
Unlike previous ILC proofs, we simply define which changes are valid
via a \emph{logical relation}, then show the fundamental property for this
logical relation (see \cref{sec:ilc-background}). To extend this proof to
untyped $\lambda$-calculus, we switch to \emph{step-indexed} logical relations.

To support differentiation on our case studies, we also represent function changes
as closures that can be inspected, to support manipulating them more efficiently
and detecting at runtime when a function change is \emph{nil} hence need not be
applied. To show this representation is correct, we also use closures in our
mechanized proof.

Unlike plain ILC, typing programs in CTS is challenging, because the shape of
caches for a function depends on the function implementation.
Our case studies show how to non-trivially embed resulting programs in typed
languages, at least for our case studies, but our proofs support an untyped
target language.

In sum, we present the following contributions:
\pg{revise more, add sections; this is getting redundant with the text.}
\begin{itemize}
\item via examples, we motivate extending ILC to remember intermediate
  results (\cref{sec:cts-motivation});
\item we give a novel proof of correctness for ILC for untyped
  $\lambda$-calculus, based on step-indexed logical relations
  (\cref{sec:sound-derive});
\item building on top of ILC-style differentiation, we show how to transform
  untyped higher-order programs to \emph{cache-transfer-style (CTS)}
  (\cref{sec:transformation});
\item we show that programs and derivatives in cache-transfer style
  \emph{simulate} correctly their non-CTS variants (\cref{sec:transformation-soundness});
\item we mechanize in Coq most of our proofs (see supplementary material);
\item we perform performance case studies (in \cref{sec:case-studies}) applying
  (by hand) extension of this technique to Haskell programs, and incrementalize
  efficiently also programs that do not admit self-maintainable derivatives.
\end{itemize}

\pg{Try merging with contributions if we can.}
The rest of the paper is organized as follows. \Cref{sec:cts-motivation} summarizes
ILC and motivates the extension to cache-transfer style.
\Cref{sec:formalization} presents our formalization and proofs.
\Cref{sec:case-studies} presents our case studies and benchmarks. \Cref{sec:cts-rw}
discusses related work and \cref{sec:conclusions} concludes.
