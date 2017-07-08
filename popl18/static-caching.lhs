\PassOptionsToPackage{kerning=true}{microtype}
\PassOptionsToPackage{unicode}{hyperref}
%% For double-blind review submission
\documentclass[acmsmall,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission
%\documentclass[acmsmall,review]{acmart}\settopmatter{printfolios=true}
%\documentclass[sigplan,10pt,review]{acmart}\settopmatter{printfolios=true}

%% For final camera-ready submission
%\documentclass[acmlarge]{acmart}\settopmatter{}

% Directives for lhs2TeX formatting

%include polycode.fmt
%include changes.fmt

% Shrink a bit lhs2TeX code  this hook is there for this reason:
\renewcommand{\hscodestyle}{\small}
% If we're desperate, but it looks bad:
%\renewcommand{\hscodestyle}{\footnotesize}
%
\input{macros}

% Local packages

\usepackage{locallabel,reversion}
\usepackage{syntaxmacros,multicol}
\usepackage{tikz}
\usepackage{pgfplots}
\usepackage{subcaption}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\input{paperInfo}

%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission
\setcopyright{none}             %% For review submission
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2017}           %% If different from \acmYear

%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
\citestyle{acmauthoryear}

% \title[Incremental λ-Calculus in Cache-Transfer Style]{Incremental λ-Calculus in Cache-Transfer Style: Static Memoization by Program Transformation}
\title{Incremental λ-Calculus in Cache-Transfer Style}
\subtitle{Static Memoization by Program Transformation}

\author{Paolo G. Giarrusso}
\affiliation{
  %\position{Position1}
  \department{Wilhelm-Schickard-Institut}              %% \department is recommended
  \institution{University of Tübingen}            %% \institution is required
  % \streetaddress{Street1 Address1}
  \city{Tübingen}
  % \state{State1}
  % \postcode{Post-Code1}
  \country{Germany}
}

\author{Yann Régis-Gianas}
\affiliation{
  \department{IRIF, PPS, {\pi}r^2}              %% \department is recommended
  \institution{University of Paris Diderot, INRIA}            %% \institution is required
  \city{Paris}
  \country{France}
}
\author{Philipp Schuster}
\affiliation{
  \department{Wilhelm-Schickard-Institut}              %% \department is recommended
  \institution{University of Tübingen}            %% \institution is required
  \city{Tübingen}
  \country{Germany}
}

\begin{abstract}
  % TODO: more general abstract, this is too technical.
Incremental computation requires propagating changes and reusing intermediate
results of base computations.
Derivatives, as produced by static differentiation~\citep{CaiEtAl2014ILC}, propagate
changes but do not reuse intermediate results.
We introduce additional program transformations producing purely functional
programs that create and maintain nested tuples of intermediate results. We
avoid remembering values needed by self-maintainable derivatives.
To prove correctness of our transformation, we extend the correctness proof of
static differentiation from STLC to untyped $\lambda$-calculus via
\emph{step-indexed logical relations}, and prove correctness of the additional
transformation via simulation theorems.

We evaluate incrementalization performance via case studies.
We provide derivatives of primitives for operations on collections,
differentiate our case studies using those primitives,
and already on input sizes less than $10^3$ we measure speedups of two orders of
magnitude, up to 180x; computing output changes can be up to 370x faster.
% We augment derivatives to maintain intermediate results while
% introduce a
% program transformation, that produces purely functional programs that produce
% and remember nested tuples of intermediate results and avoid remembering
% values that are only used by self-maintainable derivatives.
\end{abstract}

%\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
%\terms
%term1, term2

%\keywords
%keyword1, keyword2


\maketitle

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
  results (\cref{sec:motivation});
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
The rest of the paper is organized as follows. \Cref{sec:motivation} summarizes
ILC and motivates the extension to cache-transfer style.
\Cref{sec:formalization} presents our formalization and proofs.
\Cref{sec:case-studies} presents our case studies and benchmarks. \Cref{sec:rw}
discusses related work and \cref{sec:conclusions} concludes.

\section{Introducing Cache-Transfer Style}
\label{sec:motivation}
In this section we motivate cache-transfer style (CTS).
\Cref{sec:ilc-background} summarizes a reformulation of ILC, so we recommend it
also to readers familiar with \citet{CaiEtAl2014ILC}.
In \cref{sec:motivating-example} we consider a minimal first-order example, namely an
average function. We incrementalize it using ILC, explain why the result is
inefficient, and show that remembering results via cache-transfer style enables
efficient incrementalization with asymptotic speedups.
In \cref{sec:higher-order-example} we consider a higher-order example that
requires not just cache-transfer style but also efficient support for both nil
and non-nil function changes, together with the ability to detect nil changes.

\subsection{Background}
\label{sec:ilc-background}
ILC considers simply-typed programs, and assumes that base types and primitives
come with support for incrementalization.

The ILC framework describes changes as first-class values, and types them using
dependent types. To each type |A| we associate a type |Dt ^ A| of changes for
|A|, and an \emph{update operator} |`oplus` : A -> Dt^A -> A|, that updates an
initial value with a change to compute an updated value.
We also consider changes for evaluation environments, which contain changes for
each environment entry.

A change |da :: Dt^A| can be \emph{valid} from |a1 :: A| to |a2 :: A|, and we write
then |fromtotau A a1 da a2|. Then |a1| is the \emph{source} or \emph{initial value}
for |da|, and |a2| is the \emph{destination} or \emph{updated value} for |da|.
From |fromtotau A a1 da a2| follows that |a2| coincides with |a1 `oplus` da|, but
validity imposes additional invariants that are useful during
incrementalization.
A change can be valid for more than one source, but a change |da| and a source
|a1| uniquely determine the destination |a2 = a1 `oplus` da|.
To avoid ambiguity, we always consider a change together with a specific source.

Each type comes with its definition of validity: Validity is a ternary
\emph{logical relation}.
%
For function types |A -> B|, we
define |Dt^(A -> B) = A -> Dt^A -> Dt^B|, and say that
a function change |df :: Dt^(A -> B)| is valid from |f1 :: A -> B| to |f2 :: A ->
B| (that is, |fromtotau (A -> B) f1 df f2|) if and only if |df| maps valid input
changes to valid output changes; by that,
we mean that if |fromtotau A a1 da a2|, then |fromtotau B (f1 a1) (df a1 da) (f2 a2)|.
Source and destination of |df a1 da|, that is |f1 a1| and |f2 a2|, are the result of
applying two different functions, that is |f1| and |f2|.

\pg{Rewritten to generalize ``derivative''.}
ILC expresses incremental programs as \emph{derivatives}. Generalizing previous
usage, we simply say derivative for all terms produced by differentiation.
If |dE| is a valid environment change from |E1| to |E2|, and term |t| is
well-typed and can be evaluated against environments |E1, E2|,
then term |derive t|, the derivative of |t|, evaluated against |dE|, produces
a change from |v1| to |v2|, where |v1| is the value of |t| in environment |E1|,
and |v2| is the value of |t| in environment |E2|. This correctness property follows
immediately the \emph{fundamental property} for the logical relation of
validity and can be proven accordingly; we give a step-indexed variant of this
proof in \cref{sec:sound-derive}.
%\pg{For now, omit citations to my PhD thesis, especially to chapters.}
%~\citep[Ch.~12]{GiarrussoPhD2017}.
If |t| is a function and |dE| is a nil change (that is, its source |E1| and
destination |E2| coincide), then |derive t| produces a nil function change and
is also a derivative according to \citet{CaiEtAl2014ILC}.

To support incrementalization, one must define change types and validity for
each base type, and a correct derivative for each primitive. Functions written
in terms of primitives can be differentiated automatically.
As in all approaches to incrementalization (see \cref{sec:rw}), one cannot
incrementalize efficiently an arbitrary program: ILC limits the effort to base
types and primitives.

\subsection{A first-order motivating example: computing averages}
\label{sec:motivating-example}
% XXX I'm not happy with these variable names.
Suppose we need to compute the average |y| of a bag of numbers |xs :: Bag Int|,
and that whenever we receive a change |dxs :: Dt ^ (Bag Int)| to this bag we
need to compute the change |dy| to the average |y|.

%For simplicity, we omit ominus... we use

In fact, we expect multiple consecutive updates to our bag. Hence, we say we have
an initial bag |xs1| and compute its average |y1| as |y1 = avg xs1|, and then consecutive changes
|dxs1, dxs2, ...|. Change |dxs1| goes from |xs1| to |xs2|,
|dxs2| goes from |xs2| to |xs3|, and so on. We need to compute |y2 = avg xs2|,
|y3 = avg xs3|, but more quickly than we would by calling |avg| again.

We can compute the average through the following function (that we present in Haskell):
\begin{code}
avg xs =
  let  s =  sum xs
       n =  length xs
       r =  div s n
  in   r
\end{code}
We write this function in \emph{A'-normal form} (A'NF), a small variant of
\emph{A-normal form} (ANF)~\cite{sabry1993reasoning} that we introduce. In
A'NF, programs bind to a variable the result of each function call in |avg|,
instead of using it directly; unlike plain ANF, A'NF also binds the result of
tail calls such as |div s n| in |avg|. A'NF simplifies conversion to
cache-transfer style.

We can incrementalize efficiently both |sum| and |length| by generating via
ILC their derivatives |dsum| and |dlength|, assuming a language plugin
supporting bags supporting folds.

But division is more challenging. To be sure, we can write the following
derivative:
\begin{code}
ddiv a1 da b1 db =
  let  a2 = a1 `oplus` da
       b2 = b1 `oplus` db
  in   div a2 b2 `ominus` div a1 b1
\end{code}
Function |ddiv| computes the difference between the updated and the original
result without any special optimization, but still takes $O(1)$ for machine
integers. But unlike other derivatives, |ddiv| uses its base inputs |a1| and
|b1|, that is, it is not \emph{self-maintainable}~\citep{CaiEtAl2014ILC}.

Because |ddiv| is not self-maintainable, a derivative calling it will not be
efficient. To wit, let us look at |davg|, the derivative of |avg|:

\begin{code}
davg xs dxs =
  let  s   =  sum xs
       ds  = dsum xs dxs
       n   =  length xs
       dn  = dlength xs dxs
       r   = div s n
       dr  = ddiv s ds n dn
  in   dr
\end{code}

This function recomputes |s|, |n| and |r| just like in |avg|, but |r| is not
used so its recomputation can easily be removed by later optimizations. On the
other hand, derivative |ddiv| will use the values of its base inputs |a1| and |b1|,
so derivative |davg| will need to recompute |s| and |n| and save no time over
recomputation!
If |ddiv| were instead a \emph{self-maintainable} derivative, the computations
of |s| and |n| would also be unneeded and could be optimized away.
\citeauthor{CaiEtAl2014ILC} leave efficient support for non-self-maintainable
derivatives for future work.
%Let's enjoy self-righteous self-bashing!

\pg{TODO: caches mostly do not contain actual intermediate results, but other
  caches; the only exception is for the ``leaves'', that is primitives.}
To avoid recomputation we must simply remember intermediate results as needed.
Executing |davg xs1 dxs1| will compute exactly the
same |s| and |n| as executing |avg xs1|, so we must just save and reuse them,
without needing to use memoization proper.
Hence, we CTS-convert each function |f| to a \emph{CTS function} |fC| and a \emph{CTS
derivative} |dfC|: CTS function |fC| produces, together with its final result, a
\emph{cache}, that the caller must pass to CTS derivative |dfC|. A cache is just a tuple of
values, containing information from subcalls---either inputs (as we explain in a
bit), intermediate results or
\emph{subcaches}, that is caches returned from further function calls.
%
In fact,
typically only primitive functions like |div| need to recall actual result;
automatically transformed functions only need to remember subcaches or inputs.
% Callers must be updated to remember
% the cache |c1| produced by CTS function |fC x| and pass it to \emph{CTS
%   derivative} |dfC|, invoked as |dfC x dx c1|.

% A first version of |avgC| and |davgC| in CTS is hence:
% \begin{code}
% data AvgC = AvgC SumC LengthC DivC
% avgC :: [Int] -> (Int, AvgC)

% avgC xs =
%   let  (s, cs1)  = sumC xs
%        (n, cn1)  = lengthC xs
%        (r, cr1)  = s `divC` n
%   in   (r, AvgC cs1 cn1 cr1)

% davgC :: [Int] -> Dt ^ [Int] -> AvgC -> (Dt ^ Int, AvgC)
% davgC xs dxs (AvgC cs1 cn1 cr1) =
%   let  (ds, cs2)  = dsumC xs dxs cs1
%        (dn, cn2)  = dlengthC xs dxs cn1
%        (dr, cr2)  = ddivC s ds n dn cr1
%        in   (dr, AvgC cs2 cn2 cr2)
% \end{code}
% %
CTS conversion is simplified by first converting to A'NF, where all results of
subcomputations are bound to variables: we just collect all caches in scope and
return them.
% it is easy to return caches for all
% subcomputation results when writing |avgC| and |davgC|: we just collect together
% all caches in scope.

As an additional step, we avoid always passing base inputs to derivatives by
defining |Dt^(A -> B) = Dt^A -> Dt^B|.
Instead of always passing a base input and possibly not using it, we can simply
assume that primitives whose derivative needs a base input store the input in
the cache.
%needing a base store it in the cache together with the needed intermediate results.

To make the translation uniform, we stipulate all functions in the program are
transformed to CTS, using a (potentially empty) cache. Since the
type of the cache for a function |f :: A -> B| depends on implementation of |f|, we
introduce for each function |f| a type for its cache |FC|, so that CTS function
|fC| has type |A -> (B, FC)| and CTS derivative |dfC| has type |Dt^A -> FC ->
(Dt^B, FC)|.

The definition of |FC| is only needed inside |fC| and |dfC|, and it can be
hidden in other functions to keep implementation details hidden in transformed
code; because of limitations of Haskell modules, we can only hide such
definitions from functions in other modules.

Since functions of the same type translate to functions of different types, the
translation does not preserve well-typedness in a higher-order language in
general, but it works well in our case studies
(\cref{sec:case-studies}); \cref{sec:incr-an-aver} shows how to map such functions. We
return to this point briefly in~\cref{sec:hiding-cache-type}.

%Using this variation, |avgC| stays the same but |davgC| becomes:
CTS-converting our example produces the following code:
\begin{code}
data AvgC = AvgC SumC LengthC DivC
avgC :: Bag Int -> (Int, AvgC)

avgC xs =
  let  (s, cs1)  = sumC xs
       (n, cn1)  = lengthC xs
       (r, cr1)  = s `divC` n
  in   (r, AvgC cs1 cn1 cr1)

davgC :: Dt ^ (Bag Int) -> AvgC -> (Dt ^ Int, AvgC)
davgC dxs (AvgC cs1 cn1 cr1) =
  let  (ds, cs2)  = dsumC dxs cs1
       (dn, cn2)  = dlengthC dxs cn1
       (dr, cr2)  = ddivC ds dn cr1
       in   (dr, AvgC cs2 cn2 cr2)
\end{code}

In the above program, |sumC| and |lengthC| are self-maintainable, that is they
need no base inputs and can be transformed to use empty caches. On the other
hand, |ddiv| is not self-maintainable, so we transform it to remember and use
its base inputs.
%Hence, we show an altered version of |div| called |divC| and the associated derivative |ddivC|:
\begin{code}
divC a b = (a `div` b, (a, b))
ddivC da db (a1, b1) =
  let  a2  = a1 `oplus` da
       b2  = b1 `oplus` db
  in   (div a2 b2 `ominus` div a1 b1, (a2, b2))
\end{code}
Crucially, |ddivC| must return an updated cache to ensure correct
incrementalization, so that application of further changes works correctly. In
general, if |(y, c1) = fC x| and |(dy, c2) = dfC dx c1|, then |(y `oplus` dy,
c2)| must equal the result of the base function |fC| applied to the new input |x
`oplus` dx|, that is |(y `oplus` dy, c2) = fC (x `oplus` dx)|.

Finally, to use these functions, we need to adapt the caller. Let's first show
how to deal with a sequence of changes: imagine that |dxs1| is a valid change
for |xs|, and that |dxs2| is a valid change for |xs `oplus` dxs1|. To update the
average for both changes, we can then call the |avgC| and |davgC| as follows:

\begin{code}
-- A simple example caller with two consecutive changes
avgDAvgC :: Bag Int -> Dt ^ (Bag Int) -> Dt ^ (Bag Int) ->
  (Int, Dt ^ Int, Dt ^ Int, AvgC)
avgDAvgC xs dxs1 dxs2 =
  let  (res1,   cache1) = avgC   xs
       (dres1,  cache2) = davgC  dxs1 cache1
       (dres2,  cache3) = davgC  dxs2 cache2
  in   (res1, dres1, dres2, cache3)
\end{code}
Incrementalization guarantees that the produced changes update the output
correctly in response to the input changes: that is, we have |res1 `oplus` dres1
= avg (xs `oplus` dxs1)| and |res1 `oplus` dres1 `oplus` dres2 = avg (xs `oplus`
dxs1 `oplus` dxs2)|. We also return the last cache to allow further updates to
be processed.

Alternatively, we can try writing a caller that gets an initial input and a
(lazy) list of changes, does incremental computation, and prints updated
outputs:
\begin{spec}
processChangeList (dxsN : dxss) yN cacheN = do
  let (dy, cacheN') = avg' dxsN cacheN
      yN' = yN `oplus` dy
  print yN'
  processChangeList dxss yN' cacheN'

-- Example caller with multiple consecutive
-- changes
someCaller xs1 dxss = do
  let (y1, cache1) = avgC xs1
  processChangeList dxss y1 cache1
\end{spec}
% XXX the subfunctions haven't been transformed yet.
% Explain WHAT THE HECK happened, in general.

More in general, we produce both an augmented base function and a derivative,
where the augmented base function communicates with the derivative by returning
a cache. The content of this cache are determined statically, and can be
accessed by tuple projections without any dynamic lookups; hence, we term the
approach \emph{static caching}.
% mention initial runs and incremental updates.

In the rest of the paper, we use the above idea to develop a correct
transformation that allows incrementalizing programs using static caching.

We'll return to this example in~\cref{sec:incr-an-aver}.
% XXX mention other contributions: prove correctness, show how to use it, evaluate it...

\subsection{A higher-order motivating example: nested loops}
\label{sec:higher-order-example}

Next, we consider differentiation with static caching on a minimal higher-order
example. To incrementalize this example, we enable detecting nil function
changes at runtime by representing function changes as closures that can be
inspected by incremental programs. We'll return to this example
in~\cref{sec:incr-nest-loop}.

We take an example of nested loops over sequences, implemented in terms of
standard Haskell functions |map| and |concat|. For simplicity, we compute the
Cartesian product of inputs:
\begin{code}
  cartesianProduct :: Sequence a -> Sequence b -> Sequence (a, b)
  cartesianProduct xs ys =
    concatMap (\x -> map (\y -> (x, y)) ys) xs
  concatMap f xs = concat (map f xs)
\end{code}
Computing |cartesianProduct xs ys| loops over each element |x| from sequence
|xs| and |y| from sequence |ys|, and produces a list of pairs |(x, y)|, taking
quadratic time $O(n^2)$ (we assume for simplicity that |size xs| and |size ys|
are both $O(n)$).
Adding a fresh element to either
|xs| or |ys| generates an output change containing $\Theta(n)$ fresh pairs:
hence derivative |dcartesianProduct| must take at least linear time. Thanks to
specialized derivatives |dmap| and |dconcat| for primitives |map| and |concat|,
|dcartesianProduct| has asymptotically optimal time complexity. To achieve this
complexity, |dmap f df| must detect when |df| is a nil function change and avoid
applying it to unchanged input elements.
% We consider \emph{total} derivatives, that is
% derivatives with respect to changes for all inputs. Hence,

To simplify the transformations we describe, we $\lambda$-lift
programs\pg{citation} before differentiating and transforming them.
\begin{code}
  cartesianProduct xs ys =
    concatMap (mapPair1 ys) xs

  mapPair1 ys = \x -> map (pair1 x) ys

  pair1 x = \y -> (x, y)

  concatMap f xs =
    let  yss = map f xs
    in   concat yss
\end{code}
\pg{show derivatives here? probably use already the caching variant.}
Suppose we add an element to either |xs| or |ys|.\pg{what about both?}
%Incrementalizing this program using ILC is not straightforward.
If change |dys| adds one element to |ys|, then |dmapPair1 ys dys|, the argument
to |dconcatMap|, is a non-nil function change taking constant time, so |dconcatMap|
must apply it to each element of |xs `oplus` dxs|.\pg{show reuse of previous results/caches.}

Suppose next that change |dxs| adds one element to |xs| and |dys| is a nil change
for |ys|. Then |dmapPair1 ys dys| is a nil function change. And we must detect
this dynamically.\pg{Why do we care about detection?}
If a function change |df : Dt ^ (A -> B)| is represented as a
function, and |A| is infinite, one cannot detect dynamically that it is a nil change.
To enable runtime nil change detection, we apply closure
conversion on function changes: a function change |df|, represented as a closure is
nil for |f| only if all environment changes it contains are also nil, and if the
contained function is a derivative of |f|'s function.

\input{formalization}



\section{Case studies}
\label{sec:case-studies}

In this section, we investigate whether our transformations incrementalize
efficiently programs in a typed language such as Haskell.
And indeed, after providing support for the needed bulk operations on sequences,
bags and maps, we successfully transform a few case studies and obtain efficient
incremental programs, that is ones for which incremental computation is faster
than from scratch recomputation.

We type CTS programs by by associating to each function |f| a cache type |FC|.
We can transform programs that use higher-order functions by making closure
construction explicit.

We illustrate those points on three case studies: average computation over bags of
integers, a nested loop over two sequences and a more involved example inspired
by \citeauthor{Koch14}'s work on incrementalizing database queries. 

In all cases, we confirm that results are consistent between from scratch
recomputation and incremental evaluation.

Our benchmarks were compiled by GHC 8.0.2. They were run on a 2.60GHz dual core
Intel i7-6600U CPU with 12GB of RAM running Ubuntu 16.04.

\subsection{Incrementalizing average computation over integers bags}
\label{sec:incr-an-aver}

Section \cref{sec:motivating-example} motivates our transformation with a
running example of computing the average over a bag of integers. 
We represent bags as maps from elements to (possibly negative) multiplicities.
Earlier work \citep{CaiEtAl2014ILC,Koch14} represents bag changes as bags
of removed and added elements: to update element |a| with change |da|, one removes
|a| and adds |a `oplus` da|. Instead, our bag changes contain element changes: a
valid bag change is either a replacement change (with a new bag) or a list of atomic
changes.
An atomic change contains an element |a|, a valid change for that element
|da|, a multiplicity |n| and a change to that multiplicity |dn|. Updating a bag
with an atomic change means removing |n| occurrences of |a| and
inserting |n `oplus` dn| occurrences of updated element |a `oplus` da|.
% Incremental functions can handle such changes
% In other representations, modifying an element
% when representing bag changes as
% bags of additions and removals~\citep{CaiEtAl2014ILC,Koch14}, element ch
% When represe
% In contrast to
% Compared to a representation of bag changes as bags as in
% \citet{CaiEtAl2014ILC} this representation allows us to represent changes to
% elements more directly making some programs more incremental.

\begin{code}
type Bag a = Map a Int
type Dt^(Bag a) = Replace (Bag a) | Ch [AtomicChange a]
data AtomicChange a = AtomicChange a (Dt^a) Int (Dt^Int)
\end{code}

This change type enables both users and derivatives to express efficiently various bag
changes, such as inserting a single element or changing a single element, but
also changing some but not all occurrences of an element in a bag.

\begin{code}
insertSingle :: a -> Dt^(Bag a)
insertSingle a = Ch [AtomicChange a (nil a) 0 (Ch 1)]

changeSingle :: a -> Dt^a -> Dt^(Bag a)
changeSingle a da = Ch [AtomicChange a da 1 (nil 1)]
\end{code}

Based on this change structure, we provide efficient primitives and their
derivatives. The CTS variant of |map|, that we call |mapC| takes a function
|fC| in CTS and a bag |as| and produces a bag and a cache. Because |map| is not
self-maintainable the cache stores the arguments |fC| and |as|. In addition the
cache stores for each invocation of |fC|, and therefore for each distinct element
in |as|, the result of |fC| of type |b| and the cache of type |c|.
The incremental function |dmapC| has to produce an
updated cache. We check that this is the same cache that |mapC| would produce
when applied to updated inputs using the QuickCheck library.

Following ideas inspired by~\citet{Rossberg2010fing}, all higher-order functions
(and typically, also their caches) are parametric over cache types of their
function arguments. Here, functions |mapC| and |dmapC| and cache type |MapCache|
are parametric over the cache type |c| of |fC| and |dfC|.
\begin{code}
map :: (a -> b) -> Bag a -> Bag b
type MapCache a b c = (a -> (b, c), Bag a, Map a (b, c))
mapC :: (a -> (b, c)) -> Bag a -> (Bag b, MapCache a b c)
dmapC :: (Dt^a -> c -> (Dt^b, c)) -> Dt^(Bag a) -> MapCache a b c -> (Dt^(Bag b), MapCache a b c)
\end{code}

We wrote the |length| and |sum| function used in our benchmarks in terms of
primitives |map| and |foldGroup|. We applied our transformations to get
|lengthC|, |dlengthC|, |sumC| and |dsumC|. This transformation could in
principle be automated. Implementing the CTS variant and CTS derivative of
primitives efficiently requires manual work.

%format dxNm1 = dx "_{n-1}"
%format xi = x "_i"
%format yi = y "_i"
%format dxi = dx "_i"
%format dyi = dy "_i"

We evaluate whether we can produce an updated result with |davgC| faster than
by from scratch recomputation with |avg|. We use the |criterion| library for
benchmarking. The benchmarking code and our raw results are available in the
supplementarty material. We fix an initial bag of size |n|. It contains the
integers
from |1| to |n|. We define a sequence of consecutive changes of length |r|
as the insertion of |1|, the deletion of |1|, the insertion of |2|, the deletion
of |2| and so on. We update the initial bag with these changes, one after
another, to obtain a sequence of input bags.

We measure the time taken by from scratch recomputation. We apply |avg| to
each input bag in the sequence and fully force all results. We report the time
from scratch recomputation takes as this measured time divided by the number |r|
of input bags. We measure the time taken by our CTS variant |avgC| similarly.
We make sure to fully force all results and caches |avgC| produces on the sequence
of input bags.

We measure the time taken by our CTS derivative |davgC|. We assume a fully
forced initial result and cache. We apply |davgC| to each change in the
sequence of bag changes using the cache from the previous invocation. We then
apply the result change to the previous result. We fully force the obtained
sequence of results. Finally we measure the time taken to only produce the sequence
of result changes without applying them.

Because of laziness, choosing what exactly to measure is tricky.
We ensure that reported times include the entire cost of computing the whole
sequence of results. To measure this cost, we ensure any thunks within the
sequence are forced. We need not force any partial results, such as output
changes or caches. Doing so would distort the results because forcing the whole
cache can cost asymptotically more than running derivatives. However, not using
the cache at all underestimates the cost of incremental computation. Hence, we
measure a sequence of consecutive updates, each using the cache produced by the
previous one.

\begin{figure}
  \footnotesize
  \begin{subfigure}[l]{0.45\linewidth}
  \begin{tikzpicture}
    \begin{axis}[
        width=\linewidth,
        height=\linewidth,
        xlabel=input size,
        ylabel=time in milliseconds,
        y filter/.code={\pgfmathparse{#1*1000}\pgfmathresult},
        legend pos=north west
      ]
      \addplot table[x=size, y=from_scratch, col sep=comma]{benchmark-results/average.csv};
      \addlegendentry{original}
      \addplot table[x=size, y=caching, col sep=comma]{benchmark-results/average.csv};
      \addlegendentry{caching}
      \addplot table[x=size, y=change_only, col sep=comma]{benchmark-results/average.csv};
      \addlegendentry{change only}
      \addplot table[x=size, y=incremental, col sep=comma]{benchmark-results/average.csv};
      \addlegendentry{incremental}
    \end{axis}
  \end{tikzpicture}
  \caption{Benchmark results for average}
  \label{fig:average-results}
\end{subfigure}
\hfill
\begin{subfigure}[r]{0.45\linewidth}
  \begin{tikzpicture}
    \begin{axis}[
        width=\linewidth,
        height=\linewidth,
        xlabel=input size,
        ylabel=time in milliseconds,
        y filter/.code={\pgfmathparse{#1*1000}\pgfmathresult},
        legend pos=north west
      ]
      \addplot table[x=size, y=from_scratch, col sep=comma]{benchmark-results/indexedJoin.csv};
      \addlegendentry{original}
      \addplot table[x=size, y=caching, col sep=comma]{benchmark-results/indexedJoin.csv};
      \addlegendentry{caching}
      \addplot table[x=size, y=change_only, col sep=comma]{benchmark-results/indexedJoin.csv};
      \addlegendentry{change only}
      \addplot table[x=size, y=incremental, col sep=comma]{benchmark-results/indexedJoin.csv};
      \addlegendentry{incremental}
    \end{axis}
  \end{tikzpicture}
  \caption{Benchmark results for totalPrice}
  \label{fig:indexedJoin-results}
\end{subfigure}
\end{figure}

The plot in \cref{fig:average-results} shows execution time versus the size
|n| of the initial input. To produce the initial result and cache, |avgC| takes
longer than the original |avg| function takes to produce just the result. This
is to be expected. Producing the result incrementally is much faster than from
scratch recomputation. This speedup increases with the size of the initial bag.
For an initial bag size of 800 incrementally updating the result is 70 times faster
than from scratch recomputation.

The difference between only producing the output change versus producing
the output change and updating the result is very small in this example. This is
to be expected because in this example the result is an integer and updating
and evaluating an integer is fast. We will see an example where there is a
bigger difference between the two.


\subsection{Incrementalizing a nested loop over two sequences}
\label{sec:incr-nest-loop}

We implemented incremental sequences and related primitives following \citet{Firsov2016purely}: our
change operations and first-order operations (such as |concat|) reuse their
implementation. On the other hand, we must extend higher-order operations such
as |map| to handle non-nil function changes and caching. A correct and efficient
CTS incremental |dmapC| function has to work differently depending on whether the
given function change is nil or not: For a non-nil function change it has to
go over the input sequence; for a nil function change it can avoid that.

\ps{Briefly describe change structure for sequences}

Consider the running example again, this time in A'NF. The partial application of
a lambda lifted function constructs a closure. We made that explicit with a
|closure| function.

\begin{code}
  cartesianProduct xs ys = let
    mapPair1Ys = closure mapPair1 ys
    xys = concatMap mapPair1Ys xs
    in xys

  mapPair1 ys = \x -> let
    pair1X = closure pair1 x
    xys = map pair1X ys
    in xys
\end{code}

While the only valid change for closed functions is their nil change, for closures
we can have non-nil function changes. We represent closed functions and closures
as variants of the same type. Correspondingly we represent changes to a closed
function and changes to a closure as variants of the same type of function changes.
We inspect this representation at runtime to find out if a function change
is a nil change.
We have evaluated another representation of function changes with different
tradeoffs where we use defunctionalization instead of closure conversion.

\begin{code}
  data Fun a b c where
    Closed :: (a -> (b, c)) -> Fun a b c
    Closure :: (e -> a -> (b, c)) -> e -> Fun a b c

  data Dt^(Fun a b c) where
    DClosed :: (Dt^a -> c -> (Dt^b, c)) -> Dt^(Fun a b c)
    DClosure :: (Dt^e -> Dt^a -> c -> (Dt^b, c)) -> Dt^e -> Dt^(Fun a b c)
\end{code}

We use the same benchmark setup as in the benchmark for the average computation on bags.
The input for size |n| is a pair of sequences |(xs, ys)|. Each sequence
initially contains the integers from |1| to |n|. Updating the result in reaction
to a change |dxs| to |xs| takes less time than updating the result in reaction
to a change |dys| to |ys|. The reason is that when |dys| is a nil change we
dynamically detect that the function change passed to |dconcatMapc| is the nil
change and avoid looping over |xs| entirely.

We benchmark changes to the outer sequence |xs| and the inner sequence |ys|
separately. In both cases the sequence of changes are insertions and deletions of
different numbers at different positions.
When we benchmark changes to the outer sequence |xs|
we take this sequence of changes for |xs| and all changes to |ys| will be nil
changes. When we benchmark changes to the inner sequence |ys| we take this sequence
of changes for |ys| and all changes to |xs| will be nil changes.

\begin{figure}
  \footnotesize
  \begin{subfigure}[l]{0.45\linewidth}
  \begin{tikzpicture}
    \begin{axis}[
        width=\linewidth,
        height=\linewidth,
        xlabel=input size,
        ylabel=time in seconds,
        legend pos=north west
      ]
      \addplot table[x=size, y=from_scratch, col sep=comma]{benchmark-results/nestedLoopInner.csv};
      \addlegendentry{original}
      \addplot table[x=size, y=caching, col sep=comma]{benchmark-results/nestedLoopInner.csv};
      \addlegendentry{caching}
      \addplot table[x=size, y=change_only, col sep=comma]{benchmark-results/nestedLoopInner.csv};
      \addlegendentry{change only}
      \addplot table[x=size, y=incremental, col sep=comma]{benchmark-results/nestedLoopInner.csv};
      \addlegendentry{incremental}
    \end{axis}
  \end{tikzpicture}
  \caption{Benchmark results for cartesian product changing \emph{inner} sequence.}
  \label{fig:nestedLoopInner-results}
\end{subfigure}
\hfill
\begin{subfigure}[r]{0.45\linewidth}
  \begin{tikzpicture}
    \begin{axis}[
        width=\linewidth,
        height=\linewidth,
        xlabel=input size,
        ylabel=time in seconds,
        legend pos=north west
      ]
      \addplot table[x=size, y=from_scratch, col sep=comma]{benchmark-results/nestedLoopOuter.csv};
      \addlegendentry{original}
      \addplot table[x=size, y=caching, col sep=comma]{benchmark-results/nestedLoopOuter.csv};
      \addlegendentry{caching}
      \addplot table[x=size, y=change_only, col sep=comma]{benchmark-results/nestedLoopOuter.csv};
      \addlegendentry{change only}
      \addplot table[x=size, y=incremental, col sep=comma]{benchmark-results/nestedLoopOuter.csv};
      \addlegendentry{incremental}
    \end{axis}
  \end{tikzpicture}
  \caption{Benchmark results for Cartesian product changing \emph{outer} sequence.}
  \label{fig:nestedLoopOuter-results}
\end{subfigure}
\end{figure}

In this example preparing the cache takes much longer than from scratch
recomputation. The speedup of incremental computation over from scratch
recomputation increases with the size of the initial sequences. It reaches
|2.5| for a change to the inner sequences and |8.8| for a change to the outer
sequence when the initial sequences have size |800|. Producing and fully forcing
only the changes to the results is |5| times faster for a change to the inner
sequence and |370| times faster for a change to the outer sequence.

While we do get speedups for both kinds of
changes (to the inner and to the outer sequence) the speedups for changes to the
outer sequence are bigger.
Due to our benchmark methodology we have to fully force updated results. This alone
takes time quadratic in the size of the input sequences |n|. Threrefore we also
report the time it takes to produce and fully force only the output changes which
is of a lower time complexity.


\subsection{Incrementalizing an indexed join of two bags}
\label{sec:incr-an-index}

As expected, we found that we can compose functions into larger and more complex programs and
apply CTS differentiation to get a fast incremental program.

For this example imagine we have a bag of orders and a bag of line items. An
order is a pair of an integer key and an exchange rate represented as an integer.
A line item is a pair of a key of a corresponding order and a price represented
as an integer. The price of an order is the sum of the prices of the
corresponding line items multiplied by the exchange rate. We want to find the
total price defined as the sum of the prices of all orders.

To do so efficiently we build an index for line items and an index for orders.
We represent indexes as maps. We build a map from order key to the sum of the
prices of corresponding line items. Because orders are not necessarily unique
by key and because multiplication distributes over addition we can build an index
mapping each order key to the sum of all exchange rates for this order key.
We then compute the total price by merging the two maps by key, multiplying
corresponding sums of exchange rates and sums of prices. We compute the total
price as the sum of those products.

Because our indexes are maps we need a change structure for maps. We generalize
the change structure for bags by generalizing from multiplicities to arbitrary
values as long as they have a group structure. A change to a map is either a
replacement change (with a new map) or a list of atomic changes. An atomic
change is a key |k|, a valid change to that key |dk|, a value |a| and a valid
change to that value |da|. To update a map with an atomic change means to use
the group structure of the type of |a| to subtract |a| at key |k| and to add |a
`oplus` da| at key |k `oplus` dk|.

\begin{code}
type Dt^(Map k a) = Replace (Map k a) | Ch [AtomicChange k a]
data AtomicChange k a = AtomicChange k (Dt^k) a (Dt^a)
\end{code}

Bags have a group structure as long as the elements have a group structure. Maps
have a group structure as long as the values have a group structure. This means
for example that we can efficiently incrementalize programs on maps from keys
to bags of elements. We implemented efficient caching and incremental primitives
for maps and verified their correctness with QuickCheck.

To build the indexes we use a |groupBy| function that we built from primitive
functions |foldMapGroup| on bags and primitive |singleton| functions for bags
and maps respectively. While computing the indexes with |groupBy| is
self-maintainable, merging them is not. We need to cache and incrementally
update the intermediately created indexes to avoid recomputing them.

\begin{code}
type Order = (Int, Int)
type LineItem = (Int, Int)

totalPrice :: Bag Order -> Bag LineItem -> Int
totalPrice orders lineItems = let
  orderIndex = groupBy fst orders
  orderSumIndex = Map.map (Bag.foldMapGroup snd) orderIndex
  lineItemIndex = groupBy fst lineItems
  lineItemSumIndex = Map.map (Bag.foldMapGroup snd) lineItemIndex
  merged = Map.merge orderSumIndex lineItemSumIndex
  total = Map.foldMapGroup multiply merged
  in total
\end{code}

This example is inspired by \citet{Koch14}.
%
Unlike them, we don't automate indexing, so to get good performance we start
from a program that explicitly uses indexes.
% While indexing arise automatically
% from their transformations,
% to get good performance we must start from a program
% that explicitly uses indexes

We evaluate the performace in the same way we did for the average computation on bags. The
initial input of size |n| is a pair of bags where both contain the pairs
|(i, i)| for |i| between |1| and |n|. The sequence of changes are alternations
between insertion and deletion of pairs |(j, j)| for different |j|. We
alternate the insertions and deletions between the orders bag and the line items
bag.

Our CTS derivative of the original program produces updated results much faster
than from scratch recomputation and again the speedup increases with the size
of the initial bags. For an initial size of the two bags of |800|
incrementally updating the result is 180 times faster than from scratch
recomputation.


\subsection{Limitations and future work}
% Knowing myself, I'm probably doing this too much.
In this section we describe limitations to be addressed in future work.

\pg{Commenting this out, don't believe it any more in general. Unless we
  do a group fold, we need to run |`ominus`|!}
% \subsubsection{Inductive data types and structural recursion}

% We believe that we can extend our transformation to work with folds over inductive
% data types.
% Derivatives for folds still need be written by hand, but mainly to handle
% structural insertions or deletions; value changes can be handled by the main
% transformation.
% General recursive functions induce recursive cache types.

% DOES THIS MEAN WE NEVER NEED ANY MAINTENANCE? Probably not. But where do we fail?

  % XXX no idea how to actually explain this, so don't at this point.

  % but only for one
  % reason. When our tree undergoes a structural change, such as inserting an
  % element, existing elements can be shuffled around. Intermediate results must
  % be shuffled around in a corresponding way.

% \paragraph{Associative incremental folds}
% Associative folds are a common case study in incremental literature; we don't
% claim this example is original. However, many implementations mix intermediate
% results for \emph{a single fold} together with the input finger tree, as
% described even by Cormen (2nd ed., Ch. 14). Our implementation stores results in
% a separate parallel tree, and thus allows performing different computations
% \emph{modularly}, without modifying the input tree.

% % unclear
% %This is only possible because we update input and cache in lockstep.
% \ps{Note it here so we don't forget to say a few words}


% pg: We say enough earlier, re expressiveness.
% \subsubsection{Incremental programs on sum types}

% We believe that our transformation can be extended to work on programs that
% use sum types. For example a change structure for |Either| could be

% \begin{code}
%   data Dt (Either a b) =
%     ChangeLeft a (Dt a) |
%     ChangeLeftToRight a b |
%     ChangeRight b (Dt b) |
%     ChangeRightToLeft b a
% \end{code}

% When a value changes from |Left a| to |Right b| we would use |`ominus`| to
% produce a change in the result. Every change structure can support |`ominus`|
% by adjoining a replacement change. In this case a change from |Left a| to
% |Right b| would trigger recomputation.
% \ps{Just some notes}


\subsubsection{Hiding the cache type}
\label{sec:hiding-cache-type}
%\ps{A limitation that the defunctionalization solution did not have}

In our experiments, functions of the same type |f1, f2 :: A -> B| can be
transformed to CTS functions |f1 :: A -> (B, C1), f2 :: A -> (B, C2)| with
different cache types |C1, C2|, since cache types depend on the implementation.
We can fix this problem with some runtime overhead by using a single cache type |Cache|,
defined as a tagged union of all cache types. If we defunctionalize function
changes, we can index this cache type with tags representing functions, but
other approaches are possible and we omit details.
We conjecture (but have not proven) this fix gives a type-preserving
translation, but leave this question for future work.
% indexed by a GADT representing the different
% functions in the program (similarly to defunctionalized functions)~\citep{GiarrussoPhD2017}.

% Our transformation adds the type of the cache to function types. It possibly
% transforms functions with equal type to functions with different types. This
% means that our transformation makes some well-typed programs ill-typed.

% For example we can't in general store functions in a homogeneous collection.

% Another example:

% \begin{code}
%   selectFirst :: (a -> b) -> (a -> b) -> (a -> b)
%   selectFirst f g = f
% \end{code}

% \ps{This becomes more limiting with ifthenelse}
% \ps{Just noting it}


\subsubsection{Nested bags}

Our implementation of bags makes nested bags overly slow: we represent bags as
tree-based maps from elements to multiplicity, so looking up a bag |b| in a bag
of bags takes time proportional to the size of |b|. Possible solutions in this
case include shredding, like done by \citep{Koch2016incremental}. We have no
such problem for nested sequences, or other nested data which can be addressed
in $O(1)$.
% the element size
% % The presented language plugin for bags is less efficient on nested bags than
% % it could be:
% The tree-based implementation of maps that we rely on compares keys (in this case
% bag elements) for insert and lookup. If the elements themselves are bags, this
% comparison is rather slow.
%
% We believe that another implementation based on hashmaps together with hash-consing
% could solve this problem.
% \ps{Handwavy, just noting}


\subsubsection{Proper tail calls}
\label{sec:tail-calls}
CTS transformation conflicts with proper tail calls, as it turns most tail calls
into non-tail calls.
In |A'NF| syntax, tail calls such as |let y = f x in g y| become |let y = f x in
let z = g y in z|, and in CTS that becomes |let (y, c_y) = f x in let (z, c_z) =
g y in (z, (c_y, c_z))|, where the call to |g| is genuinely \emph{not} in tail
position.
% An optimizer could still restore some tail calls, turning e.g. |let (y, c_y) = f
% x in (y, c_y)| back into |f x|.
This prevents recursion on deeply nested data structures like long lists: but such
programs incrementalize inefficiently if deeply nested data is affected, so
it is advisable to replace lists by other sequences anyway. It's unclear whether
such fixes are available for other uses of tail calls.
% \pg{Which ones? I can only think of CPS but CTS-transforming a CPS program as
% a normal one makes no sense.}

\subsubsection{Pervasive replacement values}
\label{sec:annoying-replacement}
Thanks to replacement changes, we can compute a change from any |v1| to any |v2|
in constant time. \citet{CaiEtAl2014ILC} use a difference operator |`ominus`| instead, but
it's hard to implement |`ominus`| in constant time on values of non-constant size.
So our formalization and implementation allow replacement values everywhere to
ensure all computations can be incrementalized in some sense.
Supporting replacement changes introduces overhead even if they are not used,
because it prevents writing self-maintainable CTS derivatives. Hence, to improve
performance, one should consider dropping support for replacement values and
restricting supported computations.
Consider a call to a binary CTS derivative |dfc da db c1| after computing |(y1,
c1) = fc a1 b1|: if |db| is a replacement change |!b2|, then |dfc| must compute
a result afresh by invoking |fc a2 b2|, and |a2 = a1 `oplus` da| requires
remembering previous input |a1| inside |c1|. By the same argument, |c1| must
also remember input |b1|. Worse, replacement values are only needed to handle
cases where incremental computation reduces to recomputation, because the new
input is completely different, or because the condition of an |if| expression
changed. Such changes to conditions are forbidden by other
works~\citep{Koch2016incremental}, we believe for similar reasons.

\subsubsection{Cache pruning via absence analysis}
\label{sec:cache-pruning}
To reduce memory usage and runtime overhead, it should be possible to
automatically remove from transformed programs any caches or cache fragments
that are not used (directly or indirectly) to compute outputs. \Citet{Liu00}
performs this transformation on CTS programs by using
\emph{absence analysis}, which was later extended to higher-order languages by
\citet{Sergey2014modular}. In lazy languages, absence analysis removes thunks
that are not needed to compute the output. We conjecture that, as long as the
analysis is extended to \emph{not} treat caches as part of the output, it should
be able to remove unused caches or inputs (assuming unused inputs exist, see
\cref{sec:annoying-replacement}).
% shown how to approach the problem for first-order languages by a first-order
% static analysis called \emph{absence analysis}, and because this analysis was
% later extended to higher-order languages by \citet{Sergey2014modular}.
% In a lazy
% program, \emph{absence analysis} identifies thunks that are not going to be
% evaluated, so that they can be later removed. As long as the cache is treated as
% a product of thunks (or \emph{negative product}), absence analysis can be
% applied directly to find out which intermediate results can be dropped.

% But GHC's implementation of absence analysis and optimizations appears to not
% remove unused intermediate results from caches (or even to detect that such
% results are unused). We conjecture the analysis is not aware that the cache is
% only shared between functions |fc| and derivatives |df| (even if we
% enforce that through existential types, or by avoiding the cache ever being
% returned).
% Such removal already happens when the functions are suitably combined
% together, %PG show example, clarify it is rather limited.
% so we are satisfied with leaving this for future work.


\subsubsection{Unary vs n-ary abstraction}
\label{sec:nary-abstraction}
We only show our transformation correct for unary functions and tuples. But many
languages provide efficient support for applying curried functions such as |div :: Int ->
Int -> Int|, via either the \emph{push-enter} or \emph{eval-apply} evaluation
model. For instance, invoking |div m n| should not require the overhead of a
function invocation for each argument~\citep{Marlow2006making}. Naively
transforming such a curried functions to CTS would produce a function |divc| of
type |Int -> (Int -> (Int, DivC2)), DivC1)| with |DivC1 = ()|, which adds
excessive overhead.%
\footnote{In \cref{sec:motivation} and our evaluation we use curried functions
and never need to use this naive encoding, but only because we always invoke
functions of known arity.}
Based on preliminary experiments, we believe we can straightforwardly combine our
approach with a push-enter or eval-apply evaluation strategy for
transformed curried functions. Alternatively, we expect that translating
Haskell to Strict Core~\citep{Bolingbroke2009types} would take care of turning
Haskell into a language where function types describe their arity, which our
transformation can easily take care of.
We leave a more proper investigation for future work.

\section{Related work}
\label{sec:rw}
Among all research on incremental computation in both programming languages and
databases~\citep{Gupta99MMV,Ramalingam93} we discuss the most closely related works.

\paragraph{Previous work on cache-transfer-style}
\citet{Liu00}'s work has been the fundamental inspiration to this work, but
her approach has no correctness proof and is restricted to a first-order untyped
language (in part because no absence analysis for higher-order languages was
available). Moreover, while the idea of cache-transfer-style is similar, it's
unclear if her approach to incrementalization would extend to higher-order
programs.
% while her approach to absence analysis was based on available
% technology that did not extend to higher-order programs unlike
% \citet{Sergey2014modular}'s.

\citet{Firsov2016purely} also approach incrementalization by code
transformation, but their approach does not deal with changes to functions.
Instead of transforming functions written in terms of primitives, they provide
combinators to write CTS functions and derivatives together. On the other hand,
they extend their approach to support mutable caches, while restricting to
immutable ones as we do might lead to a logarithmic slowdown.

\paragraph{Finite differencing}
Incremental computation on collections or databases by finite differencing has a long
tradition~\citep{Paige82FDC,Blakeley:1986:EUM}. The most recent and
impressive line of work is the one on DBToaster~\citep{Koch10IQE,Koch14}, which
is a highly efficient approach to incrementalize queries over bags by combining
iterated finite differencing with other program transformations. They show
asymptotic speedups both in theory and through experimental evaluations.
Changes are only allowed for datatypes that form groups (such as bags or certain
maps), but not for instance for lists or sets. Similar ideas were recently
extended to higher-order and nested computation~\citep{Koch2016incremental},
though still restricted to datatypes that can be turned into groups.
% DBToaster relies on iterated differentiation to

% Like
\paragraph{Logical relations}
To study correctness of incremental programs we use a logical relation among
initial values |v1|, updated values |v2| and changes |dv|.
To define a logical relation for an untyped $\lambda$-calculus we use a
\emph{step-indexed} logical relation,
following~\citep{Appel01,Ahmed2006stepindexed};
in particular, our definitions are closest to the ones by \citet{Acar08}, who
also works with an untyped language, big-step semantics and (a different form
of) incremental computation. However, their logical relation does not mention
changes explicitly, since they do not have first-class status in their system.
Moreover, we use environments rather than substitution, and use a slightly
different step-indexing for our semantics.

% \paragraph{Other work not using change structures}

% in other approaches, a change for an atomic value |a1| simply describes an
% atomic value |a1| replacing it.
% %Self-adjusting computation
% In ILC, we can define changes for |a1 :: A| using a richer language, but the richer
% this language is, the more effort is needed to perform case analysis on it. This
% affects derivatives of primitives handling changes of type |Dt ^ T|.
% % there is a tension between  tradeoff between

% % A precedent is used by
% % \citet{Cicek2016type} to study a type system that describes complexity of
% % self-adjusting computation in the presence of control flow changes during
% % incremental evaluation.

\paragraph{Dynamic incrementalization}
The approaches to incremental computation with the widest applicability are
in the family of self-adjusting computation~\citep{Acar05,Acar09}, including its
descendant Adapton \citep{Hammer2014adapton}.
These approaches incrementalize programs by combining memoization and change
propagation: after creating a trace of base computations, updated inputs are
compared with old ones in $O(1)$ to find corresponding outputs, which are
updated to account for input modifications. Compared to self-adjusting
computation, Adapton only updates results when they are demanded. As usual,
incrementalization is not efficient on arbitrary programs.
To incrementalize efficiently a program must be designed so that input changes
produce small changes to the computation trace; refinement type systems have
been designed to assist in this task~\citep{Cicek2016type,Hammer2016typeda}.
Instead of comparing inputs by pointer equality, Nominal
Adapton~\citep{Hammer2015} introduces first-class labels to identify matching
inputs, enabling reuse in more situations.

Recording traces has often significant overheads in both space and time
(slowdowns of ~20-30$\times$ are common), though
\citet{Acar10TDT} alleviate that by with datatype-specific support for tracing
higher-level operations, while \citet{Chen2014} reduce that overhead by
optimizing traces to not record redundant entries, and by logging chunks of
operations at once, which reduces memory overhead but also potential speedups.

\section{Conclusions}
\label{sec:conclusions}

We have presented a program transformation which turns a functional
program into its derivative and efficiently shares redundant
computations between them thanks to a statically computed
cache. Although our first practical case studies show promising
results, it remains now to integrate this transformation into a
realistic compiler.

% \acks
% % OMIT in blinded version.
% We thank Cai Yufei, Tillmann Rendel, Lourdes del Carmen González Huesca, Klaus
% Ostermann, Sebastian Erdweg, ... for helpful discussions on this project.


\bibliography{../Bibs/ProgLang,../Bibs/DB,../Bibs/own,../Bibs/SoftEng}

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
