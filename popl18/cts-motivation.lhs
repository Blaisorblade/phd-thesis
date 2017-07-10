% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes-popl.fmt

\section{Introducing Cache-Transfer Style}
\label{sec:cts-motivation}
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
|A|, and an \emph{update operator} |`oplus` :: A -> Dt^A -> A|, that updates an
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
As in all approaches to incrementalization (see \cref{sec:cts-rw}), one cannot
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
If a function change |df :: Dt ^ (A -> B)| is represented as a
function, and |A| is infinite, one cannot detect dynamically that it is a nil change.
To enable runtime nil change detection, we apply closure
conversion on function changes: a function change |df|, represented as a closure is
nil for |f| only if all environment changes it contains are also nil, and if the
contained function is a derivative of |f|'s function.
