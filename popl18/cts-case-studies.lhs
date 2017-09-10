% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes-popl.fmt

\section{Incrementalization case studies}
\label{sec:case-studies}
\label{sec:cts-case-studies}.

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

\subsection{Averaging integers bags}
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
function arguments. Here, functions |mapC| and |dmapC| and cache type |MapC|
are parametric over the cache type |c| of |fC| and |dfC|.
\begin{code}
map :: (a -> b) -> Bag a -> Bag b

type MapC a b c = (a -> (b, c), Bag a, Map a (b, c))
mapC :: (a -> (b, c)) -> Bag a -> (Bag b, MapC a b c)
dmapC :: (Dt^a -> c -> (Dt^b, c)) -> Dt^(Bag a) ->
  MapC a b c -> (Dt^(Bag b), MapC a b c)
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
  \begin{subfigure}[l]{0.495\linewidth}
  \begin{tikzpicture}
    \begin{axis}[
        width=\linewidth,
        height=\linewidth,
        xlabel=input size,
        ylabel=time in milliseconds,
        y filter/.code={\pgfmathparse{#1*1000}\pgfmathresult},
        legend pos=north west
      ]
      \addplot table[x=size, y=from_scratch, col sep=comma]{\poplPath{benchmark-results/average.csv}};
      \addlegendentry{original}
      \addplot table[x=size, y=caching, col sep=comma]{\poplPath{benchmark-results/average.csv}};
      \addlegendentry{caching}
      \addplot table[x=size, y=change_only, col sep=comma]{\poplPath{benchmark-results/average.csv}};
      \addlegendentry{change only}
      \addplot table[x=size, y=incremental, col sep=comma]{\poplPath{benchmark-results/average.csv}};
      \addlegendentry{incremental}
    \end{axis}
  \end{tikzpicture}
  \caption{Benchmark results for |avg|}
  \label{fig:average-results}
\end{subfigure}
\hfill
\begin{subfigure}[r]{0.495\linewidth}
  \begin{tikzpicture}
    \begin{axis}[
        width=\linewidth,
        height=\linewidth,
        xlabel=input size,
        ylabel=time in milliseconds,
        y filter/.code={\pgfmathparse{#1*1000}\pgfmathresult},
        legend pos=north west
      ]
      \addplot table[x=size, y=from_scratch, col sep=comma]{\poplPath{benchmark-results/indexedJoin.csv}};
      \addlegendentry{original}
      \addplot table[x=size, y=caching, col sep=comma]{\poplPath{benchmark-results/indexedJoin.csv}};
      \addlegendentry{caching}
      \addplot table[x=size, y=change_only, col sep=comma]{\poplPath{benchmark-results/indexedJoin.csv}};
      \addlegendentry{change only}
      \addplot table[x=size, y=incremental, col sep=comma]{\poplPath{benchmark-results/indexedJoin.csv}};
      \addlegendentry{incremental}
    \end{axis}
  \end{tikzpicture}
  \caption{Benchmark results for |totalPrice|}
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


\subsection{Nested loops over two sequences}
\label{sec:incr-nest-loop}

We implemented incremental sequences and related primitives following \citet{Firsov2016purely}: our
change operations and first-order operations (such as |concat|) reuse their
implementation. On the other hand, we must extend higher-order operations such
as |map| to handle non-nil function changes and caching. A correct and efficient
CTS incremental |dmapC| function has to work differently depending on whether the
given function change is nil or not: For a non-nil function change it has to
go over the input sequence; for a nil function change it can avoid that.

\ps{Briefly describe change structure for sequences}

Consider the running example again, this time in A'NF\@@. The partial application of
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
\begin{code}
  data Fun a b c where
    Closed :: (a -> (b, c)) -> Fun a b c
    Closure :: (e -> a -> (b, c)) -> e -> Fun a b c

  data Dt^(Fun a b c) where
    DClosed :: (Dt^a -> c -> (Dt^b, c)) -> Dt^(Fun a b c)
    DClosure :: (Dt^e -> Dt^a -> c -> (Dt^b, c)) -> Dt^e -> Dt^(Fun a b c)
\end{code}

We have also evaluated another representation of function changes with different
tradeoffs where we use defunctionalization instead of closure conversion.
\begin{poplForThesis}
We discuss the use of defunctionalization in \cref{ch:defunc-fun-changes}.
\end{poplForThesis}

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
  \begin{subfigure}[l]{0.495\linewidth}
  \begin{tikzpicture}
    \begin{axis}[
        width=\linewidth,
        height=\linewidth,
        xlabel=input size,
        ylabel=time in seconds,
        legend pos=north west
      ]
      \addplot table[x=size, y=from_scratch, col sep=comma]{\poplPath{benchmark-results/nestedLoopInner.csv}};
      \addlegendentry{original}
      \addplot table[x=size, y=caching, col sep=comma]{\poplPath{benchmark-results/nestedLoopInner.csv}};
      \addlegendentry{caching}
      \addplot table[x=size, y=change_only, col sep=comma]{\poplPath{benchmark-results/nestedLoopInner.csv}};
      \addlegendentry{change only}
      \addplot table[x=size, y=incremental, col sep=comma]{\poplPath{benchmark-results/nestedLoopInner.csv}};
      \addlegendentry{incremental}
    \end{axis}
  \end{tikzpicture}
  \caption{Benchmark results for cartesian product changing \emph{inner} sequence.}
  \label{fig:nestedLoopInner-results}
\end{subfigure}
\hfill
\begin{subfigure}[r]{0.495\linewidth}
  \begin{tikzpicture}
    \begin{axis}[
        width=\linewidth,
        height=\linewidth,
        xlabel=input size,
        ylabel=time in seconds,
        legend pos=north west
      ]
      \addplot table[x=size, y=from_scratch, col sep=comma]{\poplPath{benchmark-results/nestedLoopOuter.csv}};
      \addlegendentry{original}
      \addplot table[x=size, y=caching, col sep=comma]{\poplPath{benchmark-results/nestedLoopOuter.csv}};
      \addlegendentry{caching}
      \addplot table[x=size, y=change_only, col sep=comma]{\poplPath{benchmark-results/nestedLoopOuter.csv}};
      \addlegendentry{change only}
      \addplot table[x=size, y=incremental, col sep=comma]{\poplPath{benchmark-results/nestedLoopOuter.csv}};
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


\subsection{Indexed joins of two bags}
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

To build the indexes, we use a |groupBy| function built from primitive
functions |foldMapGroup| on bags and |singleton| for bags
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


\iftoggle{poplForThesis}{\section}{\subsection}{Limitations and future work}
\iftoggle{poplForThesis}{\let \limSection = \subsection}{\let \limSection = \subsubsection}
\label{sec:cts-limitations}
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


\limSection{Hiding the cache type}
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


\limSection{Nested bags}

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


\limSection{Proper tail calls}
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

\limSection{Pervasive replacement values}
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

%New in the thesis, include in paper?
\begin{poplForThesis}
\limSection{Recomputing updated values}
\label{sec:cts-limit-reupdate}
In some cases, the same updated input might be recomputed more than once.
If a derivative |df| needs some base input |x| (that is, if |df| is not
self-maintainable), |df|'s input cache will contain a copy of |x|, and |df|'s
output cache will contain its updated value |x `oplus` dx|. When all or most
derivatives are self-maintainable this is convenient, because in most cases
updated inputs will not need to be computed. But if most derivatives are not self-maintainable, the same updated input might be computed multiple times: specifically,
if derivative |dh| calls functions |df| and |dg|, and both |df| and |dg| need
the same base input |x|, caches for both |df| and |dg| will contain the updated
value of |x `oplus` dx|, computed independently. Worse, because of pervasive
replacement values (\cref{sec:annoying-replacement}), derivatives in our case
studies tend to not be self-maintainable.
%On the other hand, it appears that the slowdown factor is a function of the program text,
% Not clear: a loop calling |df| will recompute |x `oplus` dx| once per iteration.

In some cases, such repeated updates should be removable by a standard optimizer
after inlining and common-subexpression elimination, but it is unclear how often this happens.
To solve this problem, derivatives could take and return both old inputs |x1|
and updated ones |x2 = x1 `oplus` dx|, and |x2| could be computed at the single
location where |dx| is bound. In this case, to avoid updates for unused base
inputs we would have to rely more on absence analysis
(\cref{sec:cache-pruning}); pruning function inputs appears easier than pruning
caches. Otherwise, computations of updated inputs that are not used, in a lazy
context, might cause space leaks, where thunks for |x2 = x1 `oplus` dx1|, |x3 =
x2 `oplus` dx2| and so on might accumulate and grow without bounds.
\end{poplForThesis}

\limSection{Cache pruning via absence analysis}
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


\limSection{Unary vs n-ary abstraction}
\label{sec:nary-abstraction}
We only show our transformation correct for unary functions and tuples. But many
languages provide efficient support for applying curried functions such as |div :: Int ->
Int -> Int|, via either the \emph{push-enter} or \emph{eval-apply} evaluation
model. For instance, invoking |div m n| should not require the overhead of a
function invocation for each argument~\citep{Marlow2006making}. Naively
transforming such a curried functions to CTS would produce a function |divc| of
type |Int -> (Int -> (Int, DivC2)), DivC1)| with |DivC1 = ()|, which adds
excessive overhead.%
\footnote{In \cref{sec:cts-motivation} and our evaluation we use curried functions
and never need to use this naive encoding, but only because we always invoke
functions of known arity.}
Based on preliminary experiments, we believe we can straightforwardly combine our
approach with a push-enter or eval-apply evaluation strategy for
transformed curried functions. Alternatively, we expect that translating
Haskell to Strict Core~\citep{Bolingbroke2009types} would take care of turning
Haskell into a language where function types describe their arity, which our
transformation can easily take care of.
We leave a more proper investigation for future work.
