% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{A tour of differentiation examples}
\label{ch:diff-examples}
Before formalizing ILC, we show more example of change structures and
primitives, to show (a) designs for reusable primitives and their
derivatives, (b) to what extent we can incrementalize basic building
blocks such as recursive functions and algebraic data types, and (c) to sketch how
we can incrementalize collections efficiently. We make no attempt at
incrementalizing a complete collection API here; we discuss briefly more
complete implementations in \cref{sec:applying} and \cref{sec:case-studies}.

To describe these examples informally, we use Haskell notation and
|lett| polymorphism as appropriate (see \cref{sec:intro-stlc}).
% We already sketch, how a change structure
% can be represented in Haskell terms:

We also motivate a few extensions to differentiation that we describe later. As
we'll see in this chapter, we'll need to enable some forms of introspection on
function changes to manipulate the embedded environments, as we discuss in
\cref{ch:defunc-fun-changes}. We will also need ways to remember intermediate
results, which we will discuss in \cref{part:caching} (in particular
\cref{ch:cts}).
We will also use overly simplified change structures to illustrate a few points.

\section{Change structures as type-class instances}
We encode change structures, as sketched earlier in \cref{sec:change-intro},
through a \emph{type class} named |ChangeStruct|. An instance |ChangeStruct t|
defines a change type |Dt^t| as an associated type and operations |`oplus`|,
|`ominus`| and |`ocompose`| are defined as methods. We also define method
|oreplace|, such that |oreplace v2| produces a \emph{replacement change} from
any source to |v2|; by default, |v2 `ominus` v1| is simply an alias for
|oreplace v2|.
\begin{code}
class ChangeStruct t where
  type Dt^t
  oplus :: t -> Dt^t -> t
  oreplace :: t -> Dt^t
  ominus :: t -> t -> Dt^t
  v2 `ominus` v1 = oreplace v2
  (`ocompose`) :: Dt^t -> Dt^t -> Dt^t
  nilc :: t -> Dt^t
\end{code}
In this chapter we will
often show change structures where only some methods are defined; in actual
implementations we use a type class hierarchy to encode what operations are
available, but we collapse this hierarchy here to simplify presentation.
% We'll come back to this definition and refine it,
% describing the laws it satisfies, in \cref{sec:change-struct-tc}.

\pg{Too short for a section. Add sums and products maybe?}
\section{How to design a language plugin}
\label{sec:plugin-design}

When adding support for a datatype |T|, we will strive to
define both a change structure and derivatives of introduction and
elimination forms for |T|, since such forms constitute a complete API
for using that datatype. However, we will sometimes have to restrict
elimination forms to scenarios that can be incrementalized efficiently.

\pg{Put somewhere:}
In general, to differentiate a primitive |f : A -> B| once we have defined a
change structure for |A|, we can start by defining
\begin{equation}
  \label{eq:diff-primitive-eq-reasoning}
  |df a1 da = f (a1 `oplus` da) `ominus` f a1|,
\end{equation}
where |da| is a valid change from |a1| to |a2|. We then try to
simplify and rewrite the expression using \emph{equational reasoning}, so that it does
not refer to |`ominus`| any more, as far as possible. We can assume that all
argument changes are valid, especially if that allows producing faster
derivatives; we formalize equational reasoning for valid changes in
\cref{sec:denot-equivalence-valid}.
In fact, instead of defining |`ominus`| and simplifying |f a2 `ominus` f a1| to
not use it, it is sufficient to produce a change from |f a1| to |f a2|, even a
different one. We write |da1 `doe` da2| to mean that changes |da1| and |da2| are
equivalent, that is they have the same source and destination. We define this
concept properly in~\cref{sec:change-equivalence}.

We try to avoid running |`ominus`| on arguments of non-constant size, since it
might easily take time linear or superlinear in the argument sizes; if
|`ominus`| produces replacement values, it completes in constant time but
derivatives invoked on the produced changes are not efficient.
%implement it on lists to produce a minimal-size difference,\citep{Cormen2001}.
% Running |`ominus`| can take time linear on input sizes, or worse: If we wanted
% to find a minimal description of a change between lists,

\section{Incrementalizing a collection API}
\label{sec:incr-coll-api-intro}
In this section, we describe a collection API that we incrementalize (partially)
in this chapter.

To avoid notation conflicts, we represent lists via
datatype |List a|, defined as follows:
\begin{code}
data List a = Nil | Cons a (List a)
\end{code}

We also consider as primitive operation a standard mapping function |map|.
We also support two restricted forms of aggregation:
(a) folding over an abelian group via
|fold|, similar to how one usually folds over a monoid;\footnote{\url{https://hackage.haskell.org/package/base-4.9.1.0/docs/Data-Foldable.html}.}
(b) list concatenation via |concat|. We will not discuss how to differentiate
|concat|, as we reuse existing solutions by \citet{Firsov2016purely}.
\begin{code}
singleton :: a -> List a
singleton x = Cons x Nil

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

fold :: AbelianGroupChangeStruct b => List b -> b
fold Nil = mempty
fold (Cons x xs) = x `mappend` fold xs -- Where |`mappend`| is infix for |mappend|.

concat :: List (List a) -> List a
concat = ...
\end{code}
While usually |fold| requires only an instance |Monoid b| of type class |Monoid| to aggregate
collection elements, our variant of |fold| requires an instance of type class |GroupChangeStruct|, a
subclass of |Monoid|. This type class is not used by |fold| itself, but only by
its derivative, as we explain in \cref{sec:incr-fold}; nevertheless,
we add this stronger constraint to |fold| itself because we forbid derivatives
with stronger type-class constraints. With this approach, all clients of |fold|
can be incrementalized using differentiation.

Using those primitives, one can define further higher-order functions on
collections such as |concatMap|, |filter|, |foldMap|. In turn, these functions
form the kernel of a collection API, as studied for instance by work on the
\emph{monoid comprehension calculus}~\citep{Grust96Monoid,Fegaras95,Fegaras99},
even if they are not complete by themselves.
\begin{code}
concatMap :: (a -> List b) -> List a -> List b
concatMap f = concat . map f

filter :: (a -> Bool) -> List a -> List a
filter p = concatMap (\x -> if p x then singleton x else Nil)

foldMap :: AbelianGroupChangeStruct b => (a -> b) -> List a -> b
foldMap f = fold . map f
\end{code}
In first-order DSLs such as SQL, such functionality must typically be added through separate
primitives (consider for instance |filter|), while here we can simply
\emph{define}, for instance, |filter| on top of |concatMap|, and incrementalize
the resulting definitions using differentiation.

Function |filter| uses conditionals, which we haven't discussed yet; we show how
to incrementalize |filter| successfully in \cref{sec:chs-sums}.\pg{Do it!}

\subsection{Changes to type-class instances?}
In this whole chapter, we assume that type-class instances, such as |fold|'s
|AbelianGroupChangeStruct| argument, do not undergo changes. Since
type-class instances are closed top-level definitions of operations and are
canonical for a datatype, it is hard to imagine a change to a type-class
instance. On the other hand, type-class instances can be encoded as first-class
values. We can for instance imagine a fold taking a unit value and an
associative operation as argument.
In such scenarios, one needs additional effort to propagate changes to operation
arguments, similarly to changes to the function argument to |map|.
\pg{this is OKish, but where is |map| now discussed?}

\subsection{Incrementalizing aggregation}
\label{sec:incr-fold}
Let's now discuss how to incrementalize |fold|.
We consider an oversimplified change structure that
allows only two sorts of changes: prepending an element to a list or removing
the list head of a non-empty list, and study how to incrementalize |fold| for
such changes:

\begin{code}
data ListChange a = Prepend a | Remove
instance ChangeStruct (List a) where
  type Dt^(List a) = ListChange a
  xs `oplus` Prepend x = Cons x xs
  (Cons x xs) `oplus` Remove = xs
  Nil `oplus` Remove = error "Invalid change"

dfold xs (Prepend x) = ...
\end{code}
Removing an element from an empty list is an invalid change, hence it is safe to
give an error in that scenario as mentioned when introducing |`oplus`|
(\cref{sec:change-intro}).

By using equational reasoning as suggested in \cref{sec:plugin-design}, starting
from \cref{eq:diff-primitive-eq-reasoning},
one can show formally that |dfold xs (Prepend x)| should be a change that,
in a sense, ``adds'' |x| to the result using group operations:
\begin{code}
       dfold xs (Prepend x)
`doe`  fold (xs `oplus` Prepend x) `ominus` fold xs
=      fold (Cons x xs) `ominus` fold xs
=      (x `mappend` fold xs) `ominus` fold xs
\end{code}
Similarly, |dfold (Cons x xs) Remove| should instead ``subtract'' |x| from the result:
\begin{code}
       dfold (Cons x xs) Remove
`doe`  fold (Cons x xs `oplus` Remove) `ominus` fold (Cons x xs)
=      fold xs `ominus` fold (Cons x xs)
=      fold xs `ominus` (x `mappend` fold xs)
\end{code}
As discussed, using |`ominus`| is fast enough on, say, integers or other
primitive types, but not in general.
To avoid using |`ominus`| we must rewrite its invocation to an equivalent expression.
In this scenario we can use group changes for abelian groups, and restrict |fold| to
situations where such changes are available.

\begin{code}
dfold :: AbelianGroupChangeStruct b => List b -> Dt^(List b) -> Dt^b
dfold xs (Prepend x) = inject x
dfold (Cons x xs) Remove = inject (invert x)
dfold Nil Remove = error "Invalid change"
\end{code}

To support group changes we define the following type classes to model abelian groups
and group change structures, omitting APIs for more general groups.
|AbelianGroupChangeStruct| only requires that group
elements of type |g| can be converted into changes (type |Dt^g|), allowing
change type |Dt^g| to contain other sorts of changes.
\begin{code}
class Monoid g => AbelianGroup g where
  invert :: g -> g
class (  AbelianGroup a, ChangeStruct a) =>
         AbelianGroupChangeStruct a where
-- Inject group elements into changes. Law:
-- |a `oplus` inject b = a `mappend` b|
  inject :: a -> Dt^a
\end{code}

\Cref{sec:applying} discusses how
we can use group changes without assuming a single group is defined on elements, but here we
simply select the canonical group as chosen by type-class resolution. To use a
different group, as usual, one defines a different but isomorphic type via the
Haskell |newtype| construct. As a downside, derivatives |newtype| constructors
must convert changes across different representations.

Rewriting |`ominus`| away can also be possible for other specialized folds,
though sometimes they can be incrementalized directly; for
instance |map| can be written as a fold. Incrementalizing |map| for the
insertion of |x| into |xs| requires simplifying |map f (Cons x xs) `ominus` map
f xs|. To avoid |`ominus`| we can rewrite this change statically to |Insert (f
x)|; indeed, we can incrementalize |map| also for more realistic change structures.

\paragraph{Associative tree folds}
Other usages of fold over sequences produce result type of small bounded size
(such as integers). In this scenario, one can incrementalize the given fold
efficiently using |`ominus`| instead of relying on group operations.
For such scenarios, one can design a primitive
\[|foldMonoid :: Monoid a => List a => a|\]
for \emph{associative tree folds}, that is, a function that folds
over the input sequence using a \emph{monoid} (that is, an associative operation
with a unit). For efficient incrementalization, |foldMonoid|'s intermediate
results should form a \emph{balanced} tree and
updating this tree should take \emph{logarithmic} time: one approach to ensure
this is to represent the input sequence itself using a balanced tree, such as a
finger tree~\citep{hinze2006finger}.

Various algorithms store intermediate results of folding
inside an input balanced tree, as described by \citet[Ch.~14]{Cormen2001} or by
\citet{hinze2006finger}. But intermediate results can also be stored outside the
input tree, as is commonly done using self-adjusting
computation~\citep[Sec.~9.1]{Acar05}, or as can be done in our setting.
While we do not use such folds, we describe the existing algorithms briefly and
sketch how to integrate them in our setting.

Function |foldMonoid| must record the intermediate results, and the derivative
|dfoldMonoid| must propagate input changes to affected intermediate
results.%

\footnote{We discuss in \cref{ch:cts} how base functions communicate results to derivatives.}
% Moreover, folding must store the tree of intermediate results for reuse by the
% derivative;
To study time complexity  of input change propagation, it is useful to consider
the \emph{dependency graph} of intermediate results: in this graph, an
intermediate result |v1| has an arc to intermediate result |v2| if and only if computing |v1|
depends on |v2|.
To ensure |dfoldMonoid| is efficient, the dependency graph of intermediate
results from |foldMonoid| must form a balanced tree of logarithmic height, so
that changes to a leaf only affect a logarithmic number of intermediate
results.

In contrast, implementing |foldMonoid| using |foldr| on a list produces an
unbalanced graph of intermediate results.
For instance, take input list |xs = [1..8]|, containing numbers from 1 to 8, and
assume a given monoid.
Summing them with |foldr (`mappend`) mempty xs| means evaluating
\[|1 `mappend` (2 `mappend` (3 `mappend` (4 `mappend` (5 `mappend` (6 `mappend`
(7 `mappend` (8 `mappend` mempty)))))))|.\]
Then, a change to the last element of input |xs| affects all intermediate
results, hence incrementalization takes at least $O(n)$.
In contrast, using |foldAssoc| on |xs| should evaluate a balanced tree similar to
\[|((1 `mappend` 2) `mappend` (3 `mappend` 4)) `mappend` ((5 `mappend` 6)
`mappend` (7 `mappend` 8))|,\]
so that any individual change to a leave, insertion or
deletion only affects $O(\log n)$ intermediate results (where $n$ is the
sequence size).
% To ensure each |dfoldMonoid| takes logarithmic time,
% as it it were a balanced tree, using
% any associative operations
% , where intermediate results
% form a balanced tree,
Upon modifications to the tree, one must ensure that the balancing is
stable~\citep[Sec. 9.1]{Acar05}.
In other words, altering the tree (by inserting or removing an element) must only alter
$O(\log n)$ nodes.

We have implemented associative tree folds on very simple but unbalanced tree
structures; we believe they could be implemented and incrementalized over
balanced trees representing sequences, such as finger trees or random access
zippers~\citep{Headley2016random}, but doing so requires transforming their
implementation of their data structure to cache-transfer style (CTS)
(\cref{ch:cts}). We leave this for future work, together with an
automated implementation of CTS transformation.

% % Aggregation
% \pg{To move}
% To study aggregation we consider |foldNat|.
% % \begin{code}
% %   foldNat z s 0 = z
% %   foldNat z s (n + 1) = s (foldNat z s n)
% %   -- Assuming that dz and ds are nil.
% %   dfoldNat z dz s ds n 0 = foldNat z s n
% %   dfoldNat z dz s ds n dn = if dn > 0 then foldNat (foldNat z s n) s dn
% % \end{code}
% % Missing sections from chap-intro-incr.lhs.

% \pg{Ask question: can we define such change structures in terms of simpler ones?}

\subsection{Modifying list elements}
\label{sec:simple-changes-list-map}
In this section, we consider another change structure on lists that allows
expressing changes to individual elements.
Then, we present |dmap|, derivative of |map| for this change structure. Finally,
we sketch informally the correctness of |dmap|, which we prove formally in
\cref{ex:syn-changes-map}.

We can then represent changes to a list (|List a|) as a list of changes (|List
(Dt^a)|), one for each element.
A list change |dxs| is valid for source |xs| if
they have the same length and each element change is valid for
its corresponding element.
For this change structure we can define |`oplus`| and
|`ocompose`|, but not a total |`ominus`|: such list changes can't express the
difference between two lists of different lengths.
% We discuss
% product and sum types more in general in \cref{ch:prod-sums}.
Nevertheless, this change structure is sufficient to define
derivatives that act correctly on the changes that can be expressed.
We can describe this change structure in Haskell using a
type-class instance for class |ChangeStruct|:
\begin{code}
instance ChangeStruct (List a) where
  type Dt^(List a) = List (Dt^a)
  Nil `oplus` Nil = Nil
  (Cons x xs) `oplus` (Cons dx dxs) = Cons (x `oplus` xs) (dx `oplus` dxs)
  _ `oplus` _ = Nil
\end{code}

The following |dmap| function is a derivative for the
standard |map| function (included for reference) and the given
change structure. We discuss derivatives for recursive functions
in \cref{sec:general-recursion}.
\begin{code}
map : (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

dmap : (a -> b) -> Dt^(a -> b) -> List a -> Dt^List a -> Dt^List b
-- A valid list change has the same length as the base list:
dmap f df Nil Nil = Nil
dmap f df (Cons x xs) (Cons dx dxs) =
  Cons (df x dx) (dmap f df xs dxs)
-- Remaining cases deal with invalid changes, and a dummy
-- result is sufficient.
dmap f df xs dxs = Nil
\end{code}
Function |dmap| is a correct derivative of |map| for this change structure,
according to \cref{slogan:derive}: we sketch an informal argument by induction.
The equation for |dmap f df Nil Nil| returns |Nil|, a valid change from initial
to updated outputs, as required.
In the equation for |dmap f df (Cons x xs) (Cons dx dxs)| we compute changes to
the head and tail of the result, to produce a change from
|map f (Cons x xs)| to |map (f `oplus` df) (Cons x xs `oplus` Cons dx dxs)|. To
this end,
(a) we use |df x dx| to compute a
change to the head of the result, from |f x| to |(f `oplus` df) (x `oplus` dx)|;
(b) we use |dmap f df xs dxs| recursively to compute a change to the tail of the
result, from |map f xs| to |map (f `oplus` df) (xs `oplus` dxs)|;
(c) we assemble changes to head and tail with |Cons| into a change from
In other words, |dmap| turns input changes to output changes correctly according
to our \cref{slogan:derive}: it is a correct derivative for |map| according to
this change structure.
We have reasoned informally; we formalize this
style of reasoning in \cref{sec:denot-syntactic-reasoning}. Crucially, our
conclusions only hold if input changes are valid, hence term |map f xs `oplus` dmap f
df xs dxs| is not denotationally equal to |map (f `oplus` df) (xs `oplus` dxs)|
for arbitrary change environments:
these two terms only evaluate to the same result for valid input changes.

Since this definition of |dmap| is a correct derivative, we could use it in an incremental DSL for
list manipulation, together with other primitives. Because of limitations we
describe next, we will use instead improved language plugins for sequences.

\subsection{Limitations}
We have shown simplified list changes, but they have a few limitations. Fixing
those requires more sophisticated definitions.

As discussed, our list changes intentionally forbid changing the length of a list.
And our definition of |dmap| has further limitations: a change to a list of $n$
elements takes size $O(n)$, even when most elements do not change, and calling
|dmap f df| on it requires $n$ calls to |df|. This is only faster if |df| is
faster than |f|, but adds no further speedup.

We can describe instead a change to an arbitrary list element |x| in |xs| by
giving the change |dx| and the position of |x| in |xs|. A list change is then a
sequence of such changes:
\begin{code}
type Dt^(List a) = List (AtomicChange a)
data AtomicChange a = Modify Int (Dt^a)
\end{code}
However, fetching the |i|-th list element still takes time linear in |i|: we
need a better representation of sequences. In next section, we switch to a change structure
on sequences defined by finger trees~\citep{hinze2006finger},
following \citet{Firsov2016purely}.

\section{Efficient sequence changes}
\pg{move/merge this to chapter on CTS and add pointer}
\citet{Firsov2016purely} define an efficient representation of list changes in a
framework similar to ILC, and incrementalize selected operations over this change
structure. They also provide combinators to assemble further operations on top
of the provided ones.
We extend their framework to handle function changes and generate derivatives
for all functions that can be expressed in terms of the primitives.

\pg{Consider resuming here}
%\pg{Code size for snippets?}
Conceptually, a change for type |Sequence a| is a sequence of atomic changes.
Each atomic change inserts one element at a given position, or removes one
element, or changes an element at one
position.\footnote{\citet{Firsov2016purely} and our implementation allow changes
  to multiple elements.}
% data AtomicChange a
%   =  Insert Int a
%   |  Delete Int
%   |  ShiftAt
%   |  ChangeAt Int (Dt^a)
\begin{code}
data SeqSingleChange a
  =  Insert    { idx :: Int, x :: a }
  |  Remove    { idx :: Int }
  |  ChangeAt  { idx :: Int, dx :: Dt^a }
data SeqChange a = Sequence (SeqSingleChange a)
type Dt^(Sequence a) = SeqChange a
\end{code}
\pg{Nil change detection}
\pg{Move here example on list later}

\pg{Real list}

\pg{Average}

\subsection{Incremental higher-order primitives and nested loops}
\pg{Nested loops}
\pg{we need to discuss how map propagates changes to functions.}

\section{Products}
\label{sec:chs-products-intro}
It is also possible to define change structures for arbitrary sum and product
types, and to provide derivatives for introduction and elimination forms for
such datatypes. In this section we discuss products, in the next section sums.

We define a simple change structure for product type |A `times` B| from change
structures for |A| and |B|, similar to change structures for environments:
operations act pointwise on the two components.
\begin{code}
instance (ChangeStruct a, ChangeStruct b) => ChangeStruct (a, b) where
  type Dt^(a, b) = (Dt^a, Dt^b)
  (a, b) `oplus` (da, db) = (a `oplus` da, b `oplus` db)
  (a2, b2) `ominus` (a1, b1) = (a2 `ominus` a1, b2 `ominus` b1)
  oreplace (a2, b2) = (oreplace a2, oreplace b2)
  nil (a, b) = (nil a, nil b)
  (da1, db1) `ocompose` (da2, db2) = (da1 `ocompose` da2, db1 `ocompose` db2)
\end{code}

Through equational reasoning as in \cref{sec:plugin-design}, we can also
compute derivatives for basic primitives on product types, both
the introduction form (that we alias as |pair|) and the elimination forms |fst|
and |snd|. We just present the resulting definitions:
% ∆⨟
\begin{code}
pair a b = (a, b)
dpair a da b db = (da, db)

fst (a, b) = a
snd (a, b) = b
dfst :: Dt^(a, b) -> Dt^a
dfst (da, db) = da
dsnd :: Dt^(a, b) -> Dt^b
dsnd (da, db) = db

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b
duncurry :: (a -> b -> c) -> Dt^(a -> b -> c) -> (a, b) -> Dt^(a, b) -> Dt^c
duncurry _f df (x, y) (dx, dy) = df x dx y dy
\end{code}

One can also define $n$-ary products in a similar way. However, a product change
contains as many entries as a product.\pg{Sketch alternatives.}

\section{Sums, pattern matching and conditionals}
\label{sec:chs-sums}
In this section we define change structures for sum types, together with the
derivative of their introduction and elimination forms.
We also obtain support for booleans (which can be encoded as sum type |1 + 1|)
and conditionals (which can be encoded in terms of elimination for sums).
We have mechanically proved correctness of this change structure and
derivatives, but we do not present the tedious details in this thesis and refer
to our Agda formalization.

Changes structures for sums are more challenging than ones for products. We can
define them, but in many cases we can do better with specialized structures.
Nevertheless, such changes are useful in some scenarios.

In Haskell, sum types |a + b| are conventionally defined via datatype |Either a
b|, with introduction forms |Left| and |Right| and elimination form |either|
which will be our primitives:
\begin{code}
data Either a b = Left a | Right b

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left a) = f a
either f g (Right b) = g b
\end{code}

We can define the following change structure.
\begin{code}
data EitherChange a b
  =  LeftC (Dt^a)
  |  RightC (Dt^b)
  |  EitherReplace (Either a b)

instance (  ChangeStruct a, ChangeStruct b) =>
            ChangeStruct (Either a b) where
  type Dt^(Either a b) = EitherChange a b
  Left a   `oplus` LeftC da          = Left (a `oplus` da)
  Right b  `oplus` RightC db         = Right (b `oplus` db)
  Left _   `oplus` RightC _          = error "Invalid change!"
  Right _  `oplus` LeftC _           = error "Invalid change!"
  _        `oplus` EitherReplace e2  = e2

  oreplace = EitherReplace

  nil (Left a) = LeftC (nil a)
  nil (Right a) = RightC (nil a)
\end{code}
Changes to a sum value can either keep the same ``branch'' (left or right) and
modify the contained value, or replace the sum value with another one altogether.
Specifically, change |LeftC da| is valid from |Left a1| to |Left a2| if |da| is valid from
|a1| to |a2|. Similarly, change |RightC db| is valid from |Right b1| to |Right
b2| if |db| is valid from |b1| to |b2|.
Finally, replacement change |EitherReplace e2| is valid from |e1| to |e2| for
any |e1|.

Using \cref{eq:diff-primitive-eq-reasoning}, we can then obtain definitions for
derivatives of primitives |Left|, |Right| and |either|. The resulting code is as follows:
\begin{code}
dLeft :: a -> Dt^a -> Dt^(Either a b)
dLeft a da = LeftC da

dRight :: b -> Dt^b -> Dt^(Either a b)
dRight b db = RightC db

deither ::
  (NilChangeStruct a, NilChangeStruct b, DiffChangeStruct c) =>
  (a -> c) -> Dt^(a -> c) -> (b -> c) -> Dt^(b -> c) ->
  Either a b -> Dt^(Either a b) -> Dt^c
deither f df g dg (Left a) (LeftC da) = df a da
deither f df g dg (Right b) (RightC db) = dg b db
deither f df g dg e1 (EitherReplace e2) =
  either (f `oplus` df) (g `oplus` dg) e2 `ominus` either f g e1
deither _ _ _ _ _ _ = error "Invalid sum change"
\end{code}

We show only one case of the derivation of |deither| as an example:
\begin{equational}
\begin{code}
      deither f df g dg (Left a) (LeftC da)
`doe` {- using variants of \cref{eq:diff-primitive-eq-reasoning} for multiple arguments -}
      either (f `oplus` df) (g `oplus` dg) (Left a `oplus` LeftC da) `ominus` either f g (Left a)
=     {- simplify |`oplus`| -}
      either (f `oplus` df) (g `oplus` dg) (Left (a `oplus` da)) `ominus` either f g (Left a)
=     {- simplify |either| -}
      (f `oplus` df) (a `oplus` da) `ominus` f a
`doe` {- because |df| is a valid change for |f|, and |da| for |a| -}
      df a da
\end{code}
\end{equational}

Unfortunately, with this change structure a change from |Left a1| to |Right b2|
is simply a replacement change, so derivatives processing it must recompute
results from scratch.
In general, we cannot do better, since there need be no shared data between two
branches of a datatype. We need to find specialized scenarios where better
implementations are possible.

\subsection{Optimizing |filter|}
In \cref{sec:incr-coll-api-intro} we have defined |filter| using a conditional,
and now we have just explained that in general conditionals are inefficient!
This seems pretty unfortunate. But luckily, we can optimize |filter| using
equational reasoning.

Consider again the earlier definition of |filter|:
\begin{code}
filter :: (a -> Bool) -> List a -> List a
filter p = concatMap (\x -> if p x then singleton x else Nil)
\end{code}
As explained, we can encode conditionals using |either| and differentiate the
resulting program. However, if |p x| changes from |True| to |False|, or
viceversa (that is, for all elements |x| for which |dp x dx| is a non-nil
change), we must compute |`ominus`| at runtime. However, |`ominus`| will compare
empty list |Nil| with a singleton list produced by |singleton x| (in one
direction or the other). We can have |`ominus`| detect this situation at
runtime. But since the implementation of |filter| is known statically, we can
optimize this code at runtime, rewriting |singleton x `ominus` Nil| to |Insert
x|, and |Nil `ominus` singleton x| to |Remove|. To enable this optimization in
|dfilter|, we need to inline the function that |filter| passes as argument to
|concatMap| and all the functions it calls except |p|. Moreover, we need to
case-split on possible return values for |p x| and |dp x dx|. We omit the steps
because they are both tedious and standard.

It appears in principle possible to automate such transformations by adding
domain-specific knowledge to a sufficiently smart compiler, though we have made
no attempt at an actual implementation. It would be first necessary to
investigate further classes of examples where optimizations are
applicable.\pg{claim we have more}
Sufficiently smart compilers are rare, but since our approach produces purely
functional programs we have access to GHC and HERMIT~\citep{Farmer2012hermit}.
An interesting alternative (which does have some support for side effects) is
LMS~\citep{rompf2010lightweight} and Delite~\citep{Brown11}.
We leave further investigation for future work.

\paragraph{Extensions and future work}
But in some cases types |a| and |b| are related. Take again lists: a change from
list |as| to list |Cons a2 as| should simply say that we prepend |a2| to the
list. In a sense, we are just using a change structure from type |List a| to
|(a, List a)|.
More in general, if change |das| from |as1| to |as2| is small, a change from
list |as1| to list |Cons a2 as2| should simply ``say'' that we prepend |a2| and
that we modify |as1| into |as2|.

Such a facility might allow building change structures such as the one we
considered for lists in \cref{sec:incr-fold}.

In \cref{sec:param-derive-changes-across-types} we sketch a few ways to
construct such change structures, based on the concept of \emph{polymorphic
  change structure}, where changes have source and destination of different
types. Based on initial experiments, we believe one could develop these
constructions into a powerful combinator language for change structures, but
many questions remain open, so we leave this effort for future work.

\section{Chapter conclusion}
In this chapter we have toured what can and cannot be incrementalized using
differentiation, and how using higher-order functions allows defining generic
primitives to incrementalize.
