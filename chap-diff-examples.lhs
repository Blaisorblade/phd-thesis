% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{A tour of differentiation examples}
\label{ch:diff-examples}
Before formalizing ILC, we show more example of change structures and
primitives, to show (a) designs for reusable primitives and their
derivatives, (b) to what extent we can incrementalize basic building
blocks such as recursive functions and algebraic data types, and (c) to sketch how
we can incrementalize collections efficiently. When possible, we will try to
define change structures for a datatype, together with introduction and
elimination forms for that datatype.

To describe these examples informally, we use Haskell notation and let
polymorphism as appropriate (see \cref{sec:intro-stlc}).
% We already sketch, how a change structure
% can be represented in Haskell terms:

We also motivate a few extensions to differentiation that we describe later. As
we'll see in this chapter, we'll need to enable some forms of introspection on
function changes to manipulate the embedded environments, as we discuss in
\cref{ch:defunc-fun-changes}. We will also need ways to remember intermediate
results.\pg{discussed where?}

\section{Change structures in Haskell}
We encode change structure
as a \emph{type class} named |ChangeStruct|. An instance |ChangeStruct t|
defines a change type |Dt^t| as an associated type and operations |`oplus`|,
|`ominus`| and |`ocompose`| are defined as methods.
\begin{code}
class ChangeStruct t where
  type Dt^t
  oplus :: t -> Dt t -> t
  ominus :: t -> t -> Dt t
  (`ocompose`) :: Dt t -> Dt t -> Dt t
  nilc :: t -> Dt t
\end{code}
In this chapter we will
often show change structures where only some methods are defined; in actual
implementations we use a type class hierarchy to encode what operations are
available, but we collapse this hierarchy here to simplify presentation.
% We'll come back to this definition and refine it,
% describing the laws it satisfies, in \cref{sec:change-struct-tc}.

\pg{Too short for a section. Add sums and products maybe?}
\section{How to design a language plugin}
\pg{Put somewhere:}
In general, to differentiate a primitive |f : A -> B| once we have defined a
change structure for |A|, we can start by defining |df a1 da = f a2
`ominus` f a1|, assume |da| is a valid change from |a1| to |a2|, and try to
simplify and rewrite the expression in terms of |a1| and |da| to avoid using
|`ominus`| as far as possible.
\section{Simple changes on lists}
\label{sec:simple-changes-list-map}
In this section, we consider a basic change structure on lists and the
derivative of |map|, and we sketch informally its correctness. We prove it
formally in \cref{ex:syn-changes-map}.

To avoid notation conflicts, we represent lists via
datatype |List a|, defined as follows:
\begin{code}
  data List a = Nil | Cons a (List a)
\end{code}

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
typeclass instance for class |ChangeStruct|:
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
position.\footnote{\citet{Firsov2016purely} and our implementation allow.}
% data AtomicChange a
%   =  Insert Int a
%   |  Delete Int
%   |  ShiftAt
%   |  ChangeAt Int (Dt^a)
\begin{code}
data SeqSingleChange a
  =  Insert    { idx :: Int, x :: a }
  |  Remove    { idx :: Int }
  |  ChangeAt  { idx :: Int, dx :: Dt ^ a }
data SeqChange a = Sequence (SeqSingleChange a)
type Dt (Sequence a) = SeqChange a
\end{code}
\pg{Nil change detection}
\pg{Move here example on list later}

\pg{Real list}

\pg{Average}

\pg{Nested loops}
\section{A higher-order example}
\label{sec:differentiation-fold-example}
\pg{write}
% Referenced later in sec-performance.tex by saying:
% % We have seen in \cref{ssec:differentiation} that $\Derivative$
% % needlessly recomputes $\Merge\Xs\Ys$. However, the result is a
% % base input to $\FOLD'$.

\section{Aggregation}
\pg{To move}
To study aggregation we consider |foldNat|.
% \begin{code}
%   foldNat z s 0 = z
%   foldNat z s (n + 1) = s (foldNat z s n)
%   -- Assuming that dz and ds are nil.
%   dfoldNat z dz s ds n 0 = foldNat z s n
%   dfoldNat z dz s ds n dn = if dn > 0 then foldNat (foldNat z s n) s dn
% \end{code}
% Missing sections from chap-intro-incr.lhs.

\pg{Ask question: can we define such change structures in terms of simpler ones?}
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
  oplus (a, b) (da, db) = (oplus a da, oplus b db)
  nil (a, b) = (nil a, nil b)
  (da1, db1) `ocompose` (da2, db2) = (da1 `ocompose` da2, db1 `ocompose` db2)
\end{code}
We can also define derivatives for the basic primitives on product types, both
the introduction form (that we alias as |pair|) and the elimination forms |fst|
and |snd|.
% ∆⨟
\begin{code}
pair a b = (a, b)
dpair a da b db = (da, db)

fst (a, b) = a
snd (a, b) = b
dfst :: Dt (a, b) -> Dt a
dfst (da, db) = da
dsnd :: Dt (a, b) -> Dt b
dsnd (da, db) = db

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b
duncurry :: (a -> b -> c) -> Dt (a -> b -> c) -> (a, b) -> Dt (a, b) -> Dt c
duncurry _f df (x, y) (dx, dy) = df x dx y dy
\end{code}

One can also define $n$-ary products in a similar way. However, a product change
contains as many entries as a product.\pg{Sketch alternatives.}

\section{Sums}
\label{sec:chs-sums}
Changes structures for sums are more challenging. We can define them, but in
many cases we can do better with specialized structures.
\begin{code}
data EitherChange a b = LeftC (Dt a) | RightC (Dt b) | EitherReplace (Either a b)
oplusEither
  :: (ChangeStruct a, ChangeStruct b) =>
     Either a b -> EitherChangeBase a b -> Either a b
(Left a) `oplusEitherBase` (LeftC da) = Left (a `oplus` da)
(Right b) `oplusEitherBase` (RightC db) = Right (b `oplus` db)
(Left _) `oplusEitherBase` (RightC _) = error "Invalid change!"
(Right _) `oplusEitherBase` (LeftC _) = error "Invalid change!"

instance (ChangeStruct a, ChangeStruct b) => ChangeStruct (Either a b) where
  type Dt (Either a b) = Replace (Either a b) (EitherChangeBase a b)
  oplus = oplusEither
  oreplace = EitherReplace

instance (NilChangeStruct a, NilChangeStruct b) => NilChangeStruct (Either a b) where
  nil (Left a) = Ch $ LeftC (nil a)
  nil (Right a) = Ch $ RightC (nil a)
\end{code}
\pg{Add |either| and |deither|!}

\paragraph{Extensions}
Unfortunately, with this change structure a change from |Left a1| to |Right b2|
is simply a replacement change, so derivatives processing it must recompute
results from scratch. Could we do better?
In general no, since there need be no shared data between two
branches of a datatype.
But in some cases types |a| and |b| are related. Take again lists: a change from
list |as| to list |Cons a2 as| should simply say that we prepend |a2| to the
list. In a sense, we are just using a change structure from type |List a| to |a
`times` List a|.
More in general, if change |das| from |as1| to |as2| is small, a change from
list |as1| to list |Cons a2 as2| should simply ``say'' that we prepend |a2| and
that we modify |as1| into |as2|.
With a better way to describe a change from values of type |a| to
values of type |b|,
\pg{Later we sketch change structures across types.}

\pg{Idea: |ChangeStruct2 t1 t2, Iso t2 t3) => ChangeStruct2 t1 t3|}
% Lists can be described as the fixpoint of a sum of
% product: |List a = mu X. 1 + A `times` X|