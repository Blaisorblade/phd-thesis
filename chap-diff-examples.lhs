% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{A tour of differentiation examples}
\label{ch:diff-examples}
Before dealing with ILC formally, we show a bigger set of example change structures and primitives.
To describe these examples informally, we use Haskell notation and let
polymorphism as appropriate (see \cref{sec:intro-stlc}).
% We already sketch, how a change structure
% can be represented in Haskell terms:

\paragraph{Change structures in Haskell}
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
conclusions only hold if input changes are valid, hence |map f xs `oplus` dmap f
df xs dxs| is not denotationally equal to |map (f `oplus` df) (xs `oplus` dxs)|:
they only evaluate to the same result for valid input changes.

Since |dmap| is a correct derivative, we could use it in an incremental DSL for
list manipulation, together with other primitives. However,

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
