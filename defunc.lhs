% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

%if style == newcode
\begin{code}
{-# LANGUAGE ExistentialQuantification, TypeFamilies, TypeFamilyDependencies,
  InstanceSigs, GADTs, TypeOperators, ConstraintKinds #-}
import qualified Data.Sequence as S
import Data.Sequence(Seq)
import Prelude hiding (map, concatMap)
\end{code}
%endif

\chapter{Defunctionalizing function changes}
\label{ch:defunc-fun-changes}

Up to now we have represented function changes as functions, which can only be
applied. However, incremental programs often inspect changes to decide how to
react to them most efficiently. Also inspecting function changes would help
performance further. In this chapter, we address these restrictions by
\emph{defunctionalizing} functions and function changes, so that we can inspect
both at runtime.

Once we defunctionalize function changes, we can detect at runtime whether a
function change is nil. As we have mentioned in \cref{sec:plugins}, nil function
changes can typically be handled more efficiently. For instance, consider |t =
map f xs|, a term that maps function |f| to each element of sequence |xs|. In
general, |derive(t) = dmap f df xs dxs| must handle any change in |dxs| (which
we assume to be small) but also apply function change |df| to each element of
|xs| (which we assume to be big). However, if |df| is nil we can skip this step,
decreasing time complexity of |dmap f df xs dxs| from |O(size(xs) + size(dxs))|
to |O(size(dxs))|.

We will also present a change structure on defunctionalized function changes,
and show its benefits.\pg{Furthermore, other operations on function and
  function changes become cheaper, such as |`oplus`|, |nilc|, and so on.}
%Moreover, as we have discussed

% \chapter{Defunctionalizing function changes}
% \label{ch:defunc-fun-changes}
% If we represent function changes as functions, we can only apply them. This and
% other problems are vastly simplified if we instead defunctionalize function
% changes. Furthermore, assembling changes for functions becomes easier if the
% functions are defunctionalized as well.

% In this chapter, we show how to systematically incrementalize such
% defunctionalized programs by systematic program transformation.

% \subsection{Avoiding the closed-world assumption}
% \pg{Move this somewhere better.}

% \pg{cite Uroboro.}

% Defunctionalization as usually defined can only be performed on a closed
% program. Using open algebraic datatypes can lift this restriction, though
% usually at the cost of exhaustiveness checking.

% Representing changes as data instead of functions is not a goal per se. Rather,
% our goal is defining other primitive operations on function changes beyond
% application, and that is not possible if function changes are represented as
% functions. However, this problem could also be solved by representing function
% changes as more general \emph{codata} using copatterns. Codata generalize
% functions; while functions can only be \emph{observed} by applying them to an
% argument, codata can support further observations. Moreover, when defining
% codata using copatterns, the codata definition fixes a set of observations,
% while new generators can be defined in the entire program, similarly to how
% functions can be defined in a whole programs.

% Hence we could potentially represent changes as codata. We leave this for future
% work.

\section{Setup}
\label{sec:change-struct-tc} \pg{earlier we have a different typeclass}

We write incremental programs based on ILC by manually writing Haskell code,
containing both manually-written plugin code, and code that is transformed
systematically, based on informal generalizations and variants of
|derive(param)|. Our main goal is to study variants of differentiation and of
encodings in Haskell, while also studying language plugins for non-trivial
primitives, such as different sorts of collections. We make liberal use of GHC
extensions where needed.

As sketched before, we define change structure inside Haskell. We choose for now
a different subset of operations.
We proceed as follows.
\begin{code}
class ChangeStruct t where
  -- Next line declares |Dt^t| as an injective type function
  type Dt^t = r | r -> t

  oplus :: t -> Dt^t -> t
  oreplace :: t -> Dt^t

class ChangeStruct t => NilChangeStruct t where
  nil :: t -> Dt^t
\end{code}
%ocompose :: Dt^t -> Dt^t -> Dt^t
With this code we define type classes |ChangeStruct| and |NilChangeStruct|. We
explain each of the declared members in turn.

First, type |Dt^t| represents the change type for type |t|. To improve Haskell
type inference, we declare that |Dt| is injective, so that |Dt^t1 = Dt^t2|
implies |t1 = t2|. This forbids some potentially useful change structures, but
in exchange it makes type inference vastly more usable.

Next, we declare |`oplus`| and |nilc| as available to object programs.\pg{Why a separate type class for |nilc|?}
%
\pg{pointer to bang?} Last, we introduce |oreplace| to construct replacement
changes, characterized by the \emph{absorption law} |x `oplus` oreplace y = y|
for all |x|.
Function |oreplace| encodes |!t|, that is the bang operator. We use a different
notation because |!| is reserved for other purposes in Haskell.

These typeclasses omit operation |`ominus`| intentionally: we do \emph{not}
require that change structures support a proper difference operation.
Nevertheless, as discussed |b `ominus` a| can be expressed through |oreplace b|.
\pg{Should we omit |oreplace| at first?}

% or that all changes are
% representable.

We can then differentiate Haskell functions---even polymorphic ones. We show a
few trivial examples to highlight how derivatives are encoded in Haskell,
especially polymorphic ones.
\begin{code}
-- The standard |id| function:
id :: a -> a
id x = x
-- and its derivative:
did :: a -> Dt^a -> Dt^a
did x dx = dx

instance (NilChangeStruct a, ChangeStruct b) => ChangeStruct (a -> b) where
  type Dt^(a -> b) = a -> Dt^a -> Dt^b
  f `oplus` df = \x -> f x `oplus` df x (nil x)
  oreplace f = \x dx -> oreplace (f (x `oplus` dx))
instance (NilChangeStruct a, ChangeStruct b) => NilChangeStruct (a -> b) where
  nil f = oreplace f

-- Same for |apply|:
apply :: (a -> b) -> a -> b
apply f x = f x
dapply :: (a -> b) -> Dt^(a -> b) -> a -> Dt^a -> Dt^b
dapply f df x dx = df x dx
\end{code}
\paragraph{Which polymorphism?}
As visible here, polymorphism does not cause particular problems. However, we
only support ML (or prenex) polymorphism, not first-class
polymorphism, for two reasons.

%format T1
%format T2

First, with first-class polymorphism, we can encode
existential types |exists X. T|, and two values |v1, v2| of the same existential type
|exists X. T| can hide different types |T1, T2|,
Hence, a change between |v1| and |v2| requires handling changes between types.

Second, prenex polymorphism is a small extension of simply-typed lambda calculus
metatheoretically. We can treat prenex-polymorphic definitions as families of
monomorphic (hence simply-typed) definitions; to each definition we can apply
all the ILC theory we developed to show differentiation is correct.
% Alternatively, we can regard type variables as additional base types without
% primitives, so that we can treat our function definitions as one functions.

% \section{Setup}
% \pg{Clarify how we use Haskell}

% Even though we do not support higher-order programs directly, we still reuse or
% adapt many of the ideas from ILC. \pg{Check this} And as we will see, we treat
% defunctionalized functions specially.

% In this chapter we will support polymorphism but avoid tackling first-class
% polymorphism.
% \pg{add pointer.}

% Let's rememeber our basic interface to change structures:
% \begin{code}
% class ChangeStruct t where
%   type Dt^t = r | r -> t
%   oplus :: t -> Dt^t -> t
%   oreplace :: t -> Dt^t

% class ChangeStruct t => OnilChangeStruct t where
%   -- Proxy is used to encode explicit type application.
%   onil :: Proxy t -> Dt^t

% class ChangeStruct t => NilChangeStruct t where
%   nil :: t -> Dt^t
% \end{code}

% Let's also recall the \emph{absorption law}, |x `oplus` oreplace y = y|.

% Crucially, changes to type |t| are represented as type |Dt^t|, and this
% interface does \emph{not} require that change structures support a difference
% operation, or that all changes are representable.

\section{Defunctionalization}
Defunctionalization is a whole-program transformation that turns a program
relying on first-class functions into a first-order program. The resulting
program is expressed in a first-order language (often a subset of the original
language); closures are encoded by data values, which embed both the closure
environment and a tag to distinguish different function. Defunctionalization
also generates a function that interprets encoded closures, which we call
|applyFun|.

% We have multiple versions of the same definitions, hide the version numbers in
% LaTeX output.

%if style /= newcode

%format Fun0 = Fun
%format DFun0 = DFun
%format AddOne0 = AddOne
%format Pair0 = Pair
%format MapPair0 = MapPair
%format mapDF0 = mapDF
%format concatMapDF0 = concatMapDF
%format nestedLoopDF0 = nestedLoopDF
%format F0 = F
%format DF0 = DF
%format Code0 = Code
%format codeMatch0 = codeMatch
%format applyFun0 = applyFun
%format dapplyFun0 = dapplyFun
%format successors0 = successors

%format Fun1 = Fun
%format DFun1 = DFun
%format AddOne1 = AddOne
%format Pair1 = Pair
%format MapPair1 = MapPair
%format apply1 = apply
%format mapDF1 = mapDF
%format concatMapDF1 = concatMapDF
%format nestedLoopDF1 = nestedLoopDF
%format F1 = F
%format DF1 = DF
%format Code1 = Code
%format codeMatch1 = codeMatch
%format applyFun1 = applyFun
%format dapplyFun1 = dapplyFun
%format successors1 = successors
%format dmapDF1 = dmapDF

%format RawFun1 = RawFun
%format applyCode1 = applyCode
%format applyRaw1 = applyRaw
%format dapplyCode1 = dapplyCode

% Here indexes are not to be hidden.
%format C1
%format env1
%format env2

%format derApplyDFun1
%format Add1
%format Add2

%endif

In a typed language, defunctionalization can be done using generalized algebraic
datatypes (GADTs)~\citep{Pottier2004polymorphic}. Each first-class function of
type |sigma -> tau| is replaced by a value of a new GADT |Fun sigma tau|, that
represents defunctionalized function values and has a constructor for each
different function. If a first-class function |t1| closes over |x :: tau1|, the
corresponding constructor |C1| will take |x :: tau1| as an argument. The
interpreter for defunctionalized function values has type signature |applyFun ::
Fun sigma tau -> sigma -> tau|. The resulting programs are expressed in a
first-order subset of the original programming language.
In defunctionalized programs, all remaining functions are first-order top-level
functions.

For instance, consider the program on sequences in \cref{fig:defunc-example}.
\begin{figure}[h]
\begin{code}
successors :: [Int] -> [Int]
successors xs = map (\x -> x + 1) xs

nestedLoop :: [sigma] -> [tau] -> [(sigma, tau)]
nestedLoop xs ys = concatMap (\x -> map (\y -> (x, y)) ys) xs

map :: (sigma -> tau) -> [sigma] -> [tau]
map f [] = []
map f (x : xs) = f x : map f xs

concatMap :: (sigma -> [tau]) -> [sigma] -> [tau]
concatMap f xs = concat (map f xs)
\end{code}
\caption{A small example program for defunctionalization.}
\label{fig:defunc-example}
\end{figure}

In this program, the first-class function values arise from evaluating the three
terms |\y -> (x, y)|, that we call |pair|, |\x -> map (\y -> (x, y)) ys|,
that we call |mapPair|, and |\x -> x + 1|, that we call |addOne|.
Defunctionalization creates a type |Fun sigma tau| with a constructor for each
of the three terms, respectively |Pair|, |MapPair| and |AddOne|.
Both |pair| and |mapPair| close over some free variables, so their
corresponding constructors will take an argument
for each free variable; for |pair| we have
%
\[|x :: sigma /- (\y -> (x, y)) :: tau -> (sigma, tau)|,\]
%
while for |mapPair| we have
%
\[|ys :: [tau] /- (\x -> map (\y -> (x, y)) ys) :: sigma -> [(sigma, tau)]|.\]
%
Hence, the type of defunctionalized functions |Fun sigma tau| and its
interpreter |applyFun0| become:

\begin{code}
data Fun0 sigma tau where
  AddOne0   ::            Fun0 Int    Int
  Pair0     :: sigma  ->  Fun0 tau    (sigma, tau)
  MapPair0  :: [tau]  ->  Fun0 sigma  [(sigma, tau)]

applyFun0 ::  Fun0 sigma tau ->  sigma -> tau
applyFun0     AddOne0            x = x + 1
applyFun0     (Pair0 x)          y = (x, y)
applyFun0     (MapPair0 ys)      x = mapDF0 (Pair0 x) ys
\end{code}

We need to also transform the rest of the program accordingly.

\begin{figure}[h!]
\begin{code}
successors0 :: [Int] -> [Int]
successors0 xs = map (\x -> x + 1) xs

nestedLoopDF0 :: [sigma] -> [tau] -> [(sigma, tau)]
nestedLoopDF0 xs ys = concatMapDF0 (MapPair0 ys) xs

mapDF0 :: Fun0 sigma tau -> [sigma] -> [tau]
mapDF0 f [] = []
mapDF0 f (x : xs) = applyFun0 f x : mapDF0 f xs

concatMapDF0 :: Fun0 sigma [tau] -> [sigma] -> [tau]
concatMapDF0 f xs = concat (mapDF0 f xs)
\end{code}
\label{prog:defunc-curried}
\end{figure}

Some readers might notice this program still uses first-class function, because
it encodes multi-argument functions through currying. To get a fully first-order
program, we encode multi-arguments functions using tuples instead of currying.%
\footnote{Strictly speaking, the resulting program is still not first-order,
  because in Haskell multi-argument data constructors, such as the pair
  constructor |(,)| that we use, are still first-class curried functions, unlike
  for instance in OCaml. To make this program truly first-order, we must
  formalize tuple constructors as a term constructor, or formalize these
  function definitions as multi-argument functions. At this point, this
  discussion is merely a technicality that does not affect our goals, but it
  becomes relevant if we formalize the resulting first-order
  language~\citep{Giarrusso2017Static}.}
%
Using tuples our example becomes:
%{
%if style /= newcode
%format applyFun01 = applyFun
%format mapDF01 = mapDF
%format concatMapDF01 = concatMapDF
%format nestedLoopDF01 = nestedLoopDF
%endif
\begin{code}
applyFun01 ::  (Fun0 sigma tau, sigma) ->  tau
applyFun01     (AddOne0, x)                = x + 1
applyFun01     (Pair0 x, y)                = (x, y)
applyFun01     (MapPair0 ys, x)            = mapDF01 (Pair0 x, ys)

mapDF01 :: (Fun0 sigma tau, [sigma]) -> [tau]
mapDF01 (f, []) = []
mapDF01 (f, x : xs) = applyFun01 (f, x) : mapDF01 (f, xs)

concatMapDF01 :: (Fun0 sigma [tau], [sigma]) -> [tau]
concatMapDF01 (f, xs) = concat (mapDF01 (f, xs))

nestedLoopDF01 :: ([sigma], [tau]) -> [(sigma, tau)]
nestedLoopDF01 (xs, ys) = concatMapDF01 (MapPair0 ys, xs)
\end{code}
%}

However, we'll often write such defunctionalized programs using Haskell's
typical curried syntax, as in \cref{prog:defunc-curried}. Such programs must not
contain partial applications.
% \pg{Revise this.} But for now we'll avoid using tuples and stick to currying, as
% it makes for more idiomatic Haskell syntax.

In general, defunctionalization creates a constructor |C| of type |Fun sigma
tau| for each first-class function expression |Gamma /- t : sigma -> tau| in the
source program.\footnote{We only need codes for functions that are used as
  first-class arguments, not for other functions, though codes for the latter
  can be added as well.}
%
While lambda expression |l| closes \emph{implicitly} over environment |rho :
eval(Gamma)|, |C| closes over it explicitly: the values bound to free variables
in environment |rho| are passed as arguments to constructor |C|. As a standard
optimization, we only includes variables that actually occur free in |l|, not
all those that are bound in the context where |l| occurs.

\subsection{Defunctionalization with separate function codes}
Next, we show a slight variant of defunctionalization, that we use to achieve
our goals with less code duplication, even at the expense of some efficiency; we
call this variant \emph{defunctionalization with separate function codes}.

We first encode contexts as types and environments as values. Empty environments
are encoded as empty tuples. Environments for a context such as |x :: tau1, y ::
tau2, ...| are encoded as values of type |tau1 `times` tau2 `times` ...|

In this defunctionalization variant, instead of defining directly a GADT of
defunctionalized functions |Fun sigma tau|, we define a GADT of \emph{function
  codes} |Code env sigma tau|, whose values contain no environment. Type |Code|
is indexed not just by |sigma| and |tau| but also by the type of environments,
and has a constructor for each first-class function expression in the source
program, like |Fun sigma tau| does in conventional defunctionalization. We then
define |Fun sigma tau| as a pair of a function code of type |Code env sigma tau|
and an environment of type |env|.

As a downside, separating function codes adds a few indirections to the memory
representation of closures: for instance we use |(AddOne, ())| instead of
|AddOne|, and |(Pair, 1)| instead of |Pair 1|.

As an upside, with separate function codes we can define many operations
generically across all function codes (see \cref{sec:defunc-func-changes}),
instead of generating definitions matching on each function. What's more, we
later define operations that use raw function codes and need no environment; we
could alternatively define function codes without using them in the
representation of function values, at the expense of even more code duplication.
%
Code duplication is especially relevant because we currently perform
defunctionalization by hand, though we are confident it would be conceptually
straightforward to automate the process.\pg{Revise this.}

Defunctionalizing the program with separate function codes produces the
following GADT of function codes:
\begin{code}
type Env env = (NilChangeStruct env, NilTestable env)
data Code1 env sigma tau where
  AddOne1   ::               Code1 ()     Int    Int
  Pair1     ::               Code1 sigma  tau    (sigma, tau)
  MapPair1  :: Env sigma =>  Code1 [tau]  sigma  [(sigma, tau)]
\end{code}
\pg{Justify the |Env env| there.} We also require an interpretation function
|applyCode| for function codes. If |c| is the code for a function |f = \x -> t|,
calling |applyCode c| computes |f|'s output from an environment |env| for |f|
and an argument for |x|.
\begin{code}
applyCode1 ::  Code1 env sigma tau ->  env ->  sigma ->  tau
applyCode1     AddOne1                 ()      x      =  x + 1
applyCode1     Pair1                   x       y      =  (x, y)
applyCode1     MapPair1                ys      x      =  mapDF1 (F1 (Pair1, x)) ys
\end{code}

To define defunctionalized function values, we define a type synonym |RawFun1 env sigma tau| for
the product of |Code env sigma tau| and |env|. Then we encode type |sigma ->
tau| through type |Fun sigma tau|, defined as |RawFun1 env sigma tau| where
|env| is existentially bound.
\begin{code}
type RawFun1 env sigma tau = (Code1 env sigma tau, env)
data Fun1 sigma tau where
  F1 :: RawFun1 env sigma tau -> Fun1 sigma tau
\end{code}
To interpret defunctionalized function values, we wrap |applyCode1| in a new
version of |applyFun1|, having the same interface as the earlier |applyFun0|.
\begin{code}
applyFun1 :: Fun1 sigma tau -> sigma -> tau
applyFun1 (F1 (code, env)) arg = applyCode1 code env arg
\end{code}

The rest of the source program is defunctionalized like before, using the new
definition of |Fun sigma tau| and of |applyFun1|.

% Not shown.
\pg{show this maybe?}
%if style == newcode
\begin{code}
mapDF1 :: Fun1 sigma tau -> [sigma] -> [tau]
mapDF1 f [] = []
mapDF1 f (x : xs) = applyFun1 f x : mapDF1 f xs

dmapDF1 :: Fun1 sigma tau -> DFun1 sigma tau -> [sigma] -> Dt [sigma] -> Dt [tau]
dmapDF1 = undefined
\end{code}
%endif

\subsection{Defunctionalizing function changes}
\label{sec:defunc-func-changes}
Defunctionalization encodes function values as pairs of function codes and
environments. In ILC, a function value can change because the environment
changes or because the whole closure is replaced by a different one, with a
different function code and different environment. For now, we focus on
environment changes for simplicity. To allow inspecting function changes, we
defunctionalize them as well, but treat them specially.

Assume we want to defunctionalize a function change |df| with type |Dt^(sigma ->
tau) = sigma -> Dt^sigma -> Dt^tau|, valid for function |f : sigma -> tau|.
Instead of transforming type |Dt^(sigma -> tau)| into |Fun sigma (Fun Dt^sigma
Dt^tau)|, we transform |Dt^(sigma -> tau)| into a new type |DFun sigma tau|, the
change type of |Fun sigma tau| (|Dt^(Fun sigma tau) = DFun sigma tau|).
%
To apply |DFun sigma tau| we introduce an interpreter |dapplyFun1 :: Fun sigma
tau -> Dt^(Fun sigma tau) -> Dt^(sigma -> tau)|, or equivalently |dapplyFun1 ::
Fun sigma tau -> DFun sigma tau -> sigma -> Dt^sigma -> Dt^tau|, which also
serves as derivative of |applyFun1|.
\pg{Or maybe we first do untyped static caching and then defunctionalization?}

Like we did for |Fun sigma tau|, we define |DFun sigma tau| using function
codes. That is, |DFun sigma tau| pairs a function code |Code env sigma tau|
together with an environment change and a change structure for the environment
type.

\begin{spec}
data DFun1 sigma tau = forall env . ChangeStruct env => DF1 (Dt^env, Code1 env sigma tau)
\end{spec}

Without separate function codes, the definition of |DFun1| would have to include
one case for each first-class function.

\subsubsection{Environment changes}
\label{sec:defunc-env-changes}
Instead of defining change structures for environments, we encode environments
using tuples and define change structures for tuples.

We define first change structures for empty tuples and pairs:
\cref{sec:envs-without-base-inputs-intro}
\pg{Maybe these change structures are needed earlier?}
\begin{code}
instance ChangeStruct () where
  type Dt^() = ()
  _ `oplus` _ = ()
  oreplace _ = ()
instance (ChangeStruct a, ChangeStruct b) => ChangeStruct (a, b) where
  type Dt^(a, b) = (Dt^a, Dt^b)
  (a, b) `oplus` (da, db) = (a `oplus` da, b `oplus` db)
  oreplace (a2, b2) = (oreplace a2, oreplace b2)
\end{code}

To define change structures for $n$-uples of other arities we have two choices,
which we show on triples |(a, b, c)| and can be easily generalized.

We can encode triples as nested pairs |(a, (b, (c, ())))|. Or we can define
change structures for triples directly:

\begin{code}
instance (ChangeStruct a, ChangeStruct b,
  ChangeStruct c) => ChangeStruct (a, b, c) where

  type Dt^(a, b, c) = (Dt^a, Dt^b, Dt^c)
  (a, b, c) `oplus` (da, db, dc) = (a `oplus` da, b `oplus` db, c `oplus` dc)
  oreplace (a2, b2, c2) = (oreplace a2, oreplace b2, oreplace c2)
\end{code}

Generalizing from pairs and triples, one can define similar instances for
$n$-uples in general (say, for values of $n$ up to some high threshold).
%

% In fact, we can also replace a function value by another one with different
% code. However, for now we set aside support for this case; as we will see, for
% that case we can simply support replacing a function value with a new code and
% associated environment, that is, simply support a replacement change.

\pg{}
\subsubsection{Validity and ⊕ on defunctionalized function changes}
A function change |df| is valid for |f| if |df| has the same function code as
|f| and if |df|'s environment change is valid for |f|'s environment:
\[|fromto (Fun sigma tau) (F rho1 c) (DF drho c) (F rho2 c) = fromto env rho1
  drho rho2|\] where |c| is a function code of type |Code env sigma tau|, and
where |c|'s type binds the type variable |env| we use on the right-hand side.

Next, we implement |`oplus`| on function changes to match our definition of
validity, as required. We only need |f `oplus` df| to give a result if |df| is a
valid change for |f|. Hence, if the function code embedded in |df| does not
match the one in |f|, we give an error.\footnote{We originally specified
|`oplus`| as a total function to avoid formalizing partial functions, but as
mentioned in \cref{sec:change-intro}, we do not rely on the behavior of
|`oplus`| on invalid changes.}
However, our first attempt does not typecheck, since the typechecker does not
know whether the environment and the environment change have compatible types.
\begin{spec}
instance ChangeStruct (Fun1 sigma tau) where
  type Dt^(Fun1 sigma tau) = DFun1 sigma tau
  F1 (env, c1) `oplus` DF1 (denv, c2) =
    if c1 == c2 then
      F1 (env `oplus` denv) c1
    else
      error "Invalid function change in oplus"
\end{spec}

%format ~ = "\sim"

In particular, |env `oplus` denv| is reported as ill-typed, because we don't
know that |env| and |denv| have compatible types. Take |c1 = Pair1, c2 =
MapPair1, f = F1 (env, Pair1) :: sigma -> tau| and |df = DF1 (denv, MapPair1) ::
Dt^(sigma -> tau)|. Assume we evaluate |f `oplus` df = F1 (env, Pair1) `oplus`
DF1 (denv, MapPair1)|: there, indeed, |env :: sigma| and |denv :: [tau]|, so
|env `oplus` denv| is not type-correct. Yet, evaluating |f `oplus` df| would
\emph{not} fail, because |MapPair1| and |Pair1| are different, |c1 == c2| will
return false and |env `oplus` denv| won't be evaluated. But the typechecker does
not know that.

% Indeed, if |c1| and |c2| are different, |env|
% and |denv| have different types as well: |env :: env1| and |denv :: Dt^env2|,
% where |env1| is an existential type variable brought in scope by matching on |F
% env c1|, while |env2| is brought in scope by matching on |DF denv c2|. And even
% if |c1 == c2|, the typechecker does not learn that |c1| and |c2| have the same
% type and in particular that |env1 ~ env2| (where |~| denotes type equivalence in
% Haskell).

Hence we need an equality operation that produces a witness of type equality. We
define the needed infrastructure with few lines of code. First, we need a GADT
of witnesses of type equality; we can borrow from GHC's standard library its
definition, which is just:

\pg{add link, not ``in GHC 8.0''}
\begin{code}
-- From Data.Type.Equality
data tau1 :~: tau2 where
  Refl :: tau :~: tau
\end{code}
Assume |x :: tau1 :~: tau2|: by standard GADT typing rules, if |x| matches |Refl|
then |tau1| and |tau2| are equal and we write (with Haskell syntax) |tau1 ~
tau2|. Even if |tau1 :~: tau2| has only constructor |Refl|, a match is necessary
since |v| might be bottom. Readers familiar with type theory, Agda or Coq will
recognize that |(:~:)| resembles Agda's propositional equality or Martin-Löf's
identity types, even though it can only represents equality between types and
not between values.

Next, we define a new equality operation on codes. For equal codes, this
operation produces a witness that their environment types match, otherwise
nothing. Using this operation, we can complete the above instance of
|ChangeStruct (Fun1 sigma tau)|.

% codeMatch1 :: Code1 env1 sigma1 tau1 -> Code1 env2 sigma2 tau2 -> IsEq (env1, sigma1, tau1) (env2, sigma2, tau2)
\begin{code}
codeMatch1 :: Code1 env1 sigma tau -> Code1 env2 sigma tau -> Maybe (env1 :~: env2)
codeMatch1 AddOne1 AddOne1 = Just Refl
codeMatch1 Pair1 Pair1 = Just Refl
codeMatch1 MapPair1 MapPair1 = Just Refl
codeMatch1 _ _ = Nothing

instance ChangeStruct (Fun1 sigma tau) where
  type Dt^(Fun1 sigma tau) = DFun1 sigma tau
  (F1 (c1, env)) `oplus` (DF1 (c2, denv)) =
    case codeMatch1 c1 c2 of
      Just Refl -> F1 (c1, env `oplus` denv)
      Nothing -> error "Invalid function change in oplus"
\end{code}

\subsubsection{Applying function changes}
After defining environment changes, we define an incremental interpretation
function |dapplyCode|. If |c| is the code for a function |f = \x -> t|, as
discussed, calling |applyCode c| computes the output of |f| from an environment
|env| for |f| and an argument for |x|. Similarly, calling |dapplyCode c|
computes the output of |derive(f)| from an environment |env| for |f|, an
environment change |denv| valid for |env|, an argument for |x| and an argument
change |dx|.

% To implement function application, we first need to define how to interpret the
% function code for |f| as the derivative of |f| \pg{nonsense sentence.}, that is,
% a mapping from function codes to the behavior of their derivatives.
% %
% We define hence |dapplyCode1| for the interpreter of function codes
% |applyCode1|.

In our example, we have
\begin{code}
dapplyCode1 ::  Code1 env sigma tau ->  env ->  Dt^env ->  sigma ->  Dt^sigma ->     Dt^tau
dapplyCode1     AddOne1                 ()      ()         x         dx           =  dx
dapplyCode1     Pair1                   x       dx         y         dy           =  (dx, dy)
dapplyCode1     MapPair1                ys      dys        x         dx           =
  dmapDF1 (F1 (Pair1, x)) (DF1 (Pair1, dx)) ys dys
\end{code}

On top of |dapplyCode1| we can define |dapplyFun1|
% We can start by
% simply adding a derivative for |applyFun1|:
% \begin{code}
% dapplyFun1 :: Fun1 sigma tau -> DFun1 sigma tau -> sigma -> Dt^sigma -> Dt^tau
% dapplyFun1 (F1 (c1, env)) (DF1 (c2, denv)) = undefined
% \end{code}
\begin{code}
dapplyFun1 :: Fun1 sigma tau -> DFun1 sigma tau -> sigma -> Dt^sigma -> Dt^tau
dapplyFun1 (F1 (c1, env)) (DF1 (c2, denv)) x dx =
  case codeMatch1 c1 c2 of
    Just Refl -> dapplyCode1 c1 env denv x dx
    Nothing -> error "Invalid function change in dapplyFun"
\end{code}

\pg{resume}
Next, we add support for derivatives and function changes.
% We can start by
% simply adding a derivative for |applyFun1|:
% \begin{code}
% dapplyFun1 :: Fun1 sigma tau -> DFun1 sigma tau -> sigma -> Dt^sigma -> Dt^tau
% dapplyFun1 (F1 (c1, env)) (DF1 (c2, denv)) = undefined
% \end{code}
\begin{code}
dapplyFun1 :: Fun1 sigma tau -> DFun1 sigma tau -> sigma -> Dt^sigma -> Dt^tau
dapplyFun1 (F1 (c1, env)) (DF1 (c2, denv)) x dx =
  case codeMatch1 c1 c2 of
    Just Refl -> dapplyCode1 c1 env denv x dx
    Nothing -> error "Invalid function change in dapplyFun"
\end{code}

However, we can also implement further accessors that inspect function changes.
We can now finally detect if a change is nil. To this end, we first define a
typeclass that allows testing changes to determine if they're nil:
\begin{code}
class NilTestable t where
  isNil :: Dt^t -> Bool
\end{code}
Now, a function change is nil only if the contained environment is nil.
\begin{spec}
instance NilTestable (Fun1 sigma tau) where
  isNil :: DFun1 sigma tau -> Bool
  isNil (DF1 (denv, code)) = isNil denv
\end{spec}
However, this definition of |isNil| only works given a typeclass instance for
|NilTestable env|; we need to add this requirement as a constraint, but we
cannot add it to |isNil|'s type signature since type variable |env| is not in
scope there.
Instead, we must add the constraint where we introduce it by existential
quantification, just like the constraint |ChangeStruct env|.

\begin{code}
data DFun1 sigma tau = forall env . (NilTestable env, ChangeStruct env) => DF1 (Code1 env sigma tau, Dt^env)
\end{code}

\begin{code}
instance NilTestable (Fun1 sigma tau) where
  isNil :: DFun1 sigma tau -> Bool
  isNil (DF1 (code, denv)) = isNil denv
\end{code}

We can then wrap a derivative to return a nil change immediately if at runtime
all input changes turn out to be nil. This was not possible in the setting
described by \citet{CaiEtAl2014ILC}, because
nil function changes could not be detected at runtime, only at compile time.

\pg{Can we in this context?}
% \begin{code}
% wrapDF :: DFun sigma tau -> sigma -> Dt^sigma -> Dt^tau
% wrapDF f df x dx =
%   if isNil df then
%     nil (f x)
%   else
%
% \end{code}
%
% \begin{code}
% wrapDer1 g df c =
%   case isNilFun df of
%     Nil -> (onil Proxy, c)
%     NotNil -> g df c
% \end{code}
