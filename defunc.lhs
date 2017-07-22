% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

%if style == newcode
\begin{code}
{-# LANGUAGE ExistentialQuantification, TypeFamilies, TypeFamilyDependencies,
  InstanceSigs, GADTs, TypeOperators, ConstraintKinds #-}
import qualified Data.Sequence as S
import Data.Sequence(Seq)
import GHC.Exts (Constraint)
import Data.Proxy (Proxy(Proxy))
import Control.Arrow ((***))
import Prelude hiding (map, concatMap)
\end{code}
%endif

\chapter{Defunctionalizing function changes}
\label{ch:defunc-fun-changes}

In~\cref{ch:derive-formally}, and throughout most of~\cref{part:incr}, we represent
function changes as functions, which can only be applied.
However, incremental programs often inspect changes to decide how to
react to them most efficiently. Also inspecting function changes would help
performance further.
Representing function changes as closures, as we do in~\cref{ch:cts}
and~\cref{ch:bsos}, allows implementing some operations more efficient, but is
not fully satisfactory.
In this chapter, we address these restrictions by \emph{defunctionalizing}
functions and function changes, so that we can inspect both at runtime without
restrictions.

% In particular, by encoding functions and functions changes as
% values of algebraic datatypes, it becomes possible to test whether the function
% change is a nil change for the function.

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
and show that operations on defunctionalized function changes become cheaper.
% and show its benefits.\pg{Furthermore, other operations on function and
%   function changes become cheaper, such as |`oplus`|, |nilc|, and so on.}
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
\label{sec:change-struct-tc}

We write incremental programs based on ILC by manually writing Haskell code,
containing both manually-written plugin code, and code that is transformed
systematically, based on informal generalizations and variants of
|derive(param)|. Our main goal is to study variants of differentiation and of
encodings in Haskell, while also studying language plugins for non-trivial
primitives, such as different sorts of collections. We make liberal use of GHC
extensions where needed.

Code in this chapter has been extracted and type-checked, though we elide a few
details (mostly language extensions and imports from the standard library).
Code in this \lcnamecref{ch:defunc-fun-changes} is otherwise self-contained.
We have also tested a copy of this code more extensively.

As sketched before, we define change structure inside Haskell.
%We choose for now a different subset of operations.
%if style == newcode
\begin{code}
class ChangeStruct t where
  -- Next line declares |Dt^t| as an injective type function
  type Dt^t = r | r -> t

  oplus :: t -> Dt^t -> t
  oreplace :: t -> Dt^t

class ChangeStruct t => NilChangeStruct t where
  nil :: t -> Dt^t

class ChangeStruct a => CompChangeStruct a where
  ocompose :: Dt^a -> Dt^a -> Dt^a

-- Omitted from typeset code but used once!
class ChangeStruct t => OnilChangeStruct t where
  -- Proxy is used to encode explicit type application.
  onil :: Proxy t -> Dt^t
\end{code}
%else
\begin{code}
class ChangeStruct t where
  -- Next line declares |Dt^t| as an injective type function
  type Dt^t = r | r -> t

  oplus :: t -> Dt^t -> t
  oreplace :: t -> Dt^t

class ChangeStruct t => NilChangeStruct t where
  nilc :: t -> Dt^t

class ChangeStruct a => CompChangeStruct a where
  -- Compose change |dx1| with |dx2|, so that
  -- |x `oplus` (dx1 `ocompose` dx2) == x `oplus` dx1 `oplus` dx2|.
  (`ocompose`) :: Dt^a -> Dt^a -> Dt^a
\end{code}
%endif
%ocompose :: Dt^t -> Dt^t -> Dt^t
With this code we define type classes |ChangeStruct|, |NilChangeStruct| and
|CompChangeStruct|. We explain each of the declared members in turn.

First, type |Dt^t| represents the change type for type |t|. To improve Haskell
type inference, we declare that |Dt| is injective, so that |Dt^t1 = Dt^t2|
implies |t1 = t2|. This forbids some potentially useful change structures, but
in exchange it makes type inference vastly more usable.

Next, we declare |`oplus`|, |nilc| and |`ocompose`| as available to object programs.
%
Last, we introduce |oreplace| to construct replacement
changes, characterized by the \emph{absorption law} |x `oplus` oreplace y = y|
for all |x|.
Function |oreplace| encodes |!t|, that is the bang operator. We use a different
notation because |!| is reserved for other purposes in Haskell.

These typeclasses omit operation |`ominus`| intentionally: we do \emph{not}
require that change structures support a proper difference operation.
Nevertheless, as discussed |b `ominus` a| can be expressed through |oreplace b|.

We can then differentiate Haskell functions---even polymorphic ones. We show a
few trivial examples to highlight how derivatives are encoded in Haskell,
especially polymorphic ones.
%if style /= newcode
%format apply0 = apply
%format dapply0 = dapply
%format id0 = id
%endif
\begin{code}
-- The standard |id| function:
id0 :: a -> a
id0 x = x
-- and its derivative:
did :: a -> Dt^a -> Dt^a
did x dx = dx

instance (  NilChangeStruct a, ChangeStruct b) =>
            ChangeStruct (a -> b) where
  type Dt^(a -> b) = a -> Dt^a -> Dt^b
  f `oplus` df = \x -> f x `oplus` df x (nil x)
  oreplace f = \x dx -> oreplace (f (x `oplus` dx))

instance (  NilChangeStruct a, ChangeStruct b) =>
            NilChangeStruct (a -> b) where
  nil f = oreplace f

-- Same for |apply|:
apply0 :: (a -> b) -> a -> b
apply0 f x = f x
dapply0 :: (a -> b) -> Dt^(a -> b) -> a -> Dt^a -> Dt^b
dapply0 f df x dx = df x dx
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
While we discuss such topics in~\cref{ch:diff-parametricity-system-f}, we avoid
them here.

Second, prenex polymorphism is a small extension of simply-typed lambda calculus
metatheoretically. We can treat prenex-polymorphic definitions as families of
monomorphic (hence simply-typed) definitions; to each definition we can apply
all the ILC theory we developed to show differentiation is correct.
% Alternatively, we can regard type variables as additional base types without
% primitives, so that we can treat our function definitions as one functions.

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
\texths %drop extra space around figure
% From https://tex.stackexchange.com/a/186335/1340
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
terms |\y -> (x, y)|, that we call |pair1|, |\x -> map (\y -> (x, y)) ys|,
that we call |mapPair|, and |\x -> x + 1|, that we call |addOne|.
Defunctionalization creates a type |Fun sigma tau| with a constructor for each
of the three terms, respectively |Pair|, |MapPair| and |AddOne|.
Both |pair1| and |mapPair| close over some free variables, so their
corresponding constructors will take an argument
for each free variable; for |pair1| we have
%
\[|x :: sigma /- \y -> (x, y) :: tau -> (sigma, tau)|,\]
%
while for |mapPair| we have
%
\[|ys :: [tau] /- \x -> map (\y -> (x, y)) ys :: sigma -> [(sigma, tau)]|.\]
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
\texths %drop extra space around figure
% From https://tex.stackexchange.com/a/186335/1340
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
\caption{Defunctionalized program.}
\label{prog:defunc-curried}
\end{figure}

Some readers might notice this program still uses first-class function, because
it encodes multi-argument functions through currying. To get a fully first-order
program, we encode multi-arguments functions using tuples instead of currying.%
\footnote{Strictly speaking, the resulting program is still not first-order,
  because in Haskell multi-argument data constructors, such as the pair
  constructor $(\mathord{,})$ that we use, are still first-class curried functions, unlike
  for instance in OCaml. To make this program truly first-order, we must
  formalize tuple constructors as a term constructor, or formalize these
  function definitions as multi-argument functions. At this point, this
  discussion is merely a technicality that does not affect our goals, but it
  becomes relevant if we formalize the resulting first-order
  language as in~\cref{sec:formalization}.}
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
type Env env = (CompChangeStruct env, NilTestable env)
data Code1 env sigma tau where
  AddOne1   ::               Code1 ()     Int    Int
  Pair1     ::               Code1 sigma  tau    (sigma, tau)
  MapPair1  :: Env sigma =>  Code1 [tau]  sigma  [(sigma, tau)]
\end{code}
In this definition, type |Env| names a set of typeclass constraints on the type
of the environment, using the |ConstraintKinds| GHC language
extension.
Satisfying these constraints is necessary to implement a few operations on
functions.
We also require an interpretation function
|applyCode| for function codes. If |c| is the code for a function |f = \x -> t|,
calling |applyCode c| computes |f|'s output from an environment |env| for |f|
and an argument for |x|.
\begin{code}
applyCode1 ::  Code1 env sigma tau ->  env ->  sigma ->  tau
applyCode1     AddOne1                 ()      x      =  x + 1
applyCode1     Pair1                   x       y      =  (x, y)
applyCode1     MapPair1                ys      x      =  mapDF1 (F1 (Pair1, x)) ys
\end{code}
The implementation of |applyCode1 MapPair1| only works because of the |Env sigma|
constraint for constructor |MapPair1|: this constraint is required when
constructing the defunctionalized function value that we pass as argument to |mapDF1|.

We represent defunctionalized function values through type |RawFun1 env
sigma tau|,
a type synonym of the product of |Code env sigma tau| and |env|. We encode type |sigma ->
tau| through type |Fun sigma tau|, defined as |RawFun1 env sigma tau| where
|env| is existentially bound. We add constraint |Env env| to the definition of
|Fun sigma tau|, because implementing |`oplus`| on function changes will require
using |`oplus`| on environments.
\begin{code}
type RawFun1 env sigma tau = (Code1 env sigma tau, env)
data Fun1 sigma tau where
  F1 :: Env env => RawFun1 env sigma tau -> Fun1 sigma tau
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

dmapDF1 :: Fun1 sigma tau -> DFun1 sigma tau -> [sigma] -> Dt^[sigma] -> Dt^[tau]
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
\pg{Or maybe we first do CTS and then defunctionalization?}

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
instance (  ChangeStruct a, ChangeStruct b,
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

In particular, |env `oplus` denv| is reported as ill-typed, because we don't
know that |env| and |denv| have compatible types. Take |c1 = Pair1, c2 =
MapPair1, f = F1 (env, Pair1) :: sigma -> tau| and |df = DF1 (denv, MapPair1) ::
Dt^(sigma -> tau)|. Assume we evaluate |f `oplus` df = F1 (env, Pair1) `oplus`
DF1 (denv, MapPair1)|: there, indeed, |env :: sigma| and |denv :: [tau]|, so
|env `oplus` denv| is not type-correct. Yet, evaluating |f `oplus` df| would
\emph{not} fail, because |MapPair1| and |Pair1| are different, |c1 == c2| will
return false and |env `oplus` denv| won't be evaluated. But the typechecker does
not know that.

Hence, we need an equality operation that produces a witness of type equality. We
define the needed infrastructure with few lines of code. First, we need a GADT
of witnesses of type equality; we can borrow from GHC's standard library its
definition, which is just:

\pg{add link, not ``in GHC 8.0''}
\begin{code}
-- From |Data.Type.Equality|
data tau1 :~: tau2 where
  Refl :: tau :~: tau
\end{code}
If |x| has type |tau1 :~: tau2| and matches pattern |Refl|, then by standard
GADT typing rules |tau1| and |tau2| are equal.
Even if |tau1 :~: tau2| has only constructor |Refl|, a match is necessary
since |x| might be bottom. Readers familiar with type theory, Agda or Coq will
recognize that |:~:| resembles Agda's propositional equality or Martin-Löf's
identity types, even though it can only represents equality between types and
not between values.

Next, we implement function |codeMatch| to compare codes. For equal codes, this
operation produces a witness that their environment types match.\footnote{%
If a code is polymorphic in the environment type, it must take as argument a
representation of its type argument, to be used to implement |codeMatch|.
We represent type arguments at runtime via instances of |Typeable|, and omit
standard details here.}
Using this operation, we can complete the above instance of
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
  F1 (c1, env) `oplus` DF1 (c2, denv) =
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

On top of |dapplyCode1| we can define |dapplyFun1|, which functions as a
a derivative for |applyFun1| and allows applying function changes:
\begin{code}
dapplyFun1 :: Fun1 sigma tau -> DFun1 sigma tau -> sigma -> Dt^sigma -> Dt^tau
dapplyFun1 (F1 (c1, env)) (DF1 (c2, denv)) x dx =
  case codeMatch1 c1 c2 of
    Just Refl -> dapplyCode1 c1 env denv x dx
    Nothing -> error "Invalid function change in dapplyFun"
\end{code}

% \pg{resume}
% Next, we add support for derivatives and function changes.
% % We can start by
% % simply adding a derivative for |applyFun1|:
% % \begin{code}
% % dapplyFun1 :: Fun1 sigma tau -> DFun1 sigma tau -> sigma -> Dt^sigma -> Dt^tau
% % dapplyFun1 (F1 (c1, env)) (DF1 (c2, denv)) = undefined
% % \end{code}
% \begin{code}
% dapplyFun1 :: Fun1 sigma tau -> DFun1 sigma tau -> sigma -> Dt^sigma -> Dt^tau
% dapplyFun1 (F1 (c1, env)) (DF1 (c2, denv)) x dx =
%   case codeMatch1 c1 c2 of
%     Just Refl -> dapplyCode1 c1 env denv x dx
%     Nothing -> error "Invalid function change in dapplyFun"
% \end{code}

However, we can also implement further accessors that inspect function changes.
We can now finally detect if a change is nil. To this end, we first define a
typeclass that allows testing changes to determine if they're nil:
\begin{code}
class NilChangeStruct t => NilTestable t where
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
quantification, just like the constraint |ChangeStruct env|. In particular, we
can reuse the constraint |Env env|.
\begin{code}
data DFun1 sigma tau =
  forall env . Env env =>
  DF1 (Code1 env sigma tau, Dt^env)

instance NilChangeStruct (Fun1 sigma tau) where
  nil (F1 (code, env)) = DF1 (code, nil env)
instance NilTestable (Fun1 sigma tau) where
  isNil :: DFun1 sigma tau -> Bool
  isNil (DF1 (code, denv)) = isNil denv
\end{code}

We can then wrap a derivative via function |wrapDF| to return a nil change immediately if at runtime
all input changes turn out to be nil. This was not possible in the setting
described by \citet{CaiEtAl2014ILC}, because
nil function changes could not be detected at runtime, only at compile time.
To do so, we must produce directly a nil change for |v = applyFun1 f x|. To avoid
computing |v|, we assume we can compute a nil change for |v| without access to
|v| via operation |onil| and typeclass |OnilChangeStruct| (omitted here);
argument |Proxy| is a constant required for purely technical reasons.
\begin{code}
wrapDF :: OnilChangeStruct tau => Fun1 sigma tau -> DFun1 sigma tau -> sigma -> Dt^sigma -> Dt^tau
wrapDF f df x dx =
  if isNil df then
    onil Proxy -- Change-equivalent to |nil (applyFun1 f x)|
  else
    dapplyFun1 f df x dx
\end{code}

\section{Defunctionalization and cache-transfer-style}
%\pg{Read!}
We can combine the above ideas with cache-transfer-style (\cref{ch:cts}). We
show the details quickly.

Combining the above with caching, we can use defunctionalization as described to
implement the following interface for functions in caches. For extra generality,
we use extension |ConstraintKinds| to allow instances to define the required
typeclass constraints.
\begin{code}
class FunOps k where
  type Dk k = (dk :: * -> * -> * -> * -> *) | dk -> k

  type ApplyCtx k i o :: Constraint
  apply :: ApplyCtx k i o => k i o cache -> i -> (o, cache)

  type DApplyCtx k i o :: Constraint
  dApply :: DApplyCtx k i o =>
    Dk k i o cache1 cache2 -> Dt^i -> cache1 -> (Dt^o, cache2)

  type DerivCtx k i o :: Constraint
  deriv :: DerivCtx k i o =>
    k i o cache -> Dk k i o cache cache

  type FunUpdCtx k i o :: Constraint
  funUpdate :: FunUpdCtx k i o =>
    k i o cache1 -> Dk k i o cache1 cache2 -> k i o cache2

  isNilFun :: Dk k i o cache1 cache2 -> Maybe (cache1 :~: cache2)

updatedDeriv ::
  (FunOps k, FunUpdCtx k i o, DerivCtx k i o) =>
  k i o cache1 -> Dk k i o cache1 cache2 -> Dk k i o cache2 cache2
updatedDeriv f df = deriv (f `funUpdate` df)
\end{code}
Type constructor |k| defines the specific constructor for the function type.
In this interface, the type of function changes |DK k i o cache1 cache2|
represents functions (encoded by type constructor |Dk k|) with inputs of type
|i|, outputs of type |o|, input cache type |cache1| and output cache type
|cache2|. Types |cache1| and |cache2| coincide for typical function changes, but
can be different for replacement function changes, or more generally for
function changes across functions with different implementations and cache types.
Correspondingly, |dApply| supports applying such changes across closures with
different implementations: unfortunately, unless the two implementations are
similar, the cache content cannot be reused.

To implement this interface it is sufficient to define a type of codes that
admits an instance of type-class |Codelike|. Earlier definitions of
|codeMatch1|, |applyFun1| and |dapplyFun1|, adapted to cache-transfer style.
\begin{code}
class Codelike code where
  codeMatch :: code env1 a1 r1 cache1 -> code env2 a2 r2 cache2 ->
    Maybe ((env1, cache1) :~: (env2, cache2))
  applyCode :: code env a b cache -> env -> a -> (b, cache)
  dapplyCode :: code env a b cache -> Dt^env -> Dt^a -> cache -> (Dt^b, cache)
\end{code}
Typically, a defunctionalized program uses no first-class functions and has a
single type of functions. Having a type class of function codes weakens that
property. We can still use a single type of codes throughout our program; we can
also use different types of codes for different parts of a program, without
allowing for communications between those parts.
% Defining such instances
% %Observe that |dapply| produces caches

On top of the |Codelike| interface, we can define instances of interface |FunOps| and
|ChangeStruct|. To demonstrate this, we show a complete implementation in
\cref{fig:chs-codelike,fig:funops-codelike}.
Similarly to |`oplus`|, we can implement |`ocompose`| by comparing codes
contained in function changes; this is not straightforward when using closure
conversion as in \cref{sec:incr-nest-loop}, unless we store even more type
representations.
% In representations using closure conversion , it is
% possible to apply functions to correspondingly caches and to update a function
% with a function change, but it is not possible to define the change composition
% of two function changes.

We can detect nil changes at runtime even in cache-passing style. We can for
instance define function |wrapDer1| which does something trickier than |wrapDF|:
here we assume that |dg| is a derivative taking function change |df| as
argument. Then, if |df| is nil, |dg df| must also be nil, so we can return a nil
change directly, together with the input cache.
The input cache has the required type because in this case, the type |cache2| of
the desired output cache has matches type |cache1| of the input cache (because
we have a nil change |df| across them): the return value of |isNilFun| witnesses
this type equality.
\begin{code}
wrapDer1 ::
  (FunOps k, OnilChangeStruct r') =>
  (Dk k i o cache1 cache2 -> f cache1 -> (Dt^r', f cache2)) ->
  (Dk k i o cache1 cache2 -> f cache1 -> (Dt^r', f cache2))
wrapDer1 dg df c =
  case isNilFun df of
    Just Refl -> (onil Proxy, c)
    Nothing -> dg df c
\end{code}

We can also hide the difference between difference cache types by defining a
uniform type of caches, |Cache code|.
To hide caches, we can use a pair of a cache (of type |cache|)
and a code for that cache type. When applying a function (change) to a cache, or
when composing the function, we can compare the function code with the cache
code.

In this code we have not shown support for replacement values for functions; we
leave details to our implementation.

\begin{figure}[p]
\texths %drop extra space around figure
% From https://tex.stackexchange.com/a/186335/1340
\begin{code}
type RawFun a b code env cache = (code env a b cache, env)
type RawDFun a b code env cache = (code env a b cache, Dt^env)

data Fun a b code = forall env cache . Env env =>
  F (RawFun a b code env cache)
data DFun a b code = forall env cache . Env env =>
  DF (RawDFun a b code env cache)

-- This cache is not indexed by |a| and |b|
data Cache code = forall a b env cache . C (code env a b cache) cache

-- Wrapper
data FunW code a b cache where
  W :: Fun a b code -> FunW code a b (Cache code)

data DFunW code a b cache1 cache2 where
  DW :: DFun a b code -> DFunW code a b (Cache code) (Cache code)

derivFun :: Fun a b code -> DFun a b code
derivFun (F (code, env)) = DF (code, nil env)

oplusBase :: Codelike code => Fun a b code -> DFun a b code -> Fun a b code
oplusBase (F (c1, env)) (DF (c2, denv)) =
  case codeMatch c1 c2 of
    Just Refl ->
      F (c1, env `oplus` denv)
    _ -> error "INVALID call to oplusBase!"

ocomposeBase :: Codelike code => DFun a b code -> DFun a b code -> DFun a b code
ocomposeBase (DF (c1, denv1)) (DF (c2, denv2)) =
  case codeMatch c1 c2 of
    Just Refl ->
      DF (c1, denv1 `ocompose` denv2)
    _ -> error "INVALID call to ocomposeBase!"

instance Codelike code => ChangeStruct (Fun a b code) where
  type Dt^(Fun a b code) = DFun a b code
  oplus = oplusBase

instance Codelike code => NilChangeStruct (Fun a b code) where
  nil (F (c, env)) = DF (c, nil env)

instance Codelike code => CompChangeStruct (Fun a b code) where
  ocompose df1 df2 = ocomposeBase df1 df2

instance Codelike code => NilTestable (Fun a b code) where
  isNil (DF (c, env)) = isNil env
\end{code}
\caption{Implementing change structures using |Codelike| instances.}
\label{fig:chs-codelike}
\end{figure}

\begin{figure}[p]
\texths %drop extra space around figure
% From https://tex.stackexchange.com/a/186335/1340
\begin{code}
applyRaw :: Codelike code => RawFun a b code env cache -> a -> (b, cache)
applyRaw (code, env) = applyCode code env

dapplyRaw :: Codelike code => RawDFun a b code env cache -> Dt^a -> cache -> (Dt^b, cache)
dapplyRaw (code, denv) = dapplyCode code denv

applyFun :: Codelike code => Fun a b code -> a -> (b, Cache code)
applyFun (F f@(code, env)) arg =
  (id *** C code) $ applyRaw f arg

dapplyFun :: Codelike code => DFun a b code -> Dt^a -> Cache code -> (Dt^b, Cache code)
dapplyFun (DF (code1, denv)) darg (C code2 cache1) =
  case codeMatch code1 code2 of
    Just Refl ->
      (id *** C code1) $ dapplyCode code1 denv darg cache1
    _ -> error "INVALID call to dapplyFun!"


instance Codelike code => FunOps (FunW code) where
  type Dk (FunW code) = DFunW code
  apply (W f) = applyFun f
  dApply (DW df) = dapplyFun df
  deriv (W f) = DW (derivFun f)
  funUpdate (W f) (DW df) = W (f `oplus` df)
  isNilFun (DW df) =
    if isNil df then
      Just Refl
    else
      Nothing
\end{code}
\caption{Implementing |FunOps| using |Codelike| instances.}
\label{fig:funops-codelike}
\end{figure}

%  LocalWords:  dapplyFun dapply oreplace ChangeStruct Codelike RawFun
