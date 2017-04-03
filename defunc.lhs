% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

%if style == newcode
\begin{code}
{-# LANGUAGE ExistentialQuantification, TypeFamilies, TypeFamilyDependencies,
InstanceSigs, GADTs #-}
\end{code}
%endif

\chapter{Defunctionalizing function changes}
\label{ch:defunc-fun-changes}

Up to now we have represented function changes as functions, which can only be
applied. However, incremental programs often inspect changes to decide how to
react to them most efficiently. Inspecting function changes would also help
performance. In this chapter, we address these restrictions by
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
  function changes become cheaper, such as |oplus|, |nilc|, and so on.}
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
We write incremental programs based on ILC by manually writing Haskell code,
containing both manually-written plugin code, and code that is transformed
systematically, based on informal generalizations and variants of
|derive(param)|. Our main goal is to study variants of differentiation and of
encodings in Haskell, while also studying language plugins for non-trivial
primitives, such as different sorts of collections.

As sketched before, we internalize change structures in Haskell as follows:
\begin{code}
class ChangeStruct t where
  -- Next line declares |Dt^t| as an injective type function
  type Dt^t = r | r -> t

  oplus :: t -> Dt^t -> t
  oreplace :: t -> Dt^t

class ChangeStruct t => NilChangeStruct t where
  nil :: t -> Dt^t
\end{code}
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
  oplus f df = \x -> f x `oplus` df x (nil x)
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
only support ML (or prenex) polymorphism polymorphism, not first-class
polymorphism, for two reasons.

First, with first-class polymorphism, we can encode
existential types |exists X. T|, and two values of the same existential type
|v1, v2 :: exists X. T| can pack different types inside. Hence, a change between
|v1| and |v2| requires handling changes between types.

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
In a typed language supporting generalized algebraic datatypes (GADTs),
defunctionalization transforms the type of function values |sigma -> tau| to a
new type |Fun sigma tau| of defunctionalized function values, indexed by both
|sigma| and |tau|~\citep{Pottier2004polymorphic}, together with an interpreter
for defunctionalized function values |apply :: Fun sigma tau -> sigma -> tau|.
The resulting programs are expressed in a first-order subset of the original
programming language, where all proper functions are top-level definitions.

For instance, we imagine a program having closures |\x -> x + 1| and |\x -> x +
y|, where |y :: Int|.
\begin{figure}
\begin{code}
applyToInts :: (Int -> a) -> [a]
applyToInts f =
  [f 0, f 1]

getList :: [Int]
getList =
  let  l1 = applyToInts (\x -> x + 1)
       y = 2
       l2 = applyToInts (\x -> x + y)
  in   l1 ++ l2
\end{code}
\caption{A small program that we use as an example for defunctionalization.}
\label{fig:defunc-example}
\end{figure}
\pg{Can we incrementalize this? Hmm... Maybe take already the running example on
sequences?}


\pg{Defunctionalize all functions? Both variants? For now we don't want codes
for all top-level functions, do we?}
For each lambda expression |l = \x -> t| in the source program, typed as |Gamma
/- \x -> t : sigma -> tau|, defunctionalization creates a constructor |C| of
|Fun sigma tau|.\footnote{More specifically, we only need codes for functions
that are used as first-class arguments, not for other functions, though codes
for the latter can be added as well.}
While lambda expression |l| closes \emph{implicitly} over
environment |rho : eval(Gamma)|, |C| closes over it explicitly: the values bound
to free variables in environment |rho| are passed as arguments to constructor
|c|.

We use a variant of defunctionalization: Instead of having a single type |Fun
sigma tau|, we defunctionalize functions from |sigma| to |tau| as pairs of a
function descriptor and a (possibly empty) environment. We separate the
environment because a variety of operations must manipulate it uniformly. To
this end, we define a GADT of function codes indexed by |Code env sigma tau|,
with a case for each lambda expression in the source program. We show, as an
example, cases for the program above\pg{figure}
\begin{code}
data Code env sigma tau where
  Add1 :: Code () Int Int
  AddY :: Code Int Int Int
  -- ...
\end{code}
We also require an interpretation function |applyCode|, taking a function
code, an environment and an input and producing an output.
\begin{code}
applyCode :: Code env sigma tau -> env -> sigma -> tau
applyCode Add1  ()  x = x + 1
applyCode AddY  y   x = x + y
\end{code}

A function |sigma -> tau| is encoded as a pair of an environment of type |env|
and a function |F env (Code env sigma tau)|. To bind type variable |env|, we use
a Haskell extension called |ExistentialQuantification|, that adds to Haskell a
form of existential types.
\begin{code}
data Fun sigma tau = forall env . F env (Code env sigma tau)
\end{code}
We can wrap |applyCode| into a more conventional |applyFun| function that
interprets defunctionalized function values:
\begin{code}
applyFun :: (Fun sigma tau) -> sigma -> tau
applyFun (F env c) arg = applyCode c env arg
\end{code}

%  CPair1 :: Code sigma tau (sigma, tau)
%  CMapPair1 :: Code [tau] sigma [(sigma, tau)]

ILC requires support for function changes because the environment can change.
Hence we start by representing function changes through environment changes.

\begin{code}
data DFun sigma tau = forall env . DP (Dt^env) (Code env sigma tau)
\end{code}

In fact, we can also replace a function value by another one with different
code. However, for now we set aside support for this case; as we will see, for
that case we can simply support replacing a function value with a new code and
associated environment, that is, simply support a replacement change.

Next, we add support for derivatives and function changes. We can start by
simply adding a derivative for |applyFun|:
\begin{code}
applyDFun :: (Fun sigma tau) -> (DFun sigma tau) -> sigma -> Dt^sigma -> Dt^tau
applyDFun = undefined
\end{code}

However, we can also implement further accessors that inspect function changes. We can now finally detect if a change is nil:
\begin{code}
isNil :: DFun sigma tau -> Bool
\end{code}

We can then wrap a derivative to return a nil change immediately if at runtime
all input changes turn out to be nil. This was not possible in PLDI'14, because
nil function changes could not be detected at runtime, only at compile time.
