% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Equational reasoning on changes}
\label{sec:term-reasoning}

In this chapter, we formalize equational reasoning
directly on terms, rather than on semantic values
(\cref{sec:denot-syntactic-reasoning}), and we discuss
when two changes can be considered equivalent
(\cref{sec:change-equivalence}).
We also show, as an example, a simple change structure on lists
and a derivative of |map| for it (\cref{ex:syn-changes-map}).

To reason on terms, instead of describing the updated value of a
term |t| by using an updated environment |rho2|, we substitute in
|t| each variable |x_i| with expression |x_i `oplus` dx_i|, to
produce a term that computes the updated value of |t|, so that we
can say that |dx| is a change from |x| to |x `oplus` dx|, or that
|df x dx| is a change from |f x| to |(f `oplus` df) (x `oplus`
dx)|. Lots of the work in this chapter is needed to modify
definitions, and go from using an updated environment to using
substitution in this fashion.

To compare for equivalence terms that use changes, we can't use
denotational equality, but must restrict to consider valid
changes.

Comparing changes is trickier: most often we are not interested
in whether two changes produce the same value, but whether two
changes have the same source and destination. Hence, if two
changes share source and destination we say they are \emph{equivalent}.
As we show in this chapter, operations that preserve validity also respect
\emph{change equivalence}, because for all those operations the source
and destination of any output changes only depend on source and
destination of input changes.
Among the same source and destination there often are multiple
changes, and the difference among them can affect how long a
derivative takes, but not whether the result is correct.

We also show that change equivalence is a particular form of
logical relation, a logical \emph{partial equivalence relation}
(PER). PERs are well-known to semanticists, and often used to
study sets with invalid elements together with the appropriate
equivalence on these sets.

The rest of the chapter expands on the details, even if they are
not especially surprising.
% Not all proofs in this chapter are mechanized, but many of them
% are routine.

\section{Reasoning on changes syntactically}
\label{sec:denot-syntactic-reasoning}
To define derivatives of primitives, we will often discuss
validity of changes directly on programs, for instance saying
that |dx| is a valid change from |x| to |x `oplus` dx|, or that
|f x `oplus` df x dx| is equivalent to |f (x `oplus` dx)| if all
changes in scope are valid.

In this section we formalize these notions. We have not
mechanized proofs involving substitutions, but we include them
here, even though they are not especially interesting.

But first, we exemplify informally these notions.
\pg{Maybe: We have a derivative we can generate but that is inadequate,
  we need to write better ones by hand. Or: we can't derive this yet.
Or: just change motivation.}
\begin{example}[Deriving |map| on lists]
  \label{ex:syn-changes-map}
We consider a basic change structure on lists and the
derivative of |map|. We will describe this example
informally, using Haskell notation and let polymorphism as
appropriate (see \cref{sec:intro-stlc}); to see how such a change
structure might be formalized, compare with the change structure
for environments described earlier in \cref{def:chs-envs}. We'll
describe a more realistic change structure for sequences later.

Consider a basic change structure on cons-lists of type
|List a|, where a list change is just a list of element changes
|List (Dt^a)|, and |List a| itself is defined as
follows (in Haskell notation):\footnote{
  We use |:| for typing throughout, hence we avoid Haskell's
  builtin list syntax, which uses |:| for cons cells.}
\begin{code}
  data List a = Nil | Cons a (List a)
\end{code}

A list change |dxs| is valid for source |xs| if
they have the same length and each element change is valid for
its corresponding element.
On this basic change structure, we can define |`oplus`| and
|`ocompose`| but not |`ominus`|: such list changes can't express the
difference between two lists of different lengths. We discuss
product and sum types more in general in \cref{ch:prod-sums}.
Nevertheless, this basic change structure is sufficient to define
derivatives that act correctly on the changes that can be expressed.
We can describe this change structure in Haskell using a
typeclass instance for class |BasicChangeStruct| (included):
\pg{Not the name we use elsewhere. And not the proper location.}
\begin{code}
class BasicChangeStruct a where
  type Dt^a
  oplus :: a -> Dt^a -> a
instance BasicChangeStruct (List a) where
  type Dt^(List a) = List (Dt^a)
  Nil `oplus` Nil = Nil
  (Cons x xs) `oplus` (Cons dx dxs) = Cons (x `oplus` xs) (dx `oplus` dxs)
  _ `oplus` _ = Nil
\end{code}

The following |dmap| function is a derivative for the
standard |map| function (included for comparison) and the given
change structure. We discuss derivatives for recursive functions
in \cref{sec:general-recursion}.
% We can write a standard |map| function on this list, and also its derivative |dmap| as follows:
% If we define |map : List a -> List a| as a primitive, and not as
% a derived function defined in terms of some other primitive, we
% can write derivative |dmap| as follows (in Haskell notation):
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
\end{example}

In our example, one can show that |dmap| is a correct derivative
for |map|. As a consequence, terms |map (f `oplus` df) (xs
`oplus` dxs)| and |map f xs `oplus` dmap f df xs dxs| are
interchangeable in all valid contexts, that is, contexts that
bind |df| and |dxs| to valid changes, respectively, for |f| and
|xs|.

 We sketch an informal proof directly on terms.
\begin{proof}[Proof sketch]
We must show that |dy = dmap f df xs dxs| is a change change from
initial output |y1 = map f xs| to updated output |y2 = map (f
`oplus` df) (xs `oplus` dxs)|, for valid inputs |df| and |dxs|.

We proceed by structural induction on |xs| and |dxs| (technically, on a
proof of validity of |dxs|). Since |dxs| is valid, those two
lists have to be of the same length. If |xs| and |dxs| are both
empty, |y1 = dy = y2 = Nil| so |dy| is a valid change as required.

For the inductive step, both lists are |Cons| nodes, so we need
to show that output change
\[|dy = dmap f df (Cons x xs) (Cons dx dxs)|\]
is a valid change from
\[|y1 = map f (Cons x xs)|\] to
\[|y2 = map (f `oplus` df) (Cons (x `oplus` dx) (xs `oplus`
dxs))|.\]

To restate validity we name heads and tails of |dy, y1, y2|.
If we write |dy = Cons dh dt|, |y1 = Cons h1 t1| and |y2 = Cons
h2 t2|, we need to show that |dh| is a change from |h1| to |h2|
and |dt| is a change from |t1| to |t2|.

Indeed, head change |dh = df x dx| is a valid change from
|h1 = f x| to |h2 = f (x `oplus` dx)|.
And tail change |dt = dmap f df xs dxs| is a valid change from |t1 = map f xs| to
|t2 = map (f `oplus` df) (xs `oplus` dxs)| by
induction. Hence |dy| is a valid change from |y1| to |y2|.
\end{proof}
Hopefully this proof is already convincing, but it relies on
undefined concepts. On a metalevel function, we could already
make this proof formal, but not so on terms yet. In this section,
we define the required concepts.

\subsection{Denotational equality for valid changes}
\label{sec:denot-equality-valid}
This example uses the notion of denotational equality for valid
changes. We now proceed to formalize it.
For reference, we recall denotational equality of terms, and then
introduce its restriction:
\iftoggle{full}{
\denotEqual*
}{
\begin{restatable*}[Denotational equality]{definition}{denotEqual}
  \label{def:denot-equality}
  We say that two terms |Gamma /- t1 : tau| and |Gamma /- t2:
  tau| are denotationally equal, and write |Gamma //= t1 `cong` t2
  : tau| (or sometimes |t1 `cong` t2|), if for all environments
  |rho : eval Gamma| we have that |eval t1 rho = eval t2 rho|.
\end{restatable*}
}

For open terms |t1, t2| that depend on changes,
denotational equality is too restrictive, since it
requires |t1| and |t2| to also be equal when the changes they
depend on are not valid.
By restricting denotational equality to valid environment
changes, and terms to depend on contexts, we obtain the following definition.
\begin{definition}[Denotational equality for valid changes]
  For any context |Gamma| and type |tau|,
  we say that two terms |Dt^Gamma /- t1 : tau| and |Dt^Gamma /-
  t2 : tau| are \emph{denotationally equal for valid changes} and
  write |Dt^Gamma //= t1 `congDt` t2 : tau| if, for all valid
  environment changes |fromto Gamma rho1 drho rho2| we have that
  |t1| and |t2| evaluate in environment |drho| to the same value,
  that is, |eval t1 drho = eval t2 drho|.
\end{definition}

\begin{example}
  Terms |f x `oplus` df x dx| and |f (x `oplus` dx)| are
denotationally equal for valid changes (for any types
|sigma, tau|):
|Dt^(f : sigma -> tau, x : sigma) //= f x `oplus` df x dx `congDt` f (x `oplus` dx) : tau|.
\end{example}
\begin{example}
One of our claims in \cref{ex:syn-changes-map} can now be written
as
\[|Dt^Gamma //= map (f `oplus` df) (xs `oplus` dxs) `congDt` map f
  xs `oplus` dmap f df xs dxs : List b|\]
for a suitable context |Gamma = f : List sigma -> List tau, xs : List
sigma, map : (sigma -> tau) -> List sigma -> List tau| (and for
any types |sigma, tau|).
\end{example}

Arguably, the need for a special equivalence is a defect in our
semantics of change programs; see \cref{sec:alt-change-validity}
for relevant discussion.

\subsection{Syntactic validity}
\label{sec:denot-syntactic-validity}
Next, we define \emph{syntactic validity}, that is,
when a change term |dt| is a (valid) change
from source |t1| to destination |t2|. Intuitively, |dt| is valid
from |t1| to |t2| if |dt|, |t1| and |t2|, evaluated all
against the same valid environment change |drho|, produce a
valid change, its source and destination. Formally:
\begin{definition}[Syntactic validity]
  \label{def:syntactic-validity}
  We say that term |Dt^Gamma /- dt : Dt^tau| is a (syntactic)
  change from |Dt^Gamma /- t1 : tau| to |Dt^Gamma /- t2 : tau|, and write
  |fromtosyn Gamma tau t1 dt t2|, if
  |forall (fromto Gamma rho1 drho rho2). fromto tau (eval t1 drho) (eval dt drho) (eval t2 drho)|.
\end{definition}
\begin{notation}
  We often simply say that |dt| is a change from |t1| to |t2|,
  leaving everything else implicit when not important.
\end{notation}

Using syntactic validity, we can show for instance that |dx| is a
change from |x| to |x `oplus` dx|, that |df x dx| is a change
from |f x| to |(f `oplus` df) (x `oplus` dx)|; both examples
follow from a general statement about |derive|
(\cref{thm:derive-correct-syntactic}). Our earlier informal proof
of the correctness of |dmap| (\cref{ex:syn-changes-map}) can also
be justified in terms of syntactic validity.

Just like (semantic) |`oplus`| agrees with validity, term-level
(or syntactic) |`oplus`| agrees with syntactic validity, up to
denotational equality for valid changes.
\begin{lemma}[Term-level |`oplus`| agrees with syntactic validity]
If |dt| is a change from |t1| to |t2| (|fromtosyn Gamma tau t1 dt
t2|) then |t1 `oplus` dt| and |t2| are denotationally equal for
valid changes (|Dt^Gamma //= t1 `oplus` dt `congDt` t2 : tau|).
\end{lemma}
\begin{proof}
  Follows because term-level |`oplus`| agrees with semantic |`oplus`|
  (\cref{lem:chops-coherent}) and |`oplus`| agrees with validity.
  In more detail: fix an arbitrary valid environment change
  |fromto Gamma rho1 drho rho2|.
  First, we have |fromto tau (eval t1 drho) (eval dt drho) (eval t2
  drho)| because of syntactic validity.
  Then we conclude with this calculation:
\begin{equational}
\begin{code}
   eval (t1 `oplus` dt) drho
=  {- term-level |`oplus`| agrees with |`oplus`| (\cref{lem:chops-coherent}) -}
   eval t1 drho `oplus` eval dt drho
=  {- |`oplus`| agrees with validity -}
   eval t2 drho
\end{code}
\end{equational}
\end{proof}

Beware that the definition of |fromtosyn Gamma tau t1 dt t2|
evaluates all terms against change environment |drho|, containing
separately base values and changes. In contrast, if we use
validity in the change structure for |eval Gamma -> eval tau|, we
evaluate different terms against different environments. That is
why we have that |dx| is a change from |x| to |x `oplus` dx|
(where |x `oplus` dx| is evaluated in environment |drho|),
while |eval dx| is a valid change from |eval x| to |eval x|
(where the destination |eval x| gets applied to environment |rho2|).

\paragraph{Is syntactic validity trivial?}
Without needing syntactic validity, based on earlier chapters one
can show that
|dv| is a valid change from |v| to |v `oplus` dv|, or that |df v
dv| is a valid change from |f v| to |(f `oplus` df) (v `oplus`
dv)|, or further examples.
But that's all about values. In this section we are just translating these
notions to the level of terms, and formalize them.

Our semantics is arguably (intuitively) a trivial one, similar to
a metainterpreter interpreting object-language functions in terms of
metalanguage functions: our semantics simply embeds an
object-level $\lambda$-calculus into a meta-level and more
expressive $\lambda$-calculus, mapping for instance |\f x -> f x|
(an AST) into |\f v -> f v| (syntax for a metalevel function).
Hence, proofs in this section about syntactic validity deal
mostly with this translation. We don't expect the proofs to give
special insights, and we expect most development would keep such
issues informal (which is certainly reasonable).

Nevertheless, we write out the statements to help readers refer
to them, and write out (mostly) full proofs to help ourselves
(and readers) verify them. Proofs are mostly standard but
with a few twists, since we must often consider and relate
\emph{three} computations: the computation on initial values and
the ones on the change and on updated values.

We're also paying a proof debt. Had we used substitution and
small step semantics, we'd have directly simple statements on terms,
instead of trickier ones involving terms and environments. We
produce those statements now.
% \emph{except} that
% we must always require and propagate validity of changes, or
% substitute variables producing initial values |xi| with terms
% producing updated values
% updated values |xi `oplus` dxi|.

\subsubsection{Differentiation and syntactic validity}
We can also show that |derive t| produces a syntactically valid
change from |t|, but we need to specify its destination.
In general, |derive t| is not a change from |t| to |t|. The
destination must evaluate to the updated value of |t|; to produce
a term that evaluates to the right value, we use substitution. If
the only free variable in |t| is |x|, then |derive t| is a
syntactic change from |t| to |t[x := x `oplus` dx]|.
To repeat the same for all variables in context |Gamma|, we use
the following notation.
\begin{notation}
We write |t[Gamma := Gamma `oplus` Dt^Gamma]| to mean |t[x1 := x1
`oplus` dx1, x2 := x2 `oplus` dx2, ..., xn := xn `oplus` dxn]|.
\end{notation}
\begin{theorem}[|derive| is correct, syntactically]
  \label{thm:derive-correct-syntactic}
  For any well-typed term |Gamma /- t : tau|, term |derive t| is
  a syntactic change from |t| to |t[Gamma := Gamma `oplus` Dt^Gamma]|.
\end{theorem}
We present the following straightforward (if tedious) proof (formal but not mechanized).
\begin{proof}
  Let |t2 = t[Gamma := Gamma `oplus` Dt^Gamma]|.
  Take any |fromto Gamma rho1 drho rho2|. We must show that
  |fromto tau (eval t drho) (eval (derive t) drho) (eval t2 drho)|.

  Because |drho| extend |rho1| and |t| only needs entries
  in |rho1|, we can show that |eval t drho = eval t rho1|, hence
  our thesis becomes |fromto tau (eval t rho1) (eval (derive t)
  drho) (eval t2 drho)|.

  Because |derive| is correct (\cref{thm:derive-correct}) we know
  that |fromto tau (eval t rho1) (eval (derive t) drho) (eval t
  rho2)|; that's almost our thesis, so we must only show that
  |eval t2 drho = eval t rho2|.
  Since |`oplus`| agrees with
  validity and |drho| is valid, we have that |rho2 = rho1 `oplus`
  drho|, so our thesis is now the following equation, which we
  leave to \cref{thm:derive-correct-syntactic-env-lemma}:
  \[|eval t[Gamma := Gamma `oplus` Dt^Gamma] drho = eval t (rho1 `oplus` drho)|.\]
\end{proof}

Here's the technical lemma to complete the proof.
\begin{lemma}
  \label{thm:derive-correct-syntactic-env-lemma}
  For any |Gamma /- t : tau|, and |fromto Gamma rho1 drho rho2|
  we have
  \[|eval t[Gamma := Gamma `oplus` Dt^Gamma] drho = eval t (rho1 `oplus` drho)|.\]
\end{lemma}
\begin{proof}
  This follows from the structure of valid environment changes,
  because term-level |`oplus`| (used on the left-hand side) agrees with
  value-level |`oplus`| (used on the right-hand side) by
  \cref{lem:chops-coherent}, and because of the substitution lemma.

  More formally, we can show the thesis by induction over environments:
  for empty environments, the equations reduces to |eval t
  emptyRho = eval t emptyRho|. For the case of |Gamma, x :
  sigma| (where $x \not\in \Gamma$), the thesis can be rewritten as
  \[
    |eval
    ((t[Gamma := Gamma `oplus` Dt^Gamma])[x := x `oplus` dx])
    (drho, x = v1, dx = dv) =
    eval t (rho1 `oplus` drho, x = v1 `oplus` dv)|.
  \]
  We prove it via the following calculation.
\begin{equational}
  \begin{code}
   eval ((t[Gamma := Gamma `oplus` Dt^Gamma])[x := x `oplus` dx]) (drho, x = v1, dx = dv)
=  {- Substitution lemma on |x|. -}
   eval ((t[Gamma := Gamma `oplus` Dt^Gamma])) (drho, x = (eval (x `oplus` dx) (drho, x = v1, dx = dv)), dx = dv)
=  {- Term-level |`oplus`| agrees with |`oplus`|
      (\cref{lem:chops-coherent}). -}
   {- Then simplify |eval x| and |eval dx|. -}
   eval ((t[Gamma := Gamma `oplus` Dt^Gamma])) (drho, x = v1 `oplus` dv, dx = dv)
=  {- |t[Gamma := Gamma `oplus` Dt^Gamma]| does not mention |dx|. -}
   {- So we can modify the environment entry for |dx|. -}
   {- This makes the environment into a valid environment change. -}
   eval ((t[Gamma := Gamma `oplus` Dt^Gamma])) (drho, x = v1 `oplus` dv, dx = nil(v1 `oplus` dv))
=  {- By applying the induction hypothesis and simplifying |nilc| away. -}
   eval t (rho1 `oplus` drho, x = v1 `oplus` dv)
  \end{code}
\end{equational}
\end{proof}

% \paragraph{Discussion}
% We defined earlier a change structure on the domain of the
% \emph{denotations} of terms, that is |eval Gamma -> eval tau|.
% We could use this as a change structure on terms, but the
% resulting change structure is far less useful.
% In particular, if |\rho drho -> eval dt drho| is a change from |eval t1|
% to |eval t2|, it does not follow that |t1 `oplus` dt `cong`
% t2|.\pg{never true, define another cong relation?}
% Indeed, in the latter statement, all terms are evaluated in the
% same environment; instead, when we say that |\rho drho -> eval dt
% drho| is a change from |eval t1| to |eval t2|, we in fact
% evaluate |t2| according to an updated environment.
% So we can satisfy |t1 `oplus` dt `cong` t2| with |t1 = x|, |dt =
% dx| and |t2 = x `oplus` dx|. Yet, |\rho drho -> eval dx drho| is
% a change from |eval x| to |eval x|, not to |eval (x `oplus` dx)|.

% %but rather that |eval t1 rho `oplus` eval dt (nil rho) = eval t2 rho|
% Let us see why in more detail by recalling earlier notions.
% When we state correctness of differentiation using the change
% structure on |eval Gamma -> eval tau|, we say that |evalInc t =
% \rho drho -> eval (derive t) drho| is a change from |eval t| to
% |eval t|. Recall that, according to validity as defined by this
% change structure, we say that |\rho1 drho -> eval dt drho| is a
% valid change from |eval t1| to |eval t2| if for all valid
% environment changes |fromto Gamma rho1 drho rho2| we have that
% |eval dt drho| is a valid change from |eval t1 rho1| and |eval t2
% rho2|. Hence we have
% \begin{equation}
%   \label{eq:sem-validity-oplus-eval}
% |forall (fromto Gamma rho1 drho rho2). eval t1 rho1 `oplus` eval dt drho = eval t2 rho2|.
% \end{equation}
% For instance, applying correctness of differentiation to term |t
% = x|, we have that |eval x rho1 `oplus` eval dx drho = eval x
% rho2|.

% However, we seek to define validity on terms in a different way.
% We want to say when term |dt| is a valid change from term |t1| to
% term |t2|, so that as a corollary |t1 `oplus` dt `cong` t2| and
% |t1 `oplus` dt| and |t2| are interchangeable in all \emph{valid
%   contexts}, that is, context where all changes are valid.
% \pg{Uh! Not all contexts! Only contexts with valid environments!}
% \pg{where's the statement/lemma/theorem?}
% That is,
% \begin{equation}
% |forall (fromto Gamma rho1 drho rho2). eval (t1 `oplus` dt) drho = eval t2 drho|.
% \end{equation}
% Because evaluation commutes with |`oplus`|
% (\cref{lem:chops-coherent}), and because a valid environment
% change |drho| extends its source |rho1|, this equation is
% equivalent to
% \begin{equation}
%   \label{eq:syn-equiv-envs}
% |forall (fromto Gamma rho1 drho rho2). eval t1 rho1 `oplus` eval dt drho = eval t2 rho1|.
% \end{equation}
% This statement evaluates |t1| and |t2| in \emph{the same}
% environment |rho1|, while instead
% \cref{eq:sem-validity-oplus-eval} evaluates |t2| against |rho2|.
% Hence, we incorporate \cref{eq:syn-equiv-envs} into a new definition.
% \pg{Continue.}

% Earlier equations evaluate |t2| against |rho2|.
% \pg{revise}
% Consider the equations that must hold for all |fromto Gamma rho1
% drho rho2|
% for validity in the change structure for |eval Gamma -> eval tau|\pg{cref}:
% |eval t1 rho1 `oplus` eval dt drho = eval t2 rho2|
% % \pg{cite this from earlier!}
% and
% for correctness of differentiation (\cref{thm:derive-correct-oplus}):
% |eval t rho1 `oplus` eval (derive t) drho = eval t rho2|.
% \pg{any other ones?}
% Unlike equations we have seen before, in this equation all terms
% are evaluated with respect to the same environment.

% \pg{Earlier attempt...}
% \pg{Bad transition.}
% We might be tempted to say,
% then, that |derive t| is a change from |t| to |t|. But such a
% notion does not imply that |t `oplus` derive t = t|.
% Indeed, if we try to show \cref{eq:syn-equiv-envs} from
% |fromtosem Gamma tau (eval t) (evalInc t) (eval t)|, we obtain a
% different equation, namely
% \begin{equation}
% |forall (fromto Gamma rho1 drho rho2). eval t1 rho1 `oplus` eval dt drho = eval t2 rho2|.
% \end{equation}
% \pg{cite this from earlier!}


% or to term |t1 `oplus` dt|, that |dx| is a
% change from |x| to |x `oplus` dx|, and so on.

% But currently we lack the language to do so. We can use the
% change structure on |eval Gamma -> eval tau|, and write |fromto
% () t1 dt t2|.\pg{How to write Gamma, tau there?}
% But in such a statement means that for all

% We write substitution as |t [x := s]|, and parallel substitution
% as 
% |t [Gamma := Gamma `oplus` Dt^Gamma]|
% \begin{theorem}[Syntactic correctness for |derive(param)|]
%   |fromtosyn Gamma tau t (derive t) (t [Gamma := Gamma `oplus` Dt^Gamma])|.
% \end{theorem}
% \begin{lemma}[Substitution lemma]
%   Take terms |Gamma /- s : sigma| and |Gamma , x : sigma /- t :
%   tau|. Then for all environments |rho : eval(Gamma)|
%   substitution commutes with evaluation:
%   |eval (t [x := s]) rho = eval t (rho, x = eval(s) rho)|.
% \end{lemma}

% This 
% We will discuss changes on terms directly, without referencing
% explicitly a denotational semantics.
% Up to now, we have only discussed what 

% We can also prove a different corollary.
% \begin{corollary}
% If |Gamma /- t : tau| then |eval t `oplus` evalInc t = eval t|. That is,
% |eval t rho `oplus` evalInc t rho (nil rho) = eval t rho|.
% \end{corollary}
% \begin{proof}
%   The proof is similar to the one of \cref{thm:derive-correct-oplus}. 
%   Again, differentiation is correct (\cref{thm:derive-correct}), and |`oplus`|
%   agrees with validity. But this time we write correctness of differentiation as
%   |fromto (Gamma -> tau) (eval t) (evalInc t) (eval t)|, so that we obtain
%   |eval t `oplus` evalInc t = eval t|. Recalling that |(f `oplus` df) v = f v `oplus` f
%   v (nil v)|, that is equivalent to 
%   |eval t rho `oplus` evalInc t rho (nil rho) = eval t rho|.
% \end{proof}

% \begin{remark}
%   We'll later define a polymorphic term |/- `oplus` : t -> Dt^t -> t| which
% represents the semantic |`oplus`| inside the calculus, that is, such that
% |eval(`oplus`) emptyRho = `oplus`|. One might try to conclude that 
% \end{remark}
% Our \cref{thm:derive-correct-oplus} on |derive(t)| can also be written through
% the equation
% \begin{equation}
%   \label{eq:derive-correct-oplus-higher-order}
% |eval t `oplus` evalInc t = eval t|.
% \end{equation}
% \pg{move into theorem.}
% But we need to be
% careful. We later define |`oplus`| also as a family of terms (one for each type),
% but it does not follow in general from
% \cref{eq:derive-correct-oplus-higher-order} that |t `oplus` derive t `cong` t|.

\section{Change equivalence}
\label{sec:change-equivalence}
To optimize programs manipulate changes, we often want to replace a
change-producing term by another one, while preserving the overall program
meaning. Hence, we define an equivalence on valid changes that is preserved by
change operations, that is (in spirit) a \emph{congruence}. We call this relation
\emph{(change) equivalence}, and refrain from using other
equivalences on changes.

Earlier (say, in \cref{ssec:pointwise-changes}) we have sometimes required that
changes be equal, but that's often too restrictive.

Change equivalence is defined in terms of validity, to ensure that
validity-preserving operations preserve change equivalence: If two changes |dv1|
and |dv2| are equivalent, one can be substituted for the other in a
validity-preserving context. We can define this once for all change
structures, hence in particular for values and environments.

\begin{definition}[Change equivalence]
  Given a change structure |chs(V)|,
  changes |dva, dvb : Dt^V| are equivalent relative to source
  |v1 : V| (written |fromto V v1 (dva `doe` dvb) v2|)
  if and only if there exists |v2| such that both |dva| and
  |dvb| are valid from |v1| to |v2| (that is |fromto V v1 dva
  v2|, |fromto V v1 dvb v2|).
\end{definition}
\begin{notation}
When not ambiguous we often abbreviate |fromto V v1 (dva `doe`
dvb) v2| as |dva (doeIdx(v1)) dvb| or |dva `doe` dvb|.

Two changes are often equivalent relative to a source but not
others. Hence |dva `doe` dvb| is always an abbreviation for
change equivalence for a specific source.
\end{notation}

\begin{example}
For instance, we later use a change structure for integers using
both replacement changes and differences (\cref{ex:replacement}).
In this structure, change |0| is nil for all numbers, while
change |!5| (``bang 5'') replaces any number with 5. Hence,
changes |0| and |!5| are equivalent only relative to source 5,
and we write |0 (doeIdx 5) !5|.
\end{example}

By applying definitions, one can verify that change equivalence
relative to a source |v| is a symmetric and transitive relation on |Dt^V|.
However, it is not an equivalence relation on |Dt^V|, because it is only
reflexive on changes valid for source |v|. Using the set-theoretic concept of
subset we can then state the following lemma (whose proof we omit as it is
brief):
\begin{lemma}[|`doe`| is an equivalence on valid changes]
  \label{doe:equiv-valid}
  For each set |V| and source |v `elem` V|, change equivalence
  relative to source |v| is an equivalence relation over the set
  of changes $\{|dv `elem` Dt^V `such` dv| \text{ is valid with source } |v|\}$.
\end{lemma}
We elaborate on this peculiar sort of equivalence in \cref{sec:doe-per}.

\subsection{Preserving change equivalence}
Change equivalence relative to a source |v| is respected, in an appropriate
sense, by all validity-preserving expression contexts that accept changes with
source |v|.
To explain what this means we study an example lemma: we show that because valid
function changes preserve validity, they also respect change equivalence.
At first, we use ``(expression) context'' informally to refer to
expression contexts in the metalanguage. Later, we'll extend our
discussion to actual expression contexts in the object language.

\begin{lemma}[Valid function changes respect change equivalence]
  \label{lem:ch-respect-doe}
Any valid function change
\[|fromto (A -> B) f1 df f2|\]
respects change equivalence: if |fromto A v1 (dva `doe` dvb) v2| then
|fromto B (f1 v1) (df v1 dva `doe` df v1 dvb) (f2 v2)|.
We also say that (expression) \emph{context} |df v1 param|
respects change equivalence.
\end{lemma}
\begin{proof}
The thesis means that |fromto B (f1 v1) (df v1 dva) (f2 v2)| and |fromto B (f1
v1) (df v1 dvb) (f2 v2)|. Both equivalences follow in one step from validity of
|df|, |dva| and |dvb|.
\end{proof}

This lemma holds because the source and destination of |df v1 dv|
don't depend on |dv|, only on its source and destination. Source
and destination are shared by equivalent changes. Hence,
validity-preserving functions map equivalent changes to
equivalent changes.

In general, all operations that preserve validity also respect
\emph{change equivalence}, because for all those operations, the
source and destination of any output changes, and the resulting
value, only depend on source and destination of input changes.

However, \cref{lem:ch-respect-doe} does \emph{not} mean that |df v1 dva = df v1 dvb|,
because there can be multiple changes with the same source and destination.
For instance, say that |dva| is a list change that removes an element and readds it,
and |dvb| is a list change that describes no modification. They are both nil
changes, but a function change might handle them differently.

Moreover, we only proved that context |df v1 param| respects change equivalence
relative to
source |v1|. If value |v3| differs from |v1|, |df v3 dva| and |df v3 dvb| need
not be equivalent. Hence, we say that context |df v1| \emph{accepts changes}
with source |v1|. More in general, a context accepts changes with source |v1|
if it preserves validity for changes with source |v1|; we can say informally
that all such contexts also respect change equivalence.

Another example: context |v1 `oplus` param| also accepts changes
with source |v1|. Since this context produces a base value and not a change, it
maps equivalent changes to equal results:
\begin{lemma}[|`oplus`| respects change equivalence]
  \label{lem:oplus-respect-doe}
  If |fromto V v1 (dva `doe` dvb) v2| then |v1 `oplus` param| respects the
  equivalence between |dva| and |dvb|, that is, |v1 `oplus` dva = v1 `oplus` dvb|.
\end{lemma}
\begin{proof}
  |v1 `oplus` dva = v2 = v1 `oplus` dvb|.
\end{proof}

There are more contexts that preserve equivalence. As discussed, function
changes preserve contexts, and |derive| produces functions changes, so |derive
t| preserves equivalence on its environment, and on any of its free variables.

\begin{lemma}[|derive(param)| preserves change equivalence]
  \label{lem:eval-derive-preserve-doe}
For any term |Gamma /- t : tau|, |derive(t)| preserves change
equivalence of environments:
for all |fromto Gamma rho1 (drhoa `doe` drhob) rho2| we have
|fromto (Gamma -> tau) (eval t rho1) (eval (derive t) drhoa `doe` eval
(derive t) drhob) (eval t rho2)|.
% that is |fromto (Gamma
% -> tau) (eval t) (eval (derive t) `doe` eval (derive t)) (eval
% t)|, that is,
\end{lemma}
\begin{proof}
  To verify this, just apply correctness of differentiation to
  both changes |drhoa| and |drhob|.
\end{proof}

To show more formally in what sense change equivalence is a
congruence, we first lift it to terms, similarly to syntactic
change validity in \cref{sec:denot-syntactic-validity}.

\begin{definition}[Syntactic change equivalence]
Two change terms |Dt^Gamma /- dta : Dt^tau| and |Dt^Gamma /- dtb :
Dt^tau| are change equivalent, relative to source |Gamma /- t :
tau|, if for all valid environment changes
|fromto Gamma rho1 drho rho2| we have that
\[|from tau (eval t rho1) (eval dta drho `doe` eval dtb drho)|.\]
We write then
|fromsyn Gamma tau t (dta `doe` dtb)|
or |dta (doeIdx t) dtb|, or simply |dta `doe` dtb|.
%|fromto tau v1 (dv1 `doe` dv2) v2|,
\end{definition}
Saying that |dta| and |dtb| are equivalent relative to |t| does
not specify the destination of |dta| and |dtb|, only their
source. The only reason is to simplify the statement and proof of
\cref{thm:derive-preserve-doe}.

\begin{notation}[One-sided validity]
  We write |from V v1 dv| to mean there exists |v2| such that
  |fromto V v1 dv v2|. We will reuse existing conventions and
  write |from tau v1 dv| instead of |from (eval tau) v1 dv|
  and |from Gamma rho1 drho| instead of |from (eval Gamma) rho1 drho|.
\end{notation}
% If there exists a destination and we want to specify it,
% we can use the following stronger definition:
% \begin{definition}[Syntactic change equivalence, two sided]
% Two change terms |Dt^Gamma /- dta : Dt^tau| and |Dt^Gamma /- dtb :
% Dt^tau| are change equivalent, from source |Gamma /- t1 :
% tau| to destination |Gamma /- t2 : tau|, if for all |fromto Gamma rho1 drho rho2| we have that
% \[|fromto V (eval t1 rho1) (eval dta drho `doe` eval dtb drho)
%   (eval t2 rho2)|\]
% %\[|eval dta drho|\, |(doeIdx(eval t rho1))| |eval dtb drho|.\]
% We write then \[|fromtosyn Gamma tau t1 (dta `doe` dtb) t2|.\]
% %|fromto tau v1 (dv1 `doe` dv2) v2|,
% \end{definition}
% \begin{fact}
%   Two-sided change equivalence implies source-only change
%   equivalence: if
% \[|fromtosyn Gamma tau t1 (dta `doe` dtb) t2|\] then
% |dta (doeIdx t1) dtb|.
% \end{fact}

% % Unlike in other similar definition, when changes |dta| and |dtb| are equivalent
% % relative to |t| and given equivalent contexts |fromto Gamma rho1 drho rho2|,
% % they need
% % The equivalence of |dta| and |dtb| relative to |t| does not
% % require that the destination is again |t|.
% \pg{Use \cref{def:syntactic-validity} to also state the destination.}
% \pg{Introduce this earlier}

If two change terms are change equivalent with respect to the
right source, we can replace one for the other in an expression
context to optimize a program, as long as the expression context
is validity-preserving and accepts the change.

In particular, substituting into |derive t| preserves syntactic
change equivalence, according to the following theorem (for which
we have only a pen-and-paper formal proof).
\begin{theorem}[|derive| preserves syntactic change equivalence]
  \label{thm:derive-preserve-doe}
  For any equivalent changes |fromsyn Gamma
  sigma (dsa `doe` dsb) s|, and for any term |t| typed as
  |Gamma , x : sigma /- t : tau|,
  we can produce equivalent results by substituting into |derive
  t| either |s| and |dsa| or |s| and |dsb|:
\[|fromsyn Gamma tau (t [x := s]) ((derive t)[x := s, dx := dsa] `doe` (derive t)[x := s, dx := dsb])|.\]
\end{theorem}
\begin{proof}
  Assume |fromto Gamma rho1 drho rho2|.

  The thesis holds because |derive| preserves change equivalence
  \cref{lem:eval-derive-preserve-doe}.
  A formal proof follows through routine (and entirely tedious)
  manipulations of bindings. In essence, we can extend |drho| to
  equivalent environment changes for context |Gamma , x : sigma|
  with the values of |dsa| and |dsb|. The tedious calculations
  follow.

  % A corollary of \cref{lem:eval-derive-preserve-doe} and of a substitution lemma
  % relating substitution and denotational semantics: |eval (t) (x = eval s rho,
  % rho) = eval(t [x := s]) rho|.

  Because |dsa| and |dsb| are change-equivalent we have
  % By definition of |dsa (doeIdx(s)) dsb| we have that
  % |eval dsa drho (doeIdx(eval s rho1)) (eval dsb drho)|.
  %
  % Because |`oplus`| respects validity also syntactically \pg{?}
  % we can show that |dsa, dsb| have destination |s `oplus` dsa|, that is
  \[|from sigma (eval s rho1) (eval dsa drho `doe` eval dsb drho)|.\]
  Moreover, |eval s rho1 = eval s drho| because |drho| extends
  |rho1|. We'll use this equality without explicit mention.
  % \[|fromto sigma (eval s rho1) (eval dsa drho `doe` eval dsb drho) (eval (s `oplus` ds) rho1)|.\]
  % \[| (eval dsa drho) (doeIdx(eval s rho1)) (eval dsb drho) |.\]

  Hence, we can construct change-equivalent environments for
  evaluating |derive t|, by combining |drho| and the values of
  respectively |dsa| and |dsb|:
  \begin{multline}
  |from ((Gamma, x : sigma))
  ((rho1, x = eval s rho1))
  ((drho, x = eval s drho, dx = eval dsa drho)
   `doe` ^^^
   (drho, x = eval s drho, dx = eval dsb drho) ^^^) |.
  \end{multline}
  This environment change equivalence is respected by |derive t|, hence:
  \begin{multline}
    \label{eq:derive-preserve-doe-1}
  |from (Gamma -> tau)
    (eval t (rho1, x = eval s rho1))
    (eval (derive t) (drho, x = eval s drho, dx = eval dsa drho)
     `doe` ^^^
     eval (derive t) (drho, x = eval s drho, dx = eval dsb drho)^^^) |.
  \end{multline}
  We want to deduce the thesis by applying to this statement the substitution
  lemma for denotational semantics:
  |eval t (rho, x = eval s rho) = eval(t [x := s]) rho|.

  To apply the substitution lemma to the substitution of |dx|, we
  must adjust \cref{eq:derive-preserve-doe-1} using soundness of
  weakening. We get:
  \begin{multline}
    \label{eq:derive-preserve-doe-2}
  |from (Gamma -> tau)
    (eval t (rho1, x = eval s rho1))
    (eval (derive t) (drho, x = eval s drho, dx = eval dsa (drho, x = eval s drho))
     `doe` ^^^
     eval (derive t) (drho, x = eval s drho, dx = eval dsb (drho, x = eval s drho))^^^) |.
  \end{multline}

  This equation can now be rewritten (by applying the
  substitution lemma to the substitutions of |dx| and |x|) to the following one:

  \begin{multline}
    \label{eq:derive-preserve-doe-3}
  |from (Gamma -> tau)
    (eval (t [x := s]) rho1)
    (eval ((derive t)[dx := dsa][x := s]) drho
     `doe` ^^^
     eval ((derive t)[dx := dsb][x := s]) drho^^^) |.
  \end{multline}

  Since |x| is not in scope in |s, dsa, dsb|, we can permute
  substitutions to conclude that:
\[|fromsyn Gamma tau (t[x:=s])
  ((derive t)[x := s, dx := dsa] `doe`
   (derive t)[x := s, dx := dsb])|\]
as required.
\end{proof}
In this theorem, if |x| appears once in |t|, then |dx| appears once in |derive
t| (this follows by induction on |t|), hence |(derive t)[x := s, dx := param]|
produces a one-hole expression context.

\paragraph{Further validity-preserving contexts}
There are further operations that preserve validity. To represent terms with
``holes'' where other terms can be inserted, we can define \emph{one-level
contexts} |F|, and contexts |E|, as is commonly done:
\begin{code}
  F ::= [] t dt | ds t [] | \x dx -> [] | t `oplus` [] | dt1 `ocompose` [] | [] `ocompose` dt2
  E ::= [] | F[E]
\end{code}
If |fromto tau t1 (dt1 `doe` dt2) t2| and our context |E|
accepts changes from |t1|, then |F[dt1]| and |F[dt2]|
are change equivalent. It is easy to prove such a lemma for each possible shape
of one-level context |F|, both on values (like
\cref{lem:ch-respect-doe,lem:oplus-respect-doe}) and on terms. We have been
unable to state a more general theorem because it's not clear how to formalize
the notion of a context accepting a change in general: the syntax of a context
does not always hint at the validity proofs embedded.

\pg{explain this type system elsewhere}
\citet{CaiEtAl2014ILC} solve this problem for metalevel contexts by typing them
with dependent types. However, it is not clear such a typesystem can be
expressive enough. Consider a change |dv1| from |v1| to |v1 `oplus` dv1|, a
value |v2| which is known to be (propositionally) equal to |v1 `oplus` dv1|, and
a change |dv2| from |v2| to |v3|. Then, term |dv1 `ocompose` dv2| is not type
correct (for instance in Agda): the typechecker will complain that |dv1| has
destination |v1 `oplus` dv1| while |dv2| has source |v2|. When working in Agda,
to solve this problem we can explicitly coerce terms through propositional
equalities, and can use Agda to prove such equalities in the first place.
Formalizing an object language including such facilities is not trivial.

\subsection{Sketching an alternative syntax}
If we exclude composition, we can sketch an alternative syntax
which helps construct a congruence on changes.
The idea is to manipulate, instead of changes alone, pairs of
sources |v `elem` V| and valid changes $\{| dv `such` from V v dv |\}$.
\pg{Move notation for one-sided validity.}
%{
%format src = "\mathbf{src}"
%format dst = "\mathbf{dst}"
\begin{code}
  t ::= src dt | dst dt | x | t t | \x -> t
  dt ::= dt dt | src dt | \dx -> dt | dx
\end{code}
%}
Adapting differentiation to this syntax is easy:
\begin{code}
  derive x = dx
  derive (s t) = derive s (derive t)
  derive(\x -> t) = derive(\dx -> dt)
\end{code}
Derivatives of
primitives only need to use |dst dt| instead of |t `oplus` dt|
and |src dt| instead of |t| whenever |dt| is a change for |t|.

With this syntax, we can define change expression contexts, which
can be filled in by change expressions:

\begin{code}
  E ::= src dE | dst dE | E t | t E | \x -> E
  dE ::= dt dE | dE dt | \dx -> dE | []
\end{code}

We conjecture change equivalence is a congruence with respect to
contexts |dE|, and that contexts |E| map change-equivalent
changes to results that are denotationally equivalent for valid
changes. We leave a proof to future work, but we expect it to be
straightforward. It also appears straightforward to provide an
isomorphism between this syntax and the standard one.

However, extending such contexts with composition does not appear
trivial: contexts such as |dt `ocompose` dE| or |dE `ocompose`
dt| only respect validity when the changes sources and
destinations align correctly.

We make no further use of this alternative syntax in this work.

\subsection{Change equivalence is a PER}
\label{sec:doe-per}
Readers with relevant experience will recognize that change
equivalence is a partial equivalence relation (PER)~\citep[Ch.
5]{Mitchell1996foundations}. It is standard to use PERs to
identify valid elements in a
model~\citep{Harper1992constructing}. In this section, we state
the connection, showing that change equivalence is not an ad-hoc
construction, so that mathematical constructions using PERs can
be adapted to use change equivalence.

We recall the definition of a PER:
\begin{definition}[Partial equivalence relation (PER)]
  A relation $R \subseteq S \times S$ is a partial equivalence
  relation if it is symmetric (if $a R b$ then $b R a$) and
  transitive (if $a R b$ and $b R c$ then $a R c$).
\end{definition}
Elements related to another are also related to themselves: If
$aRb$ then $aRa$ (by transitivity: $aRb$, $bRa$, hence $aRa$). So
a PER on |S| identifies a subset of valid elements of |S|. Since
PERs are equivalence relations on that subset, they also induce a
(partial) partition of elements of |S| into equivalence classes
of change-equivalent elements.

\begin{lemma}[|`doe`| is a PER]
  Change equivalence relative to a source |a : A| is a PER on set |Dt^A|.
\end{lemma}
\begin{proof}
A restatement of \cref{doe:equiv-valid}.
\end{proof}

Typically, one studies \emph{logical PERs}, which are logical
relations and PERs at the same time~\citep[Ch. 8]{Mitchell1996foundations}.
In particular, with a logical PER two functions are related if they map related
inputs to related outputs. This helps showing that a PERs is a congruence.
Luckily, our PER is equivalent to such a definition.

\begin{lemma}[Alternative definition for |`doe`|]
Change equivalence is equivalent to the following logical relation:
\begin{code}
  fromto iota v1 (dva `doe` dvb) v2            `eqdef`
    fromto iota v1 dva v2 `wand` fromto iota v1 dva v2
  fromto (sigma -> tau) f1 (dfa `doe` dfb) f2  `eqdef`
    forall (fromto sigma v1 (dva `doe` dvb) v2).
    fromto tau (f1 v1) (dfa v1 dva `doe` dfb v2 dvb) (f2 v2)
\end{code}
\end{lemma}
\begin{proof}
  By induction on types.
\end{proof}

% A limitation of our PERs is that, compared to more typical
% examples, our PERs are constructed over an existing type system
% in the meta-theory (a semantics for simply-typed
% $\lambda$-calculus, together with separate domains for each
% type), rather than a partial combinatory algebra containing codes
% for all values.
% Since ILC can be proved correct also for untyped languages
% (\cref{sec:silr-untyped-proof}), it's unce

\section{Chapter conclusion}
\label{sec:term-reasoning-concl}
In this chapter, we have put on a more solid foundation
forms of reasoning about changes on terms, and defined an
appropriate equivalence on changes.

\chapter{Stuff}
In this chapter, we relate our formalization of changes with the one by
\citet{CaiEtAl2014ILC} in \cref{sec:alt-change-validity}.
\pg{We have proved equivalence with the one-sided definition of validity.}
\subsection{Alternative definitions of change validity}
\label{sec:alt-change-validity}

\newcommand{\ilcA}{ILC'14}
\newcommand{\ilcB}{ILC'17}

In this section we compare the formalization of ILC in this thesis (\ilcB)
with the one we and others used in our \emph{old-style}
formalization, that is, our first formalization of change
theory~\citep{CaiEtAl2014ILC} (\ilcA).
We discuss both formalizations using our current notation and terminology, except for concepts
that are not present here.
Both formalizations model function changes semantically, but the two models we
present are different. Overall, \ilcB{} uses simpler machinery and seems easier
to extend to more general base languages. Instead, \ilcA{} studies additional
entities, which however are in some ways better behaved.

In \ilcB{} function changes whose input and output domains contain
\emph{invalid} changes; but function changes must map valid changes to valid
changes. As shown, |eval(derive t)| maps valid changes to valid changes.

Instead, \ilcA{} does not define validity on change set |Dt^A|. For each value
|a : A| \ilcA{} defines a \emph{based} change set |Dt^a|; elements of |Dt^a|
\emph{correspond} to changes that are valid with respect to |a|.
Changes |df : Dt^f| for a function |f : A -> B| have a dependent type |df : (a :
A) -> Dt^a -> Dt^(f a)|, hence their input and output domains are restricted to
\emph{only} contain ``valid'' changes. Based change sets are in some ways better
behaved. However, |eval(derive t)| does not belong to any based change set, because
it has the ``wrong'' domain, even though |eval(derive t)|, when applied to
``valid changes'', has in some sense the ``correct behavior''. More precisely,
\ilcA{} introduces an incremental semantics |evalInc t| (different from the one in \ilcB{}), proves it
has a ``correct behavior'', and shows that |eval(derive t)| has a behavior that ``matches''
|evalInc t|. In turn, to make this precise, \ilcA{} defines formally when when a
based change and a change have ``matching behaviors'' through a logical
relation called \emph{erasure}: function change |df : (a : A) -> Dt^a -> Dt^(f
a)| (with source |f : A -> B)| erases to erased change |df' : A -> Dt^A -> Dt^B|
(written |erase f df df'|)
if, given any change |da : Dt^a| with source |a| that erases to |da' : Dt^A|,
output change |df a da : Dt^(f a)| erases to |df' a da' : Dt^B|.
For base types, erasure simply connects corresponding |da' : Dt^a| with |da :
Dt^A| in a manner dependent from the base type (often, just throwing away any
embedded proofs of validity).
This relation is called erasure because it goes from dependently-typed functions
to non-dependently-typed functions. This style of relation resembles the ones
used to show that a compiler produces outputs that relate to their inputs.
Changes are then ``well-behaved'' if they are the erasure of a based
change.\footnote{\citeauthor{CaiEtAl2014ILC} use different terminology: They say
``changes'' instead of ``based changes'', and ``erased changes'' instead of
``changes''. Here we change terms to use a single, consistent terminology.}

\paragraph{Relating the two models}
The two approaches have a different architecture, but reach similar results.
In particular, they give the same definition and predict the same behavior for
|eval(derive t)| in any example we are aware of.

Based on a partial mechanized proof, we conjecture that a change is valid in
\ilcB{} if and only if it is the erasure of a based change in \ilcA{}.

We have sketched a mechanized proof of this conjecture, and have a partial proof
for functions. To complete this proof, we would however need to combine the two
definitions of change structures (the one in \ilcA{} using based change sets and
the one in \ilcB{} using plain change sets), and show each operation mirrors the
other one. For instance, we'd need proofs relating the different definitions of
|`oplus`|, so that |erases a da da' -> a `oplus` da = a `oplus` da'|.
We have not completed such proofs as of this writing.

% We have also sketched a proof of our conjecture. However,

% In this thesis we have given a novel semantic model of function changes.

% In particular, we focus on change
% validity for function spaces, and its role in the overall proof
% of |derive(param)|'s correctness. Specifically, we compare
% new-style valid function changes to old-style ones, and sketch in
% which sense they are equivalent.

We have seen that based function changes have type |df : (a : A) -> Dt^a ->
Dt^(f a)|. However, based function changes have to also satisfy an additional
equation called \emph{preservation of future}:\footnote{Name suggested by Yufei Cai.}
  \[|f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da)|.\]
This equation appears inelegant, and formal proofs were often complicated by the
need to perform rewritings using it.
If we replace |f1 `oplus` df| with |f2| and |a1 `oplus` da| with |a2|, this
equation becomes |f1 a1 `oplus` df a1 da = f2 a2|, a consequence of |fromto f1
df f2|. So one might suspect that valid function changes also satisfy this
equation. We show this is indeed the case:

% This equation is one requirement that old-style function changes
% had to satisfy. What we have seen is that the new-style
% definition of validity, although different (and we believe
% simpler), implies the same equation.
% First, we show that our valid function changes satisfy
\begin{lemma}
  A valid function change |fromto (A -> B) f1 df f2| satisfies equation
  \[|f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da)|\]
  on any valid input |fromto (A -> B) a1 da a2|.
\end{lemma}
\begin{proof}
Assume |fromto (A -> B) f1 df f2| and |fromto A a1 da
a2|.
We have to show |f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da)|.

From the hypotheses one can briefly show that |fromto B (f1 a1) (df a1 da) (f2
a2)|, that |f2 = f1 `oplus` df| and that |a2 = a1 `oplus` da|.
We have seen in \cref{eq:fun-preserv-eq} that |f2 a2 = f1 a1
`oplus` df a1 da|.
Combining these equations, it follows as desired that
\begin{equational}
  \begin{code}
  f1 a1 `oplus` df a1 da
=
  f2 a2
=
  (f1 `oplus` df) (a1 `oplus` da)
  \end{code}
\end{equational}
% \[
%   |f1 a1 `oplus` df a1 da = (f1 `oplus` df) (a1 `oplus` da) = f1
%   (a1 `oplus` da) `oplus` df (a1 `oplus` da) (nil (a1 `oplus`
%   da))|.\]
\end{proof}
Beware, however, this equation on changes is not actually equivalent to the same
equation for based changes, since variables quantify over different sets (based
change sets versus change sets) and since operators like |`oplus`| refer to
different (though related) operations.

Also beware the two models are unlikely to be isomorphic in any straightforward
sense. Initially, we conjectured such an isomorphism would actually exist and
tried defining it. Please keep in mind we work in a constructive setting, hence
we tried defining a constructive isomorphism.
%
However, try converting a based function change |df' : Dt^f| with source |f : A
-> B| to a valid function change |df : Dt^(A -> B) = \(a : A) (da : Dt^A) ->
dt|. We would expect |dt| to compute |df' a da|, modulo a few conversions. But
first, |da| need not be valid. We'd have to generate some output change anyway.
We can pick |df a (nil a)|, or |nil (f a)|, or something else. But then, if
|df'| results from converting a valid function change |df0|, |df| will not have
the same behavior as |df0| on invalid changes. Hence, our conversion would not
be an isomorphism.
Worse, in a constructive and proof-relevant setting, we need to a decision
procedure that given |a : A| and |da : Dt^A| produces either a proof that |da|
is valid for |a|, or a proof that it is not valid. But validity might be
undecidable in general, especially if |A| is in turn a set of functions.

Overall, the relation between the two models is vaguely similar to the relation
between two models of the same language: while their elements have different
characteristics, they enable showing similar facts about the language (though
not necessarily the same ones).

% While that formulation has lots of conceptual elegance, programs
% produced by |derive(param)| are expressed in STLC, which does not
% support dependent types and cannot express proofs; hence
% |derive(param)| cannot produce changes that are valid according
% to \citeauthor{CaiEtAl2014ILC}. Instead,
% \citeauthor{CaiEtAl2014ILC} need to give a separate semantics
% mapping terms to their validity-embedding changes, and then
% relate validity-embedding changes to the ``erased changes''
% produced by |derive(param)|.\footnote{While we didn't realize
%   back then, we could have probably reused the theory of
%   realizability to perform erasure and extract the computational
%   content from validity-embedding changes.} While this additional
% step is not conceptually hard, mechanizing it took significant
% work; moreover, dealing with both validity-embedding changes and
% erased changes introduced significant inelegant noise in quite a
% few definitions and theorem statements.

% Using our formalization, we have also defined a type of
% validity-embedding changes |Dt^v|, with elements that pair a
% change and its validity proof:
% \[|Dt^v = Sigma [ dv `elem` Dt^V ] valid v dv|.\]

% However, such new-style validity-embedding changes are not
% equivalent to old-style changes on function spaces, even if we
% restrict our attention to valid inputs; we need one last step to
% relate them together. Take an arbitrary function |f1 : A -> B|.
% For \citeauthor{CaiEtAl2014ILC}, |df' : Dt^f1| means that |df'|
% maps validity-embedding changes to validity-embedding changes;
% for us, |df' : Dt^f1| means that |df'| contains (1) a map |df|
% from changes to changes and (2) a proof that |df| preserves
% validity: in a sense, new-style changes split what was a map of
% validity-embedding changes into its action on changes and its
% action on validity proofs. This ``splitting'' becomes trickier
% for higher-order function types, such as |(A -> B) -> (C -> D)|,
% so it must be defined by induction on types; essentially, we need
% to adapt \citeauthor{CaiEtAl2014ILC}'s erasure.

% We have not attempted a mechanization of the full equivalence,
% but we have been satisfied with mechanizing several fragments
% without further issues.

\paragraph{Mechanization overhead}
The mechanization of \ilcB{} appears simpler and
smaller than the mechanization for \ilcA{}, because we avoid needing erasure,
but also for other smaller simplifications.

Most importantly, our fundamental relation is ``two-sided''
(|fromto V v1 dv v2|) rather than ``one-sided'' (|valid V v dv| or |dv : Dt^v|);
that is, validity specifies both the source and the destination
explicitly. This is easier now that validity proofs are separate
from changes. While this might seem trivial, it's somewhat
significant for functions, especially in terms of mechanization
overhead in Agda.
%
Indeed, \ilcB{} validity allows stating that |df : Dt^(A -> B)|
is a change from |f1| to |f2|, instead of stating that |df| is a
change from |f1| to |f1 `oplus` df = \a -> f1 a `oplus` df a (nil
a)|. What's more, assume |fromto A a1 da a2|: according to
\ilcB validity preservation, change |df a1 da| has
destination |f2 a2|. Instead, according to \ilcA{} validity
preservation, change |df a1 da| has destination |(f1 `oplus` df)
(a1 `oplus` da)|, that is |f1 (a1 `oplus` da) `oplus` df (a1
`oplus` da) (nil (a1 `oplus` da))|, which adds significant noise
to mechanized proving with \ilcA definitions.

\subsection{Further alternatives and related work}
%\paragraph{Possible alternatives and related work}
\paragraph{Junkless models}
Change sets in \ilcB{} contain invalid elements, or \emph{junk}
A model without junk, like \ilcA{}, can be desirable.\pg{Can it?}
We conjecture we could combine
the benefits of the two models by defining change sets indexed from both sides:

|Dt2 (A -> B) f1 f2 = Dt2 A a1 a2 -> Dt2 B (f1 a1) (f2 a2)|.

One could then define a set of valid changes containing their source and
destination:

|Dt^V = exists v1 : V, v2 : V. ^^ Dt2^V v1 v2|.

In this approach, |Dt^(A -> B)| is not a set of functions, but we can still
define an operation that applies an element of |Dt^(A -> B)| to an element of
|Dt^A| and produces an element of |Dt^B|.

We believe the main open question is not whether defining such a model is
possible, but about the formalization overhead and their exact properties.

Such junkless models are closely related to models based on directed graphs and reflexive
graphs, where values are graphs vertexes, changes are edges between change
source and change destination (as hinted earlier). In graph language, validity
preservation means that function changes are graph homomorphisms.

Based on similar insights, \citet{Atkey2015ILC} suggests modeling ILC using
reflexive graphs, which have been used to construct parametric models for System
F and extensions, and calls for research on the relation between ILC and
parametricity.
As a follow-up work \citet{CaiPhD} studies models of ILC based on directed and
reflexive graphs.

Both parametricity and ILC define logical relations across program executions on
different inputs. When studying parametricity, differences are only allowed in
the implementations of abstractions (through abstract types or other
mechanisms). To be related, different implementations of the same abstraction
must give results that are equivalent according to the calling program.
Indeed, parametricity defines not just a logical relation but a \emph{logical
equivalence}, that can be shown to be equivalent to contextual
equivalence~\citet{Ahmed2006stepindexed}.

In ILC, instead, |fromto V v1 dv v2| holds even if |v1| and |v2| are different
and this difference is observable in the program, but require that |dv| is a
correct description of these differences.

Similarly to our proof, \citet*{Acar08} prove correctness of incrementalization
using a logical relation across executions of programs on base and updated
inputs. There, incremental computation proceeds by executing the same program
using an incremental semantics.
The proof is done on an untyped language using a step-indexed logical relation,
and authors choose to use a step-indexed big-step semantics, where the
step-indexing is sound relative to step counts for a standard small-step
semantics.
Based on a few preliminary
experiments by me and Yann Régis-Gianas, we conjecture it should be possible to
adapt the approach to step-indexing in that proof to give a correctness proof of
ILC on an untyped language using an operational semantics.

\Citeauthor*{Acar08}'s step-indexed logical relation for incremental computation
resembles the step-indexed logical relation by \citet{Ahmed2006stepindexed} to
model parametricity and program equivalence.
However, if terms |t1| and |t2| are
related according to \citeauthor*{Ahmed2006stepindexed}'s program equivalence
(at a certain step count) and |t1| terminates (at certain step counts), then
|t2| terminates and |t1| and |t2|'s results are related (at a certain step count).
Instead, if terms |t1| and |t2| are related according to \citeauthor*{Acar08}'s
relation (at a certain step count),
|t1| terminates (at certain step counts) \emph{and} |t2| terminates,
\emph{then} |t1| and |t2|'s results are related (at a certain step count).%
\footnote{The step-indexing details we omit are the same in both definitions.}
That is, with \citeauthor*{Acar08}'s logical relation, termination of |t1| in no
way implies termination of |t2|, exactly because |t1| and |t2| need not be
equivalent.

Let us see concretely why a logical relation for incrementalization must relate |t1|
and |t2| even if they are not equivalent and in particular |t1| terminates and |t2|
doesn't. Consider incrementalizing function |t = if x then 0 else loop| when |x|
goes from |true| to |false|, assuming that |loop| is a diverging subterm. Such a
change for |x| is valid, hence it must be mapped (by function application and
$\beta$-reduction) to a valid change from terminating term |if true then 0 else
loop| to non-terminating term |if false then 0 else loop|.

\section{The relation with parametricity and the abstraction theorem}

In this section we discuss similarities between correctness of |derive(param)|
(\cref{thm:derive-correct}) and the fundamental property of logical relations,
for the case of binary logical relations. This section is intended for logical
relation experts, and we keep it rather informal.

%format ppp(t) = "\mathcal{P}(" t ")"

Most studies of logical relations mention no term transformation that relates to
|derive(param)|; one exception is given by \citet{Bernardy2011realizability}.
They study relational parametricity, a particular binary logical relation, where
the fundamental property of logical relations becomes the abstraction theorem. To
prove the abstraction theorem, \citeauthor{Bernardy2011realizability} present a
term transformation |ppp(param)|; we'll show the analogy between this term
transformation and
|derive(param)|.%
%
\footnote{\citeauthor{Bernardy2011realizability} were not the first to introduce
  such a transformation, but we base our comparison off their presentation and
  avoid discussing their related work.}

Transformation |ppp(t)| takes a term |t| to a proof term |ppp(t)| in a suitable
object logic (related to the one of |t|), that proves that |t| maps logically
related inputs to logically related outputs. For binary logical relations and
simply-typed $\lambda$-calculus, we can specialize their definition to the
following:

%format (idx1 (t)) = "\mathcal{S}_1(" t ")"
%format (idx2 (t)) = "\mathcal{S}_2(" t ")"

\begin{code}
  (t1, t2) `elem` r(sigma -> tau) =
    forall x1 x2 : sigma, px : (x1, x2) `elem` r(sigma). (t1 x1, t2 x2) `elem` r(tau)
  ppp(x) =
      px
  ppp(\(x : sigma) -> t) =
    \(x1 x2 : sigma) (px : (x1, x2) `elem` r(sigma)) -> ppp(t)
  ppp(s t) =
    ppp(s) (idx1 s) (idx2 s) ppp(t)
\end{code}

where |idx1 s| and |idx2 s| subscript variables in terms with 1 and 2:
\begin{code}
  idx1(x) = x1
  idx1(\(x : sigma) -> t) = \(x1 : sigma) -> idx1 t
  idx1(s t) = (idx1 s) (idx1 t)

  idx2(x) = x2
  idx2(\(x : sigma) -> t) = \(x2 : sigma) -> idx2 t
  idx2(s t) = (idx2 s) (idx2 t)
\end{code}

To see the analogy, let's show a variant of differentiation. This time,
|derive(\x -> t) = \x1 x2 dx -> derive(t)| is a function that binds not just the
source of |dx|, but also its target, and the additional symmetry simplifies its
theoretical study.

\begin{code}
  Dt2 : (v1 v2 : V)
  Dt2 : (v1 v2 : V) -> Set
  Dt2 v1 v2 = Sigma [ dv `elem` Dt^V ] (fromto sigma v1 dv v2)
  (f1, df, f2) `elem` r(sigma -> tau) =
    forall x1, dx, x2 : sigma, dxx : r(sigma) . (f1 x1, df x1 x2 dx, f2 x2) `elem` r(tau)

  derive(x) = dx
  derive(\(x : sigma) -> t) = \x1 x2 (dx : Dt2 x1 x2) -> derive(t)
  derive(s t) = derive(s) (idx1 s) (idx2 s) (derive t)

  derive(\(x : sigma) -> t) = \x1 x2 (fromto sigma x1 dx x2) -> derive(t)
\end{code}

\pg{connection}
For readers familiar with staging,
we explain how \citeauthor{Bernardy2011realizability}'s
transformation relates to standard proofs of the abstraction theorem.
In short, (a) the usual proof of the abstraction theorem
can be regarded as an \emph{interpreter} from object-level terms to metalevel
proofs; (b) standard interpreters can be turned into compilers by staging, so
that they evaluate object-level code for a function instead of the function
itself at the metalevel; (c) an ``interpreter'' that produces a metalevel proof
can be staged into a ``compiler'' (or term transformation) into an object-level
proof term in a suitable logic; (d) the above definition of |p(t)| corresponds
(informally) to staging the proof of the abstraction theorem.
\begin{enumerate}
\item Recall that the abstraction theorem is proven by
induction on terms.\footnote{Or on typing derivations, but as discussed we
  regard the two as isomorphic, since typing is syntax-directed.} Let's write
|P(t)| to say that term |t| satisfies the abstraction theorem; then the theorem
statement is |forall t. P(t)| in the metalevel logic. The proof is constructive,
so we can regard it (informally) under the lens of the Curry-Howard isomorphism.
Under this lens, a metalevel proof of |forall t. P (t)| is a function from terms
|t| to a metalevel proof of |P(t)|; a proof by induction is a structurally
recursive function from terms to metalevel proofs, just like an interpreter is a
structural recursive function from terms to metalevel functions. Hence, we
regard the proof of the abstraction theorem as an interpreter.
\item Staging an interpreter produces a compiler, which evaluates
  not to a value |v| but to code that will later evaluate to
  value |v|; this code will already be specialized for the input
  term.
\item Similarly, by staging an interpreter that produces proofs,
  we produce a compiler from term to proofs.
\end{enumerate}

% Most other proofs,
% instead of creating a proof term, but simply produce a similar proof in the meta
% logic by induction on terms. The two proof strategies are related by an analogue
% of staging.


% Here we discuss the relation with parametricity, the abstraction theorem, and
% the fundamental property of logical relations, for readers familiar with these
% topics. Parametricity is typically studied for type systems containing System F,
% but \citet{Bernardy2011realizability} generalize it to arbitrary PTSs.



% Correctness of |derive(param)| (\cref{thm:derive-correct}) relates to binary
% parametricity. However, usual statements of binary parametricity mention no
% analog of changes or |derive(param)|. One defines a relational interpretation of
% terms, mapping input relations to output relations, and shows this maps


\chapter{Language plugins for products and sums}
\label{ch:prod-sums}

In this section, we show language plugins for sum and product
types.

\pg{Extend by showing the base semantics of these plugins.}
We give ways to give change structures for products and sums.
As primitives, we use the introduction and elimination forms for
these types. Then, we show how to obtain derivatives for these
primitives.

\pg{Consider recursive types, and recursion?}

\section{A change structure for sums}
\label{sec:chs-sums}
We can define change structures on disjoint sums |A + B|, given
change structures on |A| and |B|.
\pg{resume.}


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

\chapter{Misc}

\section{Completely invalid changes}
\label{sec:very-invalid}
\pg{Not sure that the reference to sec;invalid should go here. Ok, probably not.}
In some change sets, some changes might not be valid relative to
any source. In particular, we can construct examples in |Dt^(Int
-> Int)|.

To understand why this is plausible, we recall that as described
in \cref{ssec:pointwise-changes}, |df| can be decomposed into a
derivative, and a pointwise function change that is independent
of |da|. While pointwise changes can be defined arbitrarily, the
behavior of the derivative of |f| on changes is determined by the
behavior of |f|.

\begin{example}
  We search for a function change |df : Dt^(Int -> Int)| such
that there exist no |f1, f2: Int -> Int| for which
|fromto (Int -> Int) f1 df f2|. To find |df|, we assume that there are |f1, f2| such that |fromto
(Int -> Int) f1 df f2|, prove a few consequences, and construct
|df| that cannot satisfy them. Alternatively, we could pick the
desired definition for |df| right away, and prove by
contradiction that there exist no |f1, f2| such that |fromto (Int -> Int) f1 df
f2|.

Recall that on integers |a1 `oplus` da = a1 + da|, and that
|fromto Int a1 da a2| means |a2 = a1 `oplus` da = a1 + da|.
So, for any numbers |a1, da, a2| such that |a1 + da = a2|, validity of |df| implies that
\[|f2 (a1 + da) = f1 a1 + df a1 da|.\]

For any two numbers |b1, db| such that |b1 + db = a1 + da|,
we have that
\[|f1 a1 + df a1 da = f2 (a1 + da) = f2 (b1 + db) = f1 b1 + df b1 db|.\]

Rearranging terms, we have
\[|df a1 da - df b1 db = f1 b1 - f1 a1|,\]
that is, |df a1 da - df b1 db| does not depend on |da| and |db|.

For concreteness, let us fix |a1 = 0|, |b1 = 1|, and |a1 + da = b1 + db = s|. We have then that
\[|df 0 s - df 1 (s - 1) = f1 1 - f1 0|,\]
Once we set |h = f1 1 - f1 0|, we have |df 0 s - df 1 (s - 1) =
h|.
Because |s| is just the sum of two arbitrary numbers, while |h|
only depends on |f1|, this equation must hold for a fixed |h| and
for all integers |s|.

To sum up, we assumed for a given |df| there exists |f1, f2| such
that |fromto (Int -> Int) f1 df f2|, and concluded that there
exists |h = f1 1 - f1 0| such that for all |s|
\[|df 0 s - df 1 (s - 1) = h|.\]

At this point, we can try concrete families of functions |df| to
obtain a contradiction. Substituting a linear polynomial $|df a
da| = c_1 \cdot a + c_2 \cdot |da|$ fails to obtain a
contradiction: in fact, we can construct various |f1, f2| such
that |fromto (Int -> Int) f1 df f2|. So we try quadratic
polynomials: Substituting $|df a da| = c \cdot |da|^2$ succeeds:
we have that there is |h| such that for all integers |s|
\[c \cdot \left(s^2 - (s - 1)^2\right) = h.\]

However, $c \cdot \left(s^2 - (s - 1)^2\right) = 2 \cdot c \cdot
s - c$ which isn't constant, so there can be no such |h|.
\end{example}

% Because of |fromto (Int -> Int) f1 df f2| and because |`oplus`|
% respects validity we can show that, for any valid input |fromto
% Int a1 da a2|, we have
% \begin{equation}
%   \label{eq:ex-invalid-int-int}
%   |f2 a2 = f1 a1 `oplus` df a1 da|.
% \end{equation}

% Recall that on integers |a1 `oplus` da = a1 + da|, and that
% |fromto Int a1 da a2| means |a2 = a1 `oplus` da = a1 + da|. So
% \cref{eq:ex-invalid-int-int} becomes
% \begin{equation}
%   %\label{eq:ex-invalid-int-int}
%   |f2 (a1 + da) = f1 a1 + df a1 da|.
% \end{equation}



\section{A higher-order example}
\label{sec:differentiation-fold-example}
\pg{write}
% Referenced later in sec-performance.tex by saying:
% % We have seen in \cref{ssec:differentiation} that $\Derivative$
% % needlessly recomputes $\Merge\Xs\Ys$. However, the result is a
% % base input to $\FOLD'$.

\section{General recursion}
\label{sec:general-recursion}
\pg{write, and put somewhere. Use the example with |map| on lists.}

This section discusses informally how to differentiate terms
using general recursion and what is the behavior of the resulting terms.

\subsection{Differentiating general recursion}
%format letrec = "\mathbf{letrec}"
%format fix = "\mathbf{fix}"

Earlier we gave a rule for deriving (non-recursive) |lett|:
\begin{code}
derive(lett x = t1 in t2) =
  lett  x = t1
        dx = derive(t1)
  in    derive(t2)
\end{code}
It turns out that we can use the same rule also for recursive
|lett|-bindings, which we write here |letrec| for clarity:
\begin{code}
derive(letrec x = t1 in t2) =
  lett  x = t1
        dx = derive(t1)
  in    derive(t2)
\end{code}

\pg{Reorganize. This order makes no sense.}
\begin{example}
  In \cref{ex:syn-changes-map} we presented a derivative for
  |map|.
  We now rewrite |map| using fixpoint combinators and derive the
  |dmap| applying the rule for deriving |fix|.
% \begin{code}
% map f = fix go
%   where
%     go self Nil = Nil
%     go self (Cons x xs) = Cons (f x) (self xs)
% \end{code}

% Applying the derivation rules, we get that
% |dmap f df = fix ((derive go) (fix go))|,
% and since |fix go = map f| we can write:
% \begin{code}
% dmap f df = fix (dgo (map f))
%   where
%     dgo self dself Nil Nil = Nil
%     dgo self dself (Cons x xs) (Cons dx dxs) =
%       Cons (df x dx) (dself xs dxs)
% \end{code}
We can finally show that
\begin{code}
dmap f df Nil Nil = Nil
dmap f df (Cons x xs) (Cons dx dxs) =
  Cons (df x dx) (dmap f df xs dxs)
\end{code}
\end{example}

\subsection{Justification}
However, we justify this rule using fixpoint operators.

Let's consider STLC extended with a family of standard fixpoint
combinators $\Varid{fix}_{|tau|}|: (tau -> tau) -> tau|$, with
|fix|-reduction defined by equation |fix f -> f (fix f)|; we
search for a definition of |derive (fix f)|.

Using informal equational reasoning, if a correct definition of
|derive (fix f)| exists, it must be
\begin{code}
  derive (fix f) = fix ((derive f (fix f)))
\end{code}
\pg{use |`cong`|?}

We can proceed as follows:
% We recall that the derivative of a closed term is its nil change.
\begin{equational}
\begin{code}
   derive (fix f)
=  {- imposing that |derive| respects |fix|-reduction here -}
   derive (f (fix f))
=  {- using rules for |derive| on application -}
   (derive f) (fix f) (derive (fix f))
\end{code}
\end{equational}

This is a recursive equation in |derive (fix f)|, so we can try
to solve it using |fix| itself:
\begin{code}
  derive (fix f) = fix (\dfixf -> (derive f (fix f) dfixf))
\end{code}

Indeed, this rule gives a correct derivative.
Formalizing our reasoning using denotational semantics would
presumably require the use of domain theory. We leave
such a formalization for future work.
However, we do prove correct a variant of |fix| in
\cref{ch:bsos}, but using operational semantics.

% In particular
% \begin{code}
%    derive (fix (\ff -> t))
% =
%    fix (\dff -> (derive (\ff -> t) (fix (\ff -> t)) dff))
% =
%    fix (\dff -> derive t [ff := fix (\ff -> t)])
% \end{code}

% % |let ffact = fix (\ffact n -> n * ffact (n - 1)) in t2 =
% % letrec ffact = \n -> n * ffact (n - 1) in t2|
% % |
% % This rule is equivalent

% We can also derive the rule for |letrec|, based on this rewrite rule:
% |let ff = fix (\ff -> t) in t2 = letrec ff = t in t2|.
% We proceed as follows:
% \begin{equational}
% \begin{code}
%    derive(letrec ff = t in t2)
% =  {- -}
%    derive(lett ff = fix (\ff -> t) in t2)
% =  {- deriving |let| -}
%    let
%      ff   = fix (\ff -> t)
%      dff  = derive (fix (\ff -> t))
%    in derive t2
% =  {- deriving |fix| -}
%    let
%      ff   = fix (\ff -> t)
%      dff  = fix (\dff -> derive t [ff := (fix (\ff -> t))])
%    in derive t2
% =  {- deinline binding of |ff| -}
%    let
%      ff   = fix (\ff -> t)
%      dff  = fix (\dff -> derive t)
%    in derive t2
% =  {- |let| to |letrec| -}
%    letrec
%      ff   = t
%    in let
%      dff  = fix (\dff -> derive t)
%    in derive t2
% =  {- |let| to |letrec| -}
%    letrec
%      ff   = t
%      dff  = derive t
%    in derive t2
% \end{code}
% \end{equational}
