% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Equational reasoning on changes}
\label{sec:term-reasoning}
\label{ch:term-reasoning}

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
denotational equivalence, but must restrict to consider valid
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
Let's consider again the example from
\cref{sec:simple-changes-list-map}, in particular |dmap|.
Recall that a list change |dxs| is valid for source |xs| if
they have the same length and each element change is valid for
its corresponding element.

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

\subsection{Denotational equivalence for valid changes}
\label{sec:denot-equivalence-valid}
This example uses the notion of denotational equivalence for valid
changes. We now proceed to formalize it.
For reference, we recall denotational equivalence of terms, and then
introduce its restriction:
\begin{restatable*}[Denotational equivalence]{definition}{denotEqual}
  \label{def:denot-equivalence}
  We say that two terms |Gamma /- t1 : tau| and |Gamma /- t2:
  tau| are denotationally equal, and write |Gamma //= t1 `cong` t2
  : tau| (or sometimes |t1 `cong` t2|), if for all environments
  |rho : eval Gamma| we have that |eval t1 rho = eval t2 rho|.
\end{restatable*}

For open terms |t1, t2| that depend on changes,
denotational equivalence is too restrictive, since it
requires |t1| and |t2| to also be equal when the changes they
depend on are not valid.
By restricting denotational equivalence to valid environment
changes, and terms to depend on contexts, we obtain the following definition.
\begin{definition}[Denotational equivalence for valid changes]
  \label{def:denot-equivalence-valid-changes}
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
semantics of change programs; it might be more preferable to make the type of
changes abstract throughout the program (except for derivatives of primitives,
which must inspect derivatives), but this is not immediate, especially in a
module system like Haskell.
Other possible alternatives are discussed in \cref{sec:alt-change-validity}.

\subsection{Syntactic validity}
\label{sec:denot-syntactic-validity}
Next, we define \emph{syntactic validity}, that is,
when a change \emph{term} |dt| is a (valid) change
from source term |t1| to destination |t2|. Intuitively, |dt| is valid
from |t1| to |t2| if |dt|, |t1| and |t2|, evaluated all
against the same valid environment change |drho|, produce a
valid change, its source and destination. Formally:
\begin{definition}[Syntactic validity]
  \label{def:syntactic-validity}
  We say that term |Dt^Gamma /- dt : Dt^tau| is a (syntactic)
  change from |Dt^Gamma /- t1 : tau| to |Dt^Gamma /- t2 : tau|, and write
  |fromtosyn Gamma tau t1 dt t2|, if
  \[|forall (fromto Gamma rho1 drho rho2). fromto tau (eval t1 drho) (eval dt drho) (eval t2 drho)|.\]
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
denotational equivalence for valid changes.
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
  in |rho1|, we can show that |eval t drho = eval t rho1|, so
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
  of changes \[\{|dv `elem` Dt^V `such` dv| \text{ is valid with source } |v|\}.\]
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
\cref{thm:derive-preserve-doe}. We also need a notation for \emph{one-sided}
or \emph{source-only} validity.

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
\begin{proof}[Proof sketch]
  The thesis holds because |derive| preserves change equivalence
  \cref{lem:eval-derive-preserve-doe}.
  A formal proof follows through routine (and tedious)
  manipulations of bindings. In essence, we can extend a change environment
  |drho| for context |Gamma| to
  equivalent environment changes for context |Gamma , x : sigma|
  with the values of |dsa| and |dsb|. The tedious calculations
  follow.
\end{proof}

\begin{proof}
  % A corollary of \cref{lem:eval-derive-preserve-doe} and of a substitution lemma
  % relating substitution and denotational semantics: |eval (t) (x = eval s rho,
  % rho) = eval(t [x := s]) rho|.

  Assume |fromto Gamma rho1 drho rho2|.
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
with dependent types, but as discussed the overall proof is more awkward.
Alternatively, it appears that the use of dependent types in
\cref{ch:diff-parametricity-system-f} also ensures that change equivalence is a
congruence (though at present this is still a conjecture), without overly
complicating correctness proofs.
However, it is not clear whether such a type system can be
expressive enough without requiring additional coercions.
Consider a change |dv1| from |v1| to |v1 `oplus` dv1|, a
value |v2| which is known to be (propositionally) equal to |v1 `oplus` dv1|, and
a change |dv2| from |v2| to |v3|. Then, term |dv1 `ocompose` dv2| is not type
correct (for instance in Agda): the typechecker will complain that |dv1| has
destination |v1 `oplus` dv1| while |dv2| has source |v2|. When working in Agda,
to solve this problem we can explicitly coerce terms through propositional
equalities, and can use Agda to prove such equalities in the first place.
We leave the design of a sufficiently expressive object language where change
equivalence is a congruence for future work.

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
equivalence is a partial equivalence relation
(PER)~\citep[Ch.~5]{Mitchell1996foundations}. It is standard to use PERs to
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
relations and PERs at the same time~\citep[Ch.~8]{Mitchell1996foundations}.
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
