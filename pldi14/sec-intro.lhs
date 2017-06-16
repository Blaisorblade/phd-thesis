% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Syntactic stuff}

\pg{TODO add more.}
Finally, we relate this formalization of changes with the one by
\citet{CaiEtAl2014ILC} in \cref{sec:alt-change-validity}.

\section{Reasoning on changes syntactically}
To define derivatives of primitives, we will often discuss
validity of changes directly on programs, for instance saying
that |dx| is a valid change from |x| to |x `oplus` dx|. In this
section, we define formally what this means.

% % Hence, we define when

% and say that |dt| is a change from
% |t1| to |t2|

% \pg{Try next paragraph:}
% Up to now, we can say that |eval dx| is a change from |eval x| to
% |eval x|. We'll start saying that |dx| is a change from |x| to |x
% `oplus` dx|.

\begin{example}[Deriving |map| on lists]
  \label{ex:syn-changes-map}
We consider a basic change structure on lists and the
derivative of |map|. We will describe this example very
informally; to see how such a change structure might be
formalized, compare with the change structure for environments
described earlier in \cref{def:chs-envs}. We'll describe a more
realistic change structure for sequences later.

For instance, consider a basic change structure on cons-lists of type
|List a|, where a list change is just a list of element changes
|List (Dt^a)|. A list change |dxs| is valid for source |xs| if
they have the same length and each element change is valid for
its corresponding element.
On this basic change structure, we can define |`oplus`| and
|`ocompose`| but not |`ominus`|: such list changes can't express the
difference between two lists of different lengths.
Nevertheless, this basic change structure is sufficient to define
derivatives, which act correctly on the changes that can be expressed.

If we define |map : List a -> List a| as a primitive, and not as
a derived function defined in terms of some other primitive, we
can write derivative |dmap| as follows (in Haskell notation):
\begin{code}
  dmap f df [] [] = []
  dmap f df (x : xs) (dx : dxs) =
    df x dx : dmap f df xs dxs
\end{code}
In the equation for cons nodes |x : xs|, change |dx| describes
the change between |x| and |x `oplus` dx|, and |df x dx|
describes the change between |f x| and |f (x `oplus` dx)|.
So, by induction on the length of |xs| and |dxs|, one could show
that |dmap f df xs dxs| describes the change between |map f xs|
and |map (f `oplus` df) (xs `oplus` dxs)|. And as a consequence,
terms |map (f `oplus` df) (xs `oplus` dxs)| and |map f xs `oplus`
dmap f df xs dxs| are interchangeable in all valid contexts, that
is, contexts that bind |df| and |dxs| to valid changes,
respectively, for |f| and |xs|.
\end{example}

To support this reasoning, we define a few concepts. First, we
need to say when two terms can be replaced for each other, but
only as long as changes in the environments are valid.
Hence, we define denotational equality for valid changes.
For reference, we first recall denotational equality of terms:
\begin{definition}[Denotational equality]
  We say that two terms |Gamma /- t1 : tau| and |Gamma /- t2:
  tau|, and write |t1 `cong` t2| are denotationally equal if, for
  all environments |rho : eval Gamma| we have that |eval t1 rho =
  eval t2 rho|.
\end{definition}

Now we restrict denotational equality to valid environment
changes:
\begin{definition}[Denotational equality for valid changes]
  For any context |Gamma| and type |tau|,
  we say that two terms |Dt^Gamma /- t1 : tau| and |Dt^Gamma /-
  t2 : tau| are \emph{denotationally equal for valid changes} and
  write |Dt^Gamma /- t1 `congDt` t2 : tau| if, for all valid
  environment changes |fromto Gamma rho1 drho rho2| we have that
  |eval t1 drho = eval t2 drho|.
\end{definition}
In other words, to restrict denotational equality to valid
changes, we require |t1| and |t2| to be defined in a change
typing context, and quantify only over valid environments.
\begin{example}
One of our claims in \cref{ex:syn-changes-map} can now be written
as
\[|Dt^Gamma /- map (f `oplus` df) (xs `oplus` dxs) `congDt` map f
  xs `oplus` dmap f df xs dxs : List t|\]
for a suitable |Gamma|.
\end{example}

Next, we define the concept of \emph{syntactic
validity}, that is, when a change term |dt| is a (valid) change
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
Using syntactic validity, we can show for instance that |dx| is a change
from |x| to |x `oplus` dx|. In general, we have:
\begin{lemma}[|`oplus`| agrees with syntactic validity]
If |dt| is a change from |t1| to |t2| (|fromtosyn Gamma tau t1 dt
t2|) then |t1 `oplus` dt| and |t2| are denotationally equal for
valid changes (|Dt^Gamma /- t1 `oplus` dt `congDt`|).
\end{lemma}
\begin{proof}
  Follows because term-level |`oplus`| agrees with |`oplus`|
  (\cref{lem:chops-coherent}) and |`oplus`| agrees with validity.
  In more detail: fix an arbitrary valid environment change |fromto Gamma rho1 drho rho2|.
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

% evaluate to equal
% results in any valid change environment |drho|.
\pg{lemma! or start making all these facts?}
\pg{introduce contextual equivalence in valid environment changes.}

We can also do the reasoning in earlier
example \cref{ex:syn-changes-map}.\pg{check}
\pg{Made this up, check and show this.}
\pg{continue}

\pg{Define change structures on terms?}
\paragraph{Discussion}
We defined earlier a change structure on the domain of the
\emph{denotations} of terms, that is |eval Gamma -> eval tau|.
We could use this as a change structure on terms, but the
resulting change structure is far less useful.
In particular, if |\rho drho -> eval dt drho| is a change from |eval t1|
to |eval t2|, it does not follow that |t1 `oplus` dt `cong`
t2|.\pg{never true, define another cong relation?}
Indeed, in the latter statement, all terms are evaluated in the
same environment; instead, when we say that |\rho drho -> eval dt
drho| is a change from |eval t1| to |eval t2|, we in fact
evaluate |t2| according to an updated environment.
So we can satisfy |t1 `oplus` dt `cong` t2| with |t1 = x|, |dt =
dx| and |t2 = x `oplus` dx|. Yet, |\rho drho -> eval dx drho| is
a change from |eval x| to |eval x|, not to |eval (x `oplus` dx)|.

%but rather that |eval t1 rho `oplus` eval dt (nil rho) = eval t2 rho|
Let us see why in more detail by recalling earlier notions.
When we state correctness of differentiation using the change
structure on |eval Gamma -> eval tau|, we say that |evalInc t =
\rho drho -> eval (derive t) drho| is a change from |eval t| to
|eval t|. Recall that, according to validity as defined by this
change structure, we say that |\rho1 drho -> eval dt drho| is a
valid change from |eval t1| to |eval t2| if for all valid
environment changes |fromto Gamma rho1 drho rho2| we have that
|eval dt drho| is a valid change from |eval t1 rho1| and |eval t2
rho2|. Hence we have
\begin{equation}
  \label{eq:sem-validity-oplus-eval}
|forall (fromto Gamma rho1 drho rho2). eval t1 rho1 `oplus` eval dt drho = eval t2 rho2|.
\end{equation}
For instance, applying correctness of differentiation to term |t
= x|, we have that |eval x rho1 `oplus` eval dx drho = eval x
rho2|.

However, we seek to define validity on terms in a different way.
We want to say when term |dt| is a valid change from term |t1| to
term |t2|, so that as a corollary |t1 `oplus` dt `cong` t2| and
|t1 `oplus` dt| and |t2| are interchangeable in all contexts.
\pg{Uh! Not all contexts! Only contexts with valid environments!}
That is,
\begin{equation}
|forall (fromto Gamma rho1 drho rho2). eval (t1 `oplus` dt) drho = eval t2 drho|.
\end{equation}
Because evaluation commutes with |`oplus`|
(\cref{lem:chops-coherent}), and because a valid environment
change |drho| extends its source |rho1|, this equation is
equivalent to
\begin{equation}
  \label{eq:syn-equiv-envs}
|forall (fromto Gamma rho1 drho rho2). eval t1 rho1 `oplus` eval dt drho = eval t2 rho1|.
\end{equation}
This statement evaluates |t1| and |t2| in \emph{the same}
environment |rho1|, while instead
\cref{eq:sem-validity-oplus-eval} evaluates |t2| against |rho2|.
Hence, we incorporate \cref{eq:syn-equiv-envs} into a new definition.
\pg{Continue.}

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

\pg{Text on change equivalence follows.}

% And conversely, two function changes that map equivalent sources
% to equivalent destinations are also equivalent.
\pg{that lemma disappeared now?}

\section{Change equivalence}
\label{sec:change-equivalence}
\pg{We can use based changes. Better not.}

To optimize programs manipulate changes, we often want to replace a
change-producing term by another one, while preserving the overall program
meaning. Hence, we define an equivalence on valid changes that is preserved by
change operations, that is a \emph{congruence}. We call this relation
\emph{change equivalence}. When it is clear we talk about changes, we will just
talk about equivalence.

Earlier (say, in \cref{ssec:pointwise-changes}) we have sometimes required that
changes be equal, but that's often too restrictive.

Change equivalence is defined in terms of validity, to ensure that
validity-preserving operations preserve change equivalence: If two changes |dv1|
and |dv2| are equivalent, one can be substituted for the other in a
validity-preserving context.

\begin{definition}[Change equivalence]
  Given a change structure |chs(V)|,
  changes |dva, dvb : Dt^V| are equivalent relative to source
  |v1 : V| (written |fromto V v1 (dva `doe` dvb) v2|)
  if and only if there exists |v2| such that both |dva| and
  |dvb| are valid from |v1| to |v2| (that is |fromto V v1 dva
  v2|, |fromto V v1 dvb v2|).
\end{definition}
\begin{notation}
  We often abbreviate |fromto V v1 (dva `doe` dvb) v2| as |dva (doeIdx(v1) dvb|.
  When the source |v1| can be inferred from context, we write |dva `doe` dvb|.
\end{notation}

Two changes are often equivalent relative to a source but not
others. Hence |dva `doe` dvb| is always an abbreviation for
change equivalence for a specific source.
\begin{example}
For instance, we later use a change structure for integers using
both replacement changes and differences (\cref{ex:replacement}).
In this structure, change |0| is nil for all numbers, while
change |!5| (``bang 5'') replaces any number with 5. Hence,
changes |0| and |!5| are equivalent only relative to source 5,
and we write |0 doeIdx(5) !5|.
\end{example}

By applying definitions, one can verify that change equivalence
relative to a source |v| is a symmetric and transitive relation on |Dt^V|.
However, it is not an equivalence relation on |Dt^V|, because it is only
reflexive on changes valid for source |v|. Using the set-theoretic concept of
subset we can then state the following lemma (whose proof we omit as it is
brief):
\begin{lemma}[|`doe`| is an equivalence on valid changes]
  For each set |V| and source |v `elem` V|, change equivalence
  relative to source |v| is an equivalence relation over the set
  of changes $|dv `elem` Dt^V `such` dv| \text{ is valid with source } |v|$.
\end{lemma}
We elaborate on this peculiar sort of equivalence in \cref{sec:doe-per}.

\subsection{Preserving change equivalence}
Change equivalence relative to a source |v| is respected, in an appropriate
sense, by all validity-preserving expression contexts that accept changes with
source |v|.
To explain what this means we study an example lemma: we show that because valid
function changes preserve validity, they also respect change equivalence.
At first, we use ``context'' informally to refer to expression contexts in the
metalanguage. Later, we'll extend our discussion to actual expression contexts.

\begin{lemma}[Valid function changes respect change equivalence]
  \label{lem:ch-respect-doe}
Any valid function change
\[|fromto (A -> B) f1 df f2|\]
respects change equivalence: if |fromto A v1 (dva `doe` dvb) v2| then
|fromto B (f1 v1) (df v1 dva `doe` df v1 dvb) (f2 v2)|.
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

However, \cref{lem:ch-respect-doe} does *not* mean that |df v1 dva = df v1 dvb|,
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

For another example, |v1 `oplus` param| is also a context that accepts changes
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
equivalence: |derive(t) `doe` derive(t)|, that is |fromto (Gamma
-> tau) (eval t) (eval (derive t) `doe` eval (derive t)) (eval
t)|, that is, for all |fromto Gamma rho1 (drhoa `doe` drhob) rho2| we have
|fromto (Gamma -> tau) (eval t rho1) (eval (derive t) drhoa `doe` eval
(derive t) drhob) (eval t rho2)|.
\end{lemma}
\begin{proof}
  To verify this, just apply correctness of differentiation to both changes.
\end{proof}

To show more formally in what sense change equivalence is a congruence, we first
lift it to terms:
\begin{definition}[Term change equivalence]
Two change terms |Dt^Gamma /- dta : Dt^tau|, |Dt^Gamma /- dtb :
Dt^tau| are change equivalent, relative to source |Gamma /- t :
tau|, if for all |fromto Gamma rho1 drho rho2| we have that |eval
dta drho (doeIdx(eval t rho1)) (eval dtb drho)|. We write then |dta
(doeIdx t) dtb| or simply |dta `doe` dtb|.
%|fromto tau v1 (dv1 `doe` dv2) v2|,
\end{definition}
Saying that |dta| and |dtb| are equivalent relative to |t| does not specify the destination of |dta| and |dtb|, only their source.
% Unlike in other similar definition, when changes |dta| and |dtb| are equivalent
% relative to |t| and given equivalent contexts |fromto Gamma rho1 drho rho2|,
% they need
% The equivalence of |dta| and |dtb| relative to |t| does not
% require that the destination is again |t|.
\pg{Use \cref{def:syntactic-validity} to also state the destination.}
\pg{Introduce this earlier}

If two change terms are change equivalent with respect to the
right source, we can replace one for the other to optimize a
program, as long as the evaluation context is validity-preserving and accepts
the change.

In particular, we can substitute equivalent changes in the terms resulting from
differentiation and produce equivalent changes.
\pg{broken theorem}
\begin{theorem}
  \label{thm:derive-preserve-doe}
% If |Gamma, x : sigma /- t : tau| and |dsa `doeIdx(s)` dsb|, then |fromtosyn
% Gamma tau t ((derive t)[x := s, dx := dsa] `doe` (derive t)[x := s, dx := dsa])
% t|.
If |Gamma, x : sigma /- t : tau| and
\[|fromtosyn Gamma sigma s1 (dsa `doe` dsb) s2|\]
then
\[|fromtosyn Gamma tau (t [x := ]) ((derive t)[x := s, dx := dsa] `doe` (derive t)[x :=
s, dx := dsb]) t|.\]
\end{theorem}
We have not mechanized this lemma.
\begin{proof}
  % A corollary of \cref{lem:eval-derive-preserve-doe} and of a substitution lemma
  % relating substitution and denotational semantics: |eval (t) (x = eval s rho,
  % rho) = eval(t [x := s]) rho|.

  Assume |fromto Gamma rho1 (drhoa `doe` drhob) rho2|.

  Because |dsa| and |dsb| are change-equivalent we have
  % By definition of |dsa (doeIdx(s)) dsb| we have that
  % |eval dsa drho (doeIdx(eval s rho1)) (eval dsb drho)|.
  %
  % Because |`oplus`| respects validity also syntactically \pg{?}
  % we can show that |dsa, dsb| have destination |s `oplus` dsa|, that is
  \[|fromto sigma (eval s rho1) (eval dsa drho `doe` eval dsb drho) (eval (s
  `oplus` ds) rho1)|.\]

  Hence, we can construct change-equivalent environments for
  evaluating |derive t|, by combining |drho| and the values of
  respectively |dsa| and |dsb|:
  \begin{multline}
  |fromto (Gamma, x : sigma)
  ((rho1, x = eval s rho1))
  ((drho, x = eval s rho1, dx = eval dsa drho)
   `doe`
   (drho, x = eval s rho1, dx = eval dsb drho) ^^^)
   ((rho2, x = eval (s `oplus` dsa) rho1))|.
  \end{multline}
  This environment change equivalence is respected by |derive|, hence:
  \begin{multline}
    \label{eq:derive-preserve-doe-1}
  |fromto (Gamma -> tau)
    (eval t (rho1, x = eval s rho1))
    (eval (derive t) (drho, x = eval s rho1, dx = eval dsa drho)
     `doe`
     eval (derive t) (drho, x = eval s rho1, dx = eval dsb drho)^^^)
    (eval t (rho2, x = eval (s `oplus` dsa) rho1))|.
  \end{multline}
  We want to deduce the thesis by applying to this statement the substitution
  lemma for denotational semantics:
  |eval t (rho, x = eval s rho) = eval(t [x := s]) rho|.

  To be able to apply the substitution lemma for the substitution
  of |x| in next step, we must adjust \cref{eq:derive-preserve-doe-1}: using
  soundness of weakening and the fact that |drho| extends |rho1|,
  we replace some occurrences of |rho1| with bigger environments
  containing |drho|.
  We get:
  \begin{multline}
    \label{eq:derive-preserve-doe-2}
  |fromto (Gamma -> tau)
    (eval t (rho1, x = eval s rho1))
    (eval (derive t) (drho, x = eval s drho, dx = eval dsa (drho, x = eval s drho))
     `doe` ^^^
     eval (derive t) (drho, x = eval s drho, dx = eval dsb (drho, x = eval s drho))^^^)
    (eval t (rho2, x = eval (s `oplus` dsa) rho1))|.
  \end{multline}

  This equation can now be rewritten (by applying the
  substitution lemma twice) to the following one:

  \begin{multline}
    \label{eq:derive-preserve-doe-3}
  |fromto (Gamma -> tau)
    (eval (t [x := s]) rho1)
    (eval ((derive t)[dx := dsa][x := s]) drho
     `doe` ^^^
     eval ((derive t)[dx := dsb][x := s]) drho^^^)
    (eval t (rho2, x = eval (s `oplus` dsa) rho1))|.
  \end{multline}
  \pg{Nice, the environments don't match in the end :-)!}

\[|fromtosyn Gamma tau t ((derive t)[x := s, dx := dsa] `doe` (derive t)[x :=
s, dx := dsb]) t|.\]
\end{proof}
In this theorem, if |x| appears once in |t|, then |dx| appears once in |derive
t| (this follows by induction on |t|), hence |(derive t)[x := s, dx := param]|
produces a one-hole expression context.

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
Formalizing an object language including such facilities is highly nontrivial.

\subsection{Change equivalence is a PER}
\label{sec:doe-per}
Readers with relevant experience will recognize that this is a partial equivalence
relation (PER):
\begin{definition}[PER]
  \pg{add}
\end{definition}

\begin{lemma}[|`doe`| is a PER]
  \pg{write}
\end{lemma}

It is standard to use PERs to identify valid elements in a
model~\citep{Harper1992constructing}.
\pg{Any needed lemmas.}

Unlike ours, a typical PERs is defined
similarly to logical relations: two functions are related if they map related
inputs to related outputs. This helps showing that a PERs is a congruence.
Luckily, our PER is equivalent to a standard definition.

\begin{lemma}[Alternative definition for |`doe`|]
Change equivalence is equivalent to the following logical relation:
  \begin{code}
  fromto iota v1 (dva `doe` dvb) v2            `eqdef`
    fromto iota v1 dva v2 `and` fromto iota v1 dva v2
  fromto (sigma -> tau) f1 (dfa `doe` dfb) f2  `eqdef`
    forall (fromto sigma v1 (dva `doe` dvb) v2).
    fromto tau (f1 v1) (dfa v1 dva `doe` dfb v2 dvb) (f2 v2)
\end{code}
\end{lemma}


\section{Discussion}
In this section we discuss our proof and compare it with alternative proof
approaches.

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
(\cref{thm:derive-correct}) and the fundamental theorem of logical relations,
for the case of binary logical relations. This section is intended for logical
relation experts, and we keep it rather informal.

%format p(t) = "\mathcal{P}(" t ")"

Most studies of logical relations mention no term transformation that relates to
|derive(param)|; one exception is given by \citet{Bernardy2011realizability}.
They study relational parametricity, a particular binary logical relation, where
the fundamental theorem of logical relations becomes the abstraction theorem. To
prove the abstraction theorem, \citeauthor{Bernardy2011realizability} present a
term transformation |p(param)|; we'll show the analogy between this term
transformation and
|derive(param)|.%
%
\footnote{\citeauthor{Bernardy2011realizability} were not the first to introduce
  such a transformation, but we base our comparison off their presentation and
  avoid discussing their related work.}

Transformation |p(t)| takes a term |t| to a proof term |p(t)| in a suitable
object logic (related to the one of |t|), that proves that |t| maps logically
related inputs to logically related outputs. For binary logical relations and
simply-typed $\lambda$-calculus, we can specialize their definition to the
following:

%format (idx1 (t)) = "\mathcal{S}_1(" t ")"
%format (idx2 (t)) = "\mathcal{S}_2(" t ")"

\begin{code}
  (t1, t2) `elem` r(sigma -> tau) =
    forall x1 x2 : sigma, px : (x1, x2) `elem` r(sigma). (t1 x1, t2 x2) `elem` r(tau)
  p(x) =
      px
  p(\(x : sigma) -> t) =
    \(x1 x2 : sigma) (px : (x1, x2) `elem` r(sigma)) -> p(t)
  p(s t) =
    p(s) (idx1 s) (idx2 s) p(t)
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
% the fundamental theorem of logical relations, for readers familiar with these
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
\label{sec:non-termination}
\pg{write, and put somewhere}

\chapter{Syntactic correctness proofs for ILC}
We can also prove ILC correct without using denotational
semantics, but using only operational semantics and logical
relations.

This simplifies extending the proofs to more expressive languages
where a denotational semantics requires more sophistication. In
particular, using this approach we prove correctness of ILC for
pure untyped $\lambda$-calculus using an environment-based
call-by-value semantics. We present this development is this
chapter.

Compared to earlier chapters, this one will be more technical and
concise.

Also, using operational semantics, we can show more formally
whence function changes arise: we model function values as
closures and function change values as either closure changes
(which only modify environments) or replacement closures.

Our development is inspired significantly by
\citet{Ahmed2006stepindexed} and \citet*{Acar08}. We refer to
those works and to Ahmed's lectures at OPLSS
2013\footnote{\url{https://www.cs.uoregon.edu/research/summerschool/summer13/curriculum.html}}
for an introduction to (step-indexed) logical relations.

We can prove ILC correct using, in increasing order of complexity,
\begin{enumerate}
\item a typed language and standard syntactic logical relations;
\item a typed language and step-indexed logical relations;
\item an untyped language and step-indexed logical relations.
\end{enumerate}
We have fully mechanized the second proof, and done the others
manually.

For convenience, we consider a $\lambda$-calculus in a variant of
A-normal form.
We let meta-variable |t| range over arbitrary terms, |w| range
over neutral forms and |v| range over syntactic values (which are
always closed). Our environments are finite maps |rho| from
variables to syntactic values. The only form of syntactic values
we consider are closures |rho[\x -> t]|.
\pg{Add v ::= n production and fix sentence.}

%format `stoup` = "\mid"

%format n1
%format n2
%format w1
%format w2
%format dw1
%format dw2
%format rho' = rho "\myquote"
%format drho' = drho "\myquote"

% indexed big-step eval
%format ibseval (t) rho (n) v = rho "\vdash" t "\Downarrow_{" n "}" v
% without environments
%format ibseval' (t) (n) (v) = t "\Downarrow_{" n "}" v
% big-step eval
%format bseval  (t)  rho v = rho "\vdash" t "\Downarrow" v
% change big-step eval
%format dbseval (dt) rho drho dv = rho `stoup` drho "\vdash" dt "\Downarrow" dv

%format vn = "v_n"
%format dvn = dv "_n"
%format dxn = dx "_n"

%format (star rho (t)) = rho "^*(" t ")"
%format starv v = v "^*"

\begin{code}
  w ::= x | \x -> t
  t ::= w | w w | lett x = t in t
  v ::= rho[\x -> t]
  rho ::= x1 := v1 , ... , xn := vn
\end{code}

Next, we consider a separate language for change terms, which can
be transformed into the base language. This language supports
directly the structure of change terms.

%{
%format dwa = dw "_a"
%format dwb = dw "_b"

For instance, since a function change is applied to a base input
and a change for it at once, the syntax for change term has a
special binary application node |dw1 w dw2|; otherwise, in ANF,
such syntax must be encoded through separate applications via
|lett dwa = dw1 w in dwa dw2|.
Various other changes in the same spirit simplify similar
formalization and mechanization details.
%}
% In particular, values for
% function changes are again closures, but we require they bind
% two variables at the out

\begin{code}
  dw ::= dx | \x dx -> dt
  dt ::= dw | dw w dw | lett x = t; dx = dt in dt
  dv ::= rho `stoup` drho[\x dx -> dt]
  drho ::= dx1 := dv1 , ..., dxn := dvn
\end{code}
Differentiation maps constructs in the language of base terms
one-to-one to constructs in the language of change terms:
\begin{align*}
  |derive(x)| &= |dx| \\
  |derive(\(x : sigma) -> t)| &= |\(x : sigma) (dx : Dt^sigma) -> derive(t)| \\
  |derive(w1 w2)| &= |(derive w1) t (derive w2)| \\
  |derive(lett x = t1 in t2)| &= |lett x = t1; dx = derive t1 in derive t2|
\end{align*}
  %|derive(c)| &= |deriveConst(c)|

%format /-- = "\vdash_{\Delta}"

We define change types as before, but we modify the definition of
change contexts and environment changes to \emph{not} contain
entries for base values:
\begin{code}
  Dt^emptyCtx = emptyCtx
  Dt^(Gamma, x : tau) = Dt^Gamma, dx : Dt^tau
\end{code}

We can also define typing judgement for base terms and for change
terms. Typing for base terms is standard. For change terms, a
natural type system would only prove judgements with shape
|Gamma, Dt^Gamma /- dt : Dt^tau| (where |Gamma, Dt^Gamma| stands
for the concatenation of |Gamma| and |Dt^Gamma|).
To simplify inversion on such judgements (especially in Agda), we
write instead |Gamma /-- dt : tau|.

One can verify the following derived typing rule for |derive|:
\begin{typing}
  \Rule[T-Derive]
  {|Gamma /- t : tau|}
  {|Gamma /-- derive t : tau|}
\end{typing}
% if |Gamma /- t : tau| then |Gamma /-- derive
% t : tau|.

In our mechanization for typed ANF $\lambda$-calculus, we stick
in both cases to Church typing, hence only defining typing
derivations for typed terms.

\begin{typing}
\Rule[T-Var]
  {|x : tau `elem` Gamma|}
  {|Gamma /- x : tau|}

\Rule[T-App]
  {|Gamma /- w1 : sigma -> tau|\\
  |Gamma /- w2 : sigma|}
  {|Gamma /- w1 w2 : tau|}

\raisebox{0.5\baselineskip}{\fbox{|Gamma /- t : tau|}}

\Rule[T-Lam]
  {|Gamma , x : sigma /- t : tau|}
  {|Gamma /- \(x : sigma) -> t : sigma -> tau|}

\Rule[T-Let]
  {|Gamma /- t1 : sigma|\\
  |Gamma , x : sigma /- t2 : tau|}
  {|Gamma /- lett x = t1 in t2 : tau|}
\end{typing}

\begin{typing}
\Rule[T-DVar]
  {|x : tau `elem` Gamma|}
  {|Gamma /-- dx : tau|}

\raisebox{0.5\baselineskip}{\fbox{|Gamma /-- - dt : tau|}}

\Rule[T-DApp]
  {|Gamma /-- dw1 : sigma -> tau|\\
    |Gamma /- w2 : sigma|\\
    |Gamma /-- dw2 : sigma|}
  {|Gamma /- dw1 w2 dw2 : tau|}

\Rule[T-DLam]
  {|Gamma , x : sigma /-- dt : tau|}
  {|Gamma /-- \(x : sigma) (dt : Dt^sigma) -> dt : sigma -> tau|}

\Rule[T-DLet]{
  |Gamma /- t1 : sigma|\\
  |Gamma /-- dt1 : sigma|\\
  |Gamma , x : sigma /-- dt2 : tau|}
  {|Gamma /-- lett x = t1 ; dx = dt1 in dt2 : tau|}
\end{typing}
\pg{where?}%

Following \citet*{Acar08}, to define step-indexed logical relations
we consider a call-by-value big-step semantics, where derivations
are indexed by a step count, which counts in essence
$\beta$-reduction steps. Since our semantics uses environments,
$\beta$-reduction steps are implemented not via substitution but
via environment extension, but the resulting step-counts are the
same (\cref{sec:sanity-check-big-step}).
\begin{typing}
  \Rule[E-Var]{|rho(x) = v|}{|ibseval x rho 0 v|}

  \Axiom[E-Lam]{|ibseval (\x -> t) rho 0 (rho[\x -> t])|}

  \Rule[E-App]{|ibseval w1 rho 0 rho'[\x -> t]|\\|ibseval w2 rho 0 v2|\\|ibseval t (rho', x := v2) n v'|}{|ibseval (w1 w2) rho (1 + n) v'|}

  \Rule[E-Let]{|ibseval t1 rho n1 v1|\\|ibseval t2 (rho, x := v1) n2 v2|}{|ibseval (lett x = t1 in t2) rho (1 + n1 + n2) v2|}
\end{typing}
When we need to omit indexes, we write |bseval t rho v| to mean
that for some |n| we have |ibseval t rho n v|.

We can also define a straightforward non-indexed big-step
semantics for change terms.
\begin{typing}
  \Rule[E-DVar]{|drho(x) = v|}{|dbseval x rho drho v|}

  \Axiom[E-DLam]{|dbseval (\x dx -> dt) rho drho (rho `stoup` drho[\x dx -> dt])|}

  \Rule[E-DApp]{%
    |dbseval dw1 rho drho (rho' `stoup` drho'[\x dx -> dt])|\\
    |bseval  w2  rho v2|\\
    |dbseval dw2 rho drho dv2|\\
    |dbseval dt  (rho', x := v2) (drho', dx := dv2) dv'|}
  {|dbseval (dw1 w2 dw2) rho drho dv'|}

  \Rule[E-DLet]{
    |bseval  t1  rho v1|\\
    |dbseval dt1 rho drho dv1|\\
    |dbseval dt2 (rho, x := v1) (drho; dx := dv1) dv2|}
  {|dbseval (lett x = t1; dx = dt1 in dt2) rho drho dv2|}
\end{typing}

\section{Sanity-checking our semantics}
\label{sec:sanity-check-big-step}
In this section, we show how we ensure the step counts in our
semantics are set correctly, by relating our semantics first with
a big-step semantics based on substitution (rather than
environments) and then relating this alternative semantics to a
small-step semantics. Results in this section are useful to
understand better our semantics and as a design aide to modify
it, but are not necessary to the proof, so we have not mechanized
them.

In proofs using step-indexed logical relations, the use of
step-counts in definitions is often delicate and tricky to get
right.
But \citeauthor*{Acar08} provide a robust recipe to ensure
correct step-indexing in the semantics.
To be able to prove the fundamental lemma of logical relations,
we ensure step-counts agree with the ones induced by small-step
semantics (which counts $\beta$-reductions). Such a lemma is not
actually needed in other proofs, but only useful as a sanity
check.
We also attempted using the style of step-indexing
used by \citet{Amin2017}, but were unable to produce a proof. To
the best of our knowledge all proofs using step-indexed logical
relations, even with functional big-step semantics
\citep{Owens2016functional}, use step-indexing that agrees with
small-step semantics.

Unlike \citeauthor*{Acar08} we use environments in our big-step
semantics; this avoids the need to define substitution in our
mechanized proof. Nevertheless, one can show the two semantics
correspond to each other.
Our environments |rho| can be regarded as closed value
substitutions, as long as we also substitute away environments in values.
Formally,
we write |star rho t| for the ``homomorphic extension'' of
substitution |rho| to terms, which produces other terms.
If |v| is a value using environments, we write |w = starv v| for the
result of translating that value to not use environments; this
operation produces a closed neutral form |w|. Operations |star
rho t| and |starv v| can be defined in a mutually recursive way:
\begin{align*}
  |star rho x| &= |starv (rho(x))|\\
  |star rho (\x -> t)| &= |\x -> star rho t|\\
  |star rho (w1 w2)| &= |(star rho w1) (star rho w2)|\\
  |star rho (lett x = t1 in t2)| &= |lett x = star rho t1  in star rho t2|\\
  \\
  |starv (rho[\x -> t])| &= |\x -> star rho t|
\end{align*}
If |ibseval t rho n v| in our semantics,
a standard induction over the derivation of |ibseval t rho n v|
shows that |ibseval' (star rho t) n (starv v)|
%$|star rho t| \Downarrow_n |starv v|$
in a more conventional big-step
semantics using substitution rather than environments (also
following \citeauthor*{Acar08}):

\begin{typing}
  \Axiom[Var']{|ibseval' x 0 x|}

  \Axiom[Lam']{|ibseval' (\x -> t) 0 (\x -> t)|}

  \Rule[App']{
    |ibseval' (t[x := w2]) n w'|}
  {|ibseval' ((\x -> t) w2) (1 + n) w'|}

  \Rule[Let']{|ibseval' t1 n1 w1|\\
    |ibseval' (t2[x := w1]) n2 w2|}
  {|ibseval' (lett x = t1 in t2) (1 + n1 + n2) w2|}
\end{typing}
In this form, it is more apparent that the step indexes count
steps of $\beta$-reduction or substitution.

It's also easy to see that this big-step semantics agrees with a
standard small-step semantics $\mapsto$ (which we omit):
if |ibseval' t n w| then $|t| \mapsto^{n} |w|$.
Overall, the two statements can be composed, so our original
semantics agrees with small-step semantics:
if |ibseval t rho n v| then |ibseval' (star rho t) n (starv v)|
and finally
$|star rho t| \mapsto^{n} |starv v|$.
Hence, we can translate evaluation derivations using big-step
semantics to derivations using small-step semantics \emph{with
  the same step count}.

However, to state and prove the fundamental lemma we need not
prove that our semantics is sound relative to some other
semantics. We simply define the appropriate logical relation for
validity and show it agrees with a suitable definition for |`oplus`|.

Now that we defined our semantics, we proceed to define validity.
\section{Validity as a logical relations}
For simply-typed $\lambda$-calculus we can define logical
relations without using step-indexes, simply by using structural
recursion on types. We present the needed definitions as a
stepping stone to the definitions using step-indexed logical relations.

%format (valset (tau)) = "\mathcal{V}\left\llbracket" tau "\right\rrbracket"
%format (compset (tau)) = "\mathcal{C}\left\llbracket" tau "\right\rrbracket"
%format (envset (gamma)) = "\mathcal{G}\left\llbracket" gamma "\right\rrbracket"
Following \citet{Ahmed2006stepindexed} our validity logical
relation through two type-indexed families of relations.
Relation |valset tau| relates values |v1|, |dv| and |v2|
if |dv| is a valid change from |v1| to |v2| at type |tau|.
Relation |compset tau| relates tuples of environments and
computations,
|<rho1, t1>|, |<rho, drho, dt>| and |<rho2, t2>| if |dt| is a valid
change from |t1| and |t2|, considering the environments.
More precisely, if |t1| evaluates in environment |rho1| to |v1|,
and |t2| evaluates in environment |rho2| to |v2|, then
|dt| must evaluate in environments |rho| and |drho| to a change
value |dv|, with |v1, dv, v2| related by |valset tau|.
%
In this definition, the environments themselves need not be
related: this definition characterizes validity
\emph{extensionally}, that is, it allows unrelated
|t1|, |dt| and |t2| to have unrelated implementations.
We discuss a more intentional definition of validity in
\cref{sec:intentional-step-indexed-validity}.

In particular, for function types the relation |valset (sigma ->
tau)| relates function values |f1|, |df| and |f2| if they map
\emph{related input values} (and for |df| input changes) to
\emph{related output computations}.
\begin{figure}[h!]
\begin{align*}
  |valset Nat| ={}& \{|(n1, dn, n2) `such` n1, n2 `elem` Nat, dn
                     `elem` Int `and` n1 + dn = n2|\}\\
  |valset (sigma -> tau)| ={}&
                               \{|(rho1[\x -> t1], rho `stoup` drho[\x dx -> dt], rho2[\x -> t2]) `such` ^^^
                    ^&^ (forall ((v1, dv, v2) `elem` (valset sigma)). ^^^
                    ^&^ (<(rho1, x := v1), t1>, <(rho, x := v1) `stoup` (drho, dx := dv), dt>, ^^^
                    ^&^ <(rho2, x:= v2), t2>) `elem` (compset tau)) ^^ `and` ^^^
                    ^&^ (exists Gamma1 Gamma Gamma2 . ^^^
                    ^&^ Gamma1 , x : sigma /- t1 : tau ^^ `and` ^^^
                    ^&^ Gamma, x : sigma /-- dt : tau ^^ `and` ^^^
                    ^&^ Gamma2 , x : sigma /- t2 : tau)
                       |\}\\
  |compset tau| ={}&
                  \{|(<rho1, t1>, <rho , drho, dt>, <rho2, t2>) `such` ^^^
                    ^&^ ((bseval t1 rho1 v1) `and` (bseval t2 rho2 v2) => ^^^
                    ^&^ (dbseval dt rho drho dv) `and` (v1, dv, v2 `elem` valset tau)) ^^ `and` ^^^
                    ^&^ exists Gamma1 Gamma Gamma2 . ^^ (Gamma1 /- t1 : tau) ^^ `and` ^^ (Gamma /-- dt : tau) ^^ `and` ^^ (Gamma2 /- t2 : tau)
                       |\}\\
                  \\
  |envset emptyCtx| ={} & \{|(<emptyRho, emptyRho, emptyRho)>|\} \\
  |envset (Gamma, x : tau)| ={} &
                                  \{|<(rho1 , x := v1), (drho, dx := dv) , (rho2, x := v2)> `such` ^^^
                                  ^&^ <rho1, drho, rho2> `elem` envset Gamma `and` <v1, dv, v2> `elem` valset tau|\} \\
  |fromtosyn Gamma tau t1 dt t2| ={}&
                                      |forall ((<rho1, drho, rho2>) `elem` envset Gamma) . ^^^
                                      ^&^ (<rho1, t1>, <rho1, drho, dt>, <rho2, t2>) `elem` compset tau|
\end{align*}
\caption{Defining validity logical relations using big-step semantics.}
\label{fig:big-step-validity-ext-nosi}
\end{figure}
\pg{environments, semantic entailment and fundamental lemma.}

Given these definitions, one can prove the fundamental lemma.
\begin{theorem}[Fundamental lemma]
  For every well-typed term |Gamma /- t : tau| we have that
  |fromtosyn Gamma tau t (derive t) t|.
\end{theorem}
\begin{proof}
  By induction on the structure on terms, using ideas similar to
  \cref{thm:derive-correct}.
\end{proof}
\section{Step-indexed logical relations}
Step-indexed logical relations define approximations to a
relation, to enable dealing with non-terminating programs.
Logical relations relate the behavior of multiple terms during
evaluation; with step-indexed logical relations, we can take a
bound $k$ and restrict attention to evaluations that take at most
$k$ steps. For instance, if we define equivalence as a
step-indexed logical relation, we can say that two terms are
equivalent for $k$ or fewer steps, even if they might have
different behavior with more steps available.
In our case, we can say that a change appears valid at
step count $k$ if it behaves like a valid change in observations using
at most $k$ steps.

% Instead of observing the behavior of terms with an unbounded
% number of computation steps, as we did before, we observe the
% behavior of terms having a bounded
% we give a bound $k$, and observe
% behavior with at most $k$

First, we index the relation by both types and step-indexes,
since this is the one we use in our mechanized proof. This
relation is defined by structural induction on types.
For untyped $\lambda$-calculus, instead, we'll need to drop
types. The resulting definition is instead defined by
well-founded recursion on step-indexes.

\begin{align*}
  |valset Nat| ={}& \{|(k, n1, dn, n2) `such` n1, n2 `elem` Nat, dn
                     `elem` Int `and` n1 + dn = n2|\}\\
  |valset (sigma -> tau)| ={}&
                               \{|(k, rho1[\x -> t1], rho `stoup` drho[\x dx -> dt], rho2[\x -> t2])`such`| \\
                  & |forall ((v1, dv, v2) `elem` (valset sigma)). ^^^
                    ^&^ forall j. ^^ j < k => ^^^
                       ^&^ (j, <(rho1, x := v1), t1>, <(rho, x := v1) `stoup` (drho, dx := dv), dt>, <(rho2, x:= v2), t2>) `elem` (compset tau)|\}\\
  |compset tau| ={}&
                  \{|(k, <rho1, t1>, <rho `stoup` drho, dt>, <rho2, t2>) `such` ^^^
                     ^&^ forall j . ^^ j < k `and` ^^^
                        ^&^ (ibseval t1 rho1 k v1) `and` (bseval t2 rho2 v2) => ^^^
                           ^&^ (dbseval dt rho1 drho dv) `and` (k - j , v1, dv, v2 `elem` valset tau)|\}
\end{align*}

Unlike \citeauthor{Ahmed2006stepindexed} we use only Church
typing and do not formalize untyped terms, so we require that all
terms are well-typed as expected.

At this moment, we do not require that related closures contain
related environments: we are defining validity only based on
extensional behavior.

\section{An intentional characterization of valid function changes}
\label{sec:intentional-step-indexed-validity}

Up to now, we have defined when a function change is valid purely
based on its behavior, like we have done earlier when using
denotational semantics.
We expect it should still be possible to define |`oplus`| and
prove it agrees with validity. However, we do not do so.

To ensure that |f1 `oplus` df = f2| (for a suitable |`oplus`|) we
choose to require that closures |f1|, |df| and |f2| close over
environments of matching shapes.
\pg{Continue here.}

\begin{align*}
  |valset Nat| ={}& \{|(n1, dn, n2) `such` n1, n2 `elem` Nat, dn
                     `elem` Int `and` n1 + dn = n2|\}\\
  |valset (sigma -> tau)| ={}&
                               \{|(rho1[\x -> t1], rho `stoup` drho[\x dx -> dt], rho2[\x -> t2]) `such`| \\
  & |exists Gamma . ^^ Gamma, x : sigma /- t1 : tau `and` Dt^(Gamma, x : sigma) /- dt : Dt^tau `and` Gamma, x : sigma /- t2 : tau `and`|\\
                            & |forall ((v1, dv, v2) `elem` (valset sigma)). ^^^
                            ^&^ (<(rho1, x := v1), t1>, <(rho, x := v1) (drho, dx := dv), dt>, <(rho2, x:= v2), t2>) `elem` (compset tau)|\}\\
  |compset tau| ={}&
                  \{|(<rho1, t1>, <rho , drho, dt>, <rho2, t2>) `such` ^^^
                  ^&^ (bseval t1 rho1 v1) `and` (bseval t2 rho2 v2) => ^^^
                  ^&^ (dbseval dt rho drho dv) `and` (v1, dv, v2 `elem` valset tau)|\}
\end{align*}

\begin{align*}
  |valset Nat| ={}& \{|(k, n1, dn, n2) `such` n1, n2 `elem` Nat, dn
                     `elem` Int `and` n1 + dn = n2|\}\\
  |valset (sigma -> tau)| ={}&
                               \{|(k, rho1[\x -> t1], drho[\x dx -> dt], rho2[\x -> t2])`such`| \\
  & |exists Gamma . ^^ Gamma, x : sigma /- t1 : tau `and` Dt^(Gamma, x : sigma) /- dt : Dt^tau `and` Gamma, x : sigma /- t2 : tau `and`|\\
                  & |forall ((v1, dv, v2) `elem` (valset sigma)). ^^^
                    ^&^ forall j. ^^ j < k => ^^^
                       ^&^ (j, <(rho1, x := v1), t1>, <(drho, dx := dv), dt>, <(rho2, x:= v2), t2>) `elem` (compset tau)|\}\\
  |compset tau| ={}&
                  \{|(k, <rho1, t1>, <drho, dt>, <rho2, t2>) `such` ^^^
                     ^&^ forall j . ^^ j < k `and` ^^^
                        ^&^ (ibseval t1 rho1 k v1) `and` (bseval t2 rho2 v2) => ^^^
                           ^&^ (dbseval dt rho1 drho dv) `and` (k - j , v1, dv, v2 `elem` valset tau)|\}
\end{align*}
