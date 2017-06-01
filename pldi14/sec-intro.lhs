% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Discussing changes syntactically}
To define derivatives of primitives, we will often discuss
changes directly on programs.
We'll need language to say that term |dt| is a change from term
|t1| to term |t2|, or to term |t1 `oplus` dt|, that |dx| is a
change from |x| to |x `oplus` dx|, and so on. In such a
statement, we evaluate |t1| and |t2| in \emph{the same} environment.

But currently we lack the language to do so. We can use the
change structure on |eval Gamma -> eval tau|, and write |fromto
() t1 dt t2|.\pg{How to write Gamma, tau there?}
But in such a statement means that for all

\pg{notation?}
\begin{definition}[Syntactic validity]
  \label{def:syntactic-validity}
  |fromto (Gamma, tau) t1 dt t2|
  |fromtosyn Gamma tau t1 dt t2|.
  %|fromtosyn Gamma tau t1 dt t2 = forall (fromto Gamma rho1 drho rho2). fromto tau (eval t1 rho1) (eval dt drho) (eval t2 rho1)|.
\end{definition}

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
\pg{We can use based changes. Better not.}

To enable optimizations on programs manipulating changes,
we next define an equivalence relation on changes called
\emph{change equivalence}. When it is clear we talk about
changes, we will just talk about equivalence.

Change equivalence is defined in terms of validity so that
validity-preserving operations preserve change equivalence: If
two changes |dv1, dv2| are change-equivalent, one can be
substituted for the other in a validity-preserving context.

\begin{definition}[Change equivalence]
  Two changes |dv1|, |dv2| are equivalent, relative to source
  |v1|, if and only if there exists |v2| such that both |dv1| and
  |dv2| are valid from |v1| to |v2| (that is |fromto V v1 dv1
  v2|, |fromto V v1 dv2 v2|).
  We write then |fromto V v1 (dv1 `doe` dv2) v2|, or simply |dv1
  (doeIdx(v1) dv2|, or just |dv1 `doe` dv2| when the source |v1| is
  clear from context.
\end{definition}

Two changes are often equivalent relative to a source but not
others. Hence |dv1 `doe` dv2| is always an abbreviation for
change equivalence at a specific source.
For instance, we later use a change structure for integers using
both replacement changes and differences (\cref{ex:replacement}).
In this structure, change |0| is nil for all numbers, while
change |!5| (``bang 5'') replaces any number with 5. Hence,
changes |0| and |!5| are equivalent only relative to source 5,
and we write |0 doeIdx(5) !5|.

\paragraph{Change equivalence is an equivalence}
By applying definitions, one can verify that change equivalence
relative to a source is a symmetric and transitive relation.
However, it is only reflexive on valid changes.
\begin{lemma}[Change equivalence is an equivalence relation.]
  For each set |V| and source |v `elem` V|, change equivalence
  relative to source |v| is an equivalence relation over the sets
  of changes |dv `elem` Dt^V| that are valid with source |v|.
\end{lemma}
Readers with the relevant expertise should recognize that change
equivalence is a partial equivalence relation (PER).

\paragraph{Preserving change equivalence}
Change equivalence is respected by all validity-preserving
operations. We state few lemmas as examples.

\begin{lemma}[Valid function changes respect change equivalence]
Any valid function change |fromto (A -> B) f1 df f2| respect
change equivalence: if |fromto A v1 (dv1 `doe` dv2) v2| then
|fromto B (f1 v1) (df v1 dv1 `doe` df v1 dv2) (f2 v2)|.
\end{lemma}
\begin{proof}
  To prove this, simply show that both |df v1 dv1| and |df v1
  dv2| have the expected source and destination because of |df|'s
  validity.
\end{proof}
This lemma holds because the source and destination of |df v1 dv|
don't depend on |dv|, only on its source and destination. Source
and destination are shared by equivalent changes. Hence,
validity-preserving functions map equivalent changes to
equivalent changes.

Change equivalence can be extended to terms.
\begin{definition}[Term change equivalence]
Two change terms |Dt^Gamma /- dt1 : Dt^tau|, |Dt^Gamma /- dt2 :
Dt^tau| are change equivalent, relative to source |Gamma /- t :
tau|, if for all |fromto Gamma rho1 drho rho2| we have that |eval
dt1 drho (doeIdx(eval t rho1)) (eval dt2 drho)|. We write then |dt1
(doeIdx t) dt2| or simply |dt1 `doe` dt2|.
%|fromto tau v1 (dv1 `doe` dv2) v2|,
\end{definition}
The equivalence of |dt1| and |dt2| relative to |t| does not
require that the destination is again |t|.
\pg{Use \cref{def:syntactic-validity} to also state the destination.}
\pg{Introduce this earlier}

If two change terms are change equivalent with respect to the
right source, we can replace one for the other to optimize a
program, as long as the program context is validity-preserving.

% Since differentiation produces valid changes, 
% Differentiation produces validity-preserving operations.
\begin{lemma}[|derive(param)| preserves change equivalence]
For any term |Gamma /- t : tau|, |derive(t)| preserves change
equivalence: |derive(t) `doe` derive(t)|, that is |fromto (Gamma
-> tau) (eval t) (eval (derive t) `doe` eval (derive t)) (eval
t)|, that is, for all |fromto Gamma rho1 drho rho2| we have
|fromto (Gamma -> tau) (eval t rho1) (eval dt1 drho `doe` eval
dt2 drho) (eval t rho2)|.
\end{lemma}

There are further operations that preserve validity. To represent
terms with ``holes'' where other terms can be inserted, 
we can define \emph{one-level contexts} |F|, and contexts |E|, as
is commonly done:
\begin{code}
  F ::= [] t dt | ds t [] | \x dx -> [] | t `oplus` [] | dt1 `ocompose` [] | [] `ocompose` dt2
  E ::= [] | F[E]
\end{code}
If |fromto tau t1 (dt1 `doe` dt2) t2| and our context |E|
preserves changes from |t1| to |t2| then |F[dt1]| and |F[dt2]|
are change equivalent. It is easy to prove such lemmas for each
possible shape of one-level context |F|. For instance \pg{resume}.

% or more concisely
% |fromto (Gamma -> tau) (eval t) (eval dt1 `doe` eval dt2) (eval t)|.

  % E ::= [] | E v dv | df v E | \v dv -> E | v `oplus` E | dv1
  % `ocompose` E | E `ocompose` dv2

% such as valid function changes |df|. We only state
% here one relevant lemma.

% That's because
% validity-respecting operations
% This follows
% because of how validity preservation is defined:

% And conversely, two function changes that map equivalent sources
% to equivalent destinations are also equivalent.

Earlier (say, in \cref{ssec:pointwise-changes}) we have sometimes
written that two changes are equal. However, that's often too
restrictive.

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

\section{Nontermination}
\label{sec:non-termination}
\pg{write, and put somewhere}
