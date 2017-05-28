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
\section{A change structure for products}
\label{sec:chs-product}
We can define change structures on products |A `times` B|, given
change structures on |A| and |B|: a change on pairs is just a
pair of changes; all other change structure definitions
distribute componentwise the same way, and their correctness
reduce to the correctness on components. Since all these proofs
are similar, spelling out their details does not make them
clearer, we only give the first such proof in full.

\begin{definition}[Change structure for |A `times` B|]
  \label{def:chs-prod}
  Given change structures |chs(A)| and |chs(B)| we define a
  change structure on their product |chs(A `times` B)|, that we
  also write |chs(A) `times` chs(B)|.
  \begin{subdefinition}
  \item The change set is defined as: |Dt^(A `times` B) = Dt^A `times` Dt^B|.
  \item Validity is defined as
    \begin{multline*}
      |fromto (A `times` B) ((a1, b1)) ((da, db)) ((a2, b2)) =| \\
      |(fromto A a1 da a2)| \text{ and } |(fromto B b1 db b2)|.
    \end{multline*}
    %
    In other words, validity distributes componentwise: a product change
    is valid if each component is valid.
  \item We define change update by
    \[|(a1, b1) `oplus` (da , db) = (a1 `oplus` da, b1 `oplus` db)|.\]
  \item |`oplus`| agrees with validity on |A `times` B| because
    |`oplus`| agrees with validity on both |A| and |B|. For this
    property we give a full proof.

    For each |p1 , p2: A `times` B|
    and |fromto (A `times` B) p1 dp p2|, we must show that |p1
    `oplus` dp = p2|. Instead of quantifying over pairs |p : A
    `times` B|, we can quantify equivalently over components |a :
    A, b : B|.
    Hence, consider |a1, a2: A|, |b1, b2: B|, and changes |da,
    db| that are valid, that is, |fromto A a1 da a2| and |fromto
    B b1 db b2|: We must show that \[|(a1, b1) `oplus` (da, db) =
    (a2, b2)|.\] That follows from |a1 `oplus` da = a2| (which
    follows from |fromto A a1 da a2|) and |b1 `oplus` db = b2|
    (which follows from |fromto B b1 db b2|).
  \item We define difference by
    \[|(a2, b2) `ominus` (a1, b1) = (a2 `ominus` a1, b2 `ominus` b1)|.\]
  \item |`ominus`| produces valid changes on |A `times` B|
    because |`ominus`| produces valid changes on both |A| and
    |B|. We omit a full proof; the key step reduces the thesis
    \[|fromto (A `times` B) ((a1, b1)) ((a2, b2) `ominus` (a1, b1))
    ((a2, b2))|\] to |fromto A a1 (a2 `ominus` a1) a2| and |fromto
    B b1 (b2 `ominus` b1) b2| (where free variables range on
    suitable domains).
  \item We define |nilc| to distribute componentwise:
    \[|nil (a, b) = (nil a, nil b)|.\]
  \item |nil (a, b)| is correct, that is |fromto (A `times` B)
    ((a, b)) ((nil a, nil b)) ((a, b))|, because |nilc| is
    correct on each component.
  \item We define change composition to distribute componentwise:
    \[|ocompose ((da1, db1)) ((da2, db2)) =
    (ocompose da1 da2, ocompose db1 db2)|.\]
  \item Change composition is correct on |A `times` B|, that is
    \[|fromto (A `times` B) ((a1, b1)) ((ocompose da1 da2,
      ocompose db1 db2)) ((a3, b3))|\] whenever |fromto (A `times` B)
    ((a1, b1)) ((da1, db1)) ((a2, b2))| and |fromto (A `times` B)
    ((a2, b2)) ((da2, db2)) ((a3, b3))|, in essence because
    change composition is correct on both |A| and |B|. We leave a
    full proof as an exercise.
  \end{subdefinition}
\end{definition}

\section{A change structure for sums}
\label{sec:chs-sums}
We can define change structures on disjoint sums |A + B|, given
change structures on |A| and |B|.
\pg{resume.}


\section{A change structure for groups}
\label{sec:change-structure-groups}

To define aggregation, we will need to use a change structure on
groups.
\begin{definition}[Change structure on groups |G|]
\label{def:chs-group}
Given any group |(G, e, +, -)| we can define a change structure
|chs(G)| on carrier set |G| as follows.
\begin{subdefinition}
\item The change set is |G|.
\item Validity is defined as |fromto G g1 dg g2| if and only if
  |g2 = g1 + dg|.
\item Change update coincides with |+|: |g1 `oplus` dg = g1 +
  dg|. Hence |`oplus`| agrees \emph{perfectly} with validity: for all |g1
  `elem` G|, all
  changes |dg| are valid from |g1| to |g1 `oplus` dg| (that is
  |fromto G g1 dg (g1 `oplus` dg)|).
\item We define difference as |g2 `ominus` g1 = (- g1) + g2|.
  Verifying |fromto G g1 (g2 `ominus` g1) g2| reduces to
  verifying |g1 + ((- g1) + g2) = g2|, which follows from group axioms.
\item The only nil change is the identity element: |nil g = e|.
  Validity |fromto G g (nil g) g| reduces to |g + e = g| which
  follows from group axioms.
\item Change composition also coincides with |+|: |ocompose dg1
  dg2 = dg1 + dg2|. Let's prove that composition respects
  validity. Our hypothesis is |fromto G g1 dg1 g2| and |fromto G
  g2 dg2 g3|.
  Because |`oplus`| agrees perfectly with validity, the
  hypothesis is equivalent to |g2 = g1 `oplus` dg1| and
  \[|g3 = g2 `oplus` dg2 = (g1 `oplus` dg1) `oplus` dg2|.\]
  Our thesis is |fromto G g1 (dg1 `ocompose` dg2) g3|, that is
  \[|g3 = g1 `oplus` (dg1 `ocompose` dg2)|.\]
  Hence the thesis reduces to
  \[|(g1 `oplus` dg1) `oplus` dg2 = g1 `oplus` (dg1 `ocompose` dg2)|,\]
  hence to |g1 + (dg1 + dg2) = (g1 + dg1) + dg2|, which is just
  the associative law for group |G|.
\end{subdefinition}
\end{definition}

% Missing sections from chap-intro-incr.lhs.

\chapter{Misc}

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
