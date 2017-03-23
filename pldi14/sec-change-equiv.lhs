% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Change equivalence}

\section{Change equivalence}
\label{sec:changeeeq}
Next, we formalize when two changes are ``equivalent'', so we
know when we can replace a change by another without affecting
the result of the program. We could simply replace changes by
equal changes, but that would not enable sufficient
optimizations. For instance, if change |dv| is valid for |v|, it
is not necessarily equal to the difference |(v `oplus` dv)
`ominus` v|, but the two changes are always going to be
equivalent, even though the definition of change structure has no
such explicit requirement.

We could demand that |(v `oplus` dv) `ominus` v| be instead
\emph{equal} to |dv|. On naturals and on bags, this would be
true. But there are sensible examples of change structures where
|dv| and |(v `oplus` dv) `ominus` dv| are different changes, even
though both go from |v| to |v `oplus` dv|.

In fact, we can have multiple changes between the same source and target. For
instance, we can go from list |['a', 'b', 'c']| to list |['a', 'b', 'd']| by
first removing |'c'| and then adding |'d'|, hence through change |[Remove 2,
Insert 2 'd']|, or by inserting |'d'| and removing |'c'| through either of
|[Insert 3 'd', Remove 2]| or by |[Insert 2 'd', Remove 3]|.
We can also remove and readd all elements.

Therefore, we define an
equivalence among such changes that we call \emph{change
  equivalence}. When it is clear we are talking about changes, we
will also say that two changes are equivalent to mean that they
are change-equivalent. The definition of change equivalence is as
follows:

\begin{definition}[Change equivalence]
  Given a change structure $\chs V$, a value |v `elem` V|,
  and two changes |dv1, dv2| having |v| as source
  (|dv1, dv2 `elem` Dt ^ v|), we say that |dv1|
  is change-equivalent (or just equivalent) to |dv2|
  (written |dv1 `doe` dv2|) if and only if these changes share,
  beyond the source |v|, also their target, that is, if and only
  if |v `oplus` dv1 = v `oplus` dv2|.
\end{definition}

\begin{lemma}
  \label{def:diff-update-lemma}
  We have |(v `oplus` dv) `ominus` v `doe` dv| for any change
  structure $\chs V = |(V, Dt, `oplus`, `ominus`)|$, base value
  |v `elem` V| and change |dv| valid for |v| (that is, |dv `elem`
  Dt^v|).
\end{lemma}
\begin{optionalproof}
Since both sides are changes for |v|, the thesis is equivalent to |v `oplus` ((v
`oplus` dv) `ominus` v) = v `oplus` dv|.

To prove our thesis, we remember that thanks to \cref{def:update-diff},
for any |v1, v2 `elem` V| we have |v1 `oplus` (v2 `ominus` v1) = v2|. We can take |v1
= v|, |v2 = v `oplus` dv| and obtain |v `oplus` ((v `oplus` dv) `ominus` v) = v
`oplus` dv|, which is exactly our thesis.
\end{optionalproof}

With change equivalence we can generalize some rules from high
school algebra. There, we learn to add or subtract members from
both sides of an equation: if and only if |a = b| then |a + c = b
+ c| and |a - c = b - c|, so that |a + b = c| is equivalent to |a
= c - b|. Similarly we have:

\begin{lemma}[Equivalence cancellation]
  \label{thm:equiv-cancel}
  |v2 `ominus` v1 `doe` dv| holds if and only if |v2 = v1 `oplus`
  dv|, for any |v1, v2 `elem` V| and |dv `elem` Dt ^ v1|.
\end{lemma}
\begin{optionalproof}
  We prove both sides of the equivalence separately.
  First, if |v2 `ominus` v1 `doe` dv|, by definition |v1 `oplus` (v2
  `ominus` v1) = v1 `oplus` dv|, and canceling on the left side
  we get |v2 = v1 `oplus` dv| as desired.

  Second, if |v2 = v1 `oplus` dv|, then |v2 `ominus` v1 = (v1
  `oplus` dv) `ominus` v1 `doe` dv| (using change cancellation in
  the last step) as desired.
\end{optionalproof}

Change equivalence is indeed an equivalence relation, as stated
in the following lemma:
\begin{lemma}[Change equivalence is indeed an equivalence relation]
  For any change structure $\chs V$ and for any base value |v
  `elem` V|, change equivalence is an equivalence relation
  (reflexive, symmetric, transitive) among elements of |Dt v|.
\end{lemma}
\begin{optionalproof}
  The proofs apply the definition of change equality reduces each property to
  the same property for equality.

  Change equivalence is reflexive: |dv `doe` dv| for any |dv `elem` Dt ^ v|,
  because by reflexivity of equality |v `oplus` dv = v `oplus` dv|.

  Change equivalence is also symmetric: |dv2 `doe` dv1| iff |dv1 `doe` dv2|,
  because by symmetry of equality |v `oplus` dv2 = v `oplus` dv1| iff |v `oplus`
  dv1 = v `oplus` dv2|.

  Finally, change equivalence is transitive: |dv1 `doe` dv2| and |dv2 `doe` dv3|
  imply |dv1 `doe` dv3|, because by transitivity of equality |v `oplus` dv1 = v
  `oplus` dv2| and |v `oplus` dv2 = v `oplus` dv3| imply |v `oplus` dv1 = v
  `oplus` dv3|.
\end{optionalproof}

\begin{lemma}
  \label{thm:nil-equivs}
  Nil changes are equivalent to each other, that is, |v `oplus` dv = v| implies
  |dv `doe` nil v|, for any change structure $\chs V$ and value |v `elem` V|.
\end{lemma}
\begin{optionalproof}
  All nil changes for |v| share the same source and destination |v|, so they're
  equivalent.
\end{optionalproof}

As we will see, each valid operations in our theory (such as
derivatives) will respect change equivalence: equivalent changes
will be mapped to equivalent changes or to equal values. See in
particular \cref{thm:deriv-respect-doe,thm:change-respect-doe}.

\paragraph{Why not quotient change sets}%
\pg{Explain why we don't just take a quotient. We need to explain
  earlier what our metatheory's foundation is. Move the footnote
  on HoTT here.}

Instead of working explicitly with change sets and change equivalence, we could quotient change sets by change equivalence. \pg{In fact, here we work using setoids.} Then, whenever we define an operation on changes, we would be forced to show it respects change equivalence; here we need to state this as an additional result.
We avoid quotienting for a few reasons:
\begin{itemize}
\item The theory of changes is mechanized in Agda, which is based
  in intentional Martin-Löf type theory that does not provide
  quotient types, only setoids (essentially, what we are using),
  even though we usually hide this aspect. We could use variants
  of type theory which support quotient types (among others,
  observational type theory and homotopy type theory), but we
  decided to stick to standard type theory constructions; among
  other reasons, some formalization techniques we use (such as
  typed deBrujin indexes) do not work.%
  \pg{Revise when we describe our mechanization earlier.}
\item The goal of our theory is to support reasoning on programs,
  and in programs we do not have the option of working concretely
  with quotient types.
\item Processing two equivalent changes can have different
  performance. Take again the example above: we can go from a
  base list |v1 = ['a', 'b', 'c']| to another list |v2 = ['a',
  'b', 'd']| by a change |dv1| that just removes element |'c'|
  and adds element |'d'|, or by a change |dv2| that removes all
  elements of |v1| and then adds all elements of |v2|.
  Derivatives processing changes |dv1| or |dv2| are guaranteed to
  produce equivalent results, but inspecting |dv1| is faster than
  inspecting |dv2|, so we expect that also processing |dv1| will
  be faster than processing |dv2|.
\end{itemize}

\section{Derivatives}

Using change equivalence we immediately obtain an alternative characterization of derivatives:

\begin{lemma}[Characterization of derivatives up to change equivalence]
  \label{lem:derivatives-up-to-doe}
  A derivative |df| of function |f `elem` A -> B| can be characterized (up to
  change equivalence) by |df a da `doe` f (a `oplus` da) `ominus` f a|.
\end{lemma}
\begin{optionalproof}
  Since |df v dv| is a change for |f v|, inlining the definition of change
  equivalence in the thesis gives
  \[|f a `oplus` df a da = f a `oplus` (f (a `oplus` da) `ominus` f a)|\] Once
  we simplify the right-hand side via \cref{def:update-diff}, we're left with
  \[|f a `oplus` df a da = f (a `oplus` da)|\]
  which is the defining property of derivatives.\qed
\end{optionalproof}

It also follows that a function, in general, can have different
derivatives. Later, in \cref{thm:deriv-unique}, we show all
derivatives of the same function are ``equivalent'' in some
sense.
%
Take a function |f `elem` A -> B|, with a derivative |df1|, base
input |a `elem` A| and change |da `elem` Dt ^ a|. Let |db1| be
the result of |df1 a da|. Now |db1| is only specified up to
change equivalence, so if there is a |db2| different but
equivalent from |db1| (|db2 `doe` db1|, |db2 /= db1|), then we
can define a different derivative |df2| of |f| that is equal to
|df1| everywhere except that |df2 a da = db2|. Hence these two
derivatives are different.

We immediately verify that derivatives respect change equivalence, as promised
earlier in \cref{sec:changeeeq}:

\begin{lemma}[Derivatives respect change equivalence]
  \label{thm:deriv-respect-doe}
  A derivative |df| of function |f `elem` A -> B| always respects change
  equivalence, that is, if |dv1 `doe` dv2|, then |df v dv1 `doe` df v dv2|, for
  any value |v `elem` A|, change structure $\chs A$ and changes |dv1, dv2 `elem`
  Dt v|.
\end{lemma}
\begin{optionalproof}
  By hypothesis changes |dv1| and |dv2| are equivalent, that is |v `oplus` dv1 = v `oplus` dv2|. We
  prove the thesis directly by equational reasoning using \cref{lem:derivatives-up-to-doe}:
  \[|df v dv1 `doe` f (v `oplus` dv1) `ominus` f v = f (v `oplus` dv2) `ominus`
    f v `doe` df v dv2|\text{.}\qed\]
\end{optionalproof}

%
Next we can prove that derivatives take nil changes to nil
changes, \emph{up to change equivalence}. This lemma allows to
skip calling a derivative on a nil change, and produce a nil
change directly; this is an important optimization.\pg{revise and find back
  pointers to this from later.}

\begin{lemma}[Derivatives take nil changes to nil changes]
  \label{thm:deriv-nil}
  Applying a derivative to a value and its nil change gives a nil change, up to
  change equivalence; formally, we have |df a (nil a) `doe` (nil(f a))| for any
  change structures $\chs A$ and $\chs B$, function |f `elem` A -> B|, value |a
  `elem` A|, and |df| derivative of |f|.
\end{lemma}
\begin{optionalproof}
  We prove the thesis |df a (nil a) `doe` (nil(f a))| equationally:
\begin{equational}
\begin{code}
      df a (nil a)
`doe` {- by the definition of derivatives (\cref{def:derivatives}) -}
      f (a `oplus` nil a) `ominus` f a
=     {- because |nil(a)| is a nil change (\cref{thm:update-nil-v2}) -}
      f a `ominus` f a
=     {- by the definition of nil changes (\cref{def:nil-change-v2}) -}
      nil (f a)
\end{code}
\end{equational}
\end{optionalproof}

We explained earlier that derivatives of a function can be
different because they can return different but equivalent
changes on some inputs; as promised, we now show that all
derivatives of a function are change-equivalent.
\begin{lemma}[Derivatives are unique up to change equivalence]
  \label{thm:deriv-unique}
  If two function changes |df1, df2| are derivatives for
  |f|, then they're change equivalence to each other and to |f|'s nil change:
  |df1 `doe` nil f `doe` df2|, for
  any change structures $\chs A, \chs B$ and base function |f
  `elem` A -> B|.
\end{lemma}
\begin{optionalproof}
  Derivatives |df1| and |df2| are nil changes (as just shown in
  \cref{thm:derivative-is-nil}). Change |nil f| is also a
  nil change (by \cref{thm:update-nil-v2}). Nil changes are all
  change equivalent (by \cref{thm:nil-equivs}), that is, we have
  the thesis |df1 `doe` nil f `doe` df2|.
\end{optionalproof}


\subsection{Function changes and change equivalence}

\pg{Revise}
We claimed earlier that change equivalence is
respected by all valid operations in our theory. Here we prove
that all function changes do preserve this equivalence.

\begin{lemma}[Function change application preserves change equivalence]
  \label{thm:change-respect-doe}
  If |df1 `doe` df2| and |dv1 `doe` dv2| then |df1 v dv1 `doe`
  df2 v dv2|, for any change structures $\chs A$ and $\chs B$,
  base value |a `elem` A|, function |f `elem` A -> B|, changes
  |da1, da2 `elem` Dt ^ a| and |df1, df2 `elem` Dt ^ f|.
\end{lemma}
\begin{optionalproof}
  By definition of change equivalence, the thesis |df1 v dv1
  `doe` df2 v dv2| means that |f v `oplus` df1 v dv1 = f v
  `oplus` df2 v dv2|.
  We prove this statement by equational reasoning:
\begin{equational}
\begin{code}
   f v `oplus` df1 v dv1
=  {- by incrementalization (\cref{thm:incrementalization}) -}
   (f `oplus` df1) (v `oplus` dv1)
=  {- since |df1 `doe` df2| and |dv1 `doe` dv2| -}
   (f `oplus` df2) (v `oplus` dv2)
=  {- by incrementalization (\cref{thm:incrementalization}) -}
   f v `oplus` df2 v dv2
\end{code}
\end{equational}
\end{optionalproof}
This lemma generalizes \cref{thm:deriv-respect-doe}.

We can prove a form of extensionality for function changes:
function changes are equal if they produce change-equivalent
changes on allowed inputs.
\begin{lemma}[Extensionality for change equivalence]
  For any change structures $\chs A, \chs B$ and base function |f
  `elem` A -> B|, two function changes |df1, df2 `elem` Dt ^ f|
  are equivalent (|df1 `doe` df2|) if they behave equivalently when
  applied to arbitrary inputs |a `elem` A|, |da1, da2 `elem` Dt ^
  x| (|df1 a da1 `doe` df2 a da2|)
\end{lemma}
\begin{optionalproof}
  The thesis |df1 `doe` df2| means that |f `oplus` df1| is equal
  to |f `oplus` df2|. We prove this using function
  extensionality.
  %
  Let |a `elem` A| be an arbitrary input, and let us prove that
  |(f `oplus` df1) a| is equal to |(f `oplus` df2) a|.
  %
  First, we apply the hypothesis with |da1 = da2 = (nil a)|
  (since change equivalence is reflexive), and obtain that |df1 a
  (nil a) `doe` df2 a (nil a)|, that is |f a `oplus` df1 a (nil
  a) = f a `oplus` df2 a (nil a)|.
  Now we can prove the thesis by equational reasoning:
\begin{equational}
\begin{code}
   (f `oplus` df1) a
=  {- by the definition of |`oplus`| on functions (\cref{def:function-changes:update}) -}
   f a `oplus` df1 a (nil a)
=  {- as just shown -}
   f a `oplus` df2 a (nil a)
=  {- by the definition of |`oplus`| on functions (\cref{def:function-changes:update}) -}
   (f `oplus` df2) a {-"\text{.}"-}
\end{code}
\end{equational}
\end{optionalproof}

\pg{Integrate.}
\input{pldi14/sec-change-structures}
