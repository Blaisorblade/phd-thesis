% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\section{Function changes}
\label{sec:function-change}

Up to now we described how to model changes for non-function
values; in this section we model changes for first-class
functions.

To understand why we must consider function changes, consider the curried function
|grand_total|: it takes |xs| to a function value (that is, closure) that
knows the value of |xs|. Its derivative |dgrand_total| should
satisfy
\begin{code}
grand_total (xs `oplus` dxs) =
grand_total xs `oplus` dgrand_total xs dxs
\end{code}
That is, |dgrand_total| must take |xs| and its change to a change
of a closure; updating the closure with this change must give the
same result as |grand_total (xs `oplus` dxs)|, that is a closure
knowing the value of |xs `oplus` dxs|.
%
Similarly, since lambda-calculus functions can also take other
functions as arguments, derivatives can take function changes as
arguments.

In this section, we will demonstrate how we can construct change structures
for functions |f `elem` A -> B|, assuming change structures for |A| and |B|.

\paragraph{Definitions}
As discussed, derivatives enable incrementalizing function
application when function arguments change. When |a| changes to
|a `oplus` da|, we can compute the change of |f a|
\emph{incrementally}: That is, instead of computing |f (a `oplus`
da) `ominus` f a| (which applies |f| on the whole updated input
and is potentially very slow), we can use the derivative |df|
and compute |df a da|. We can be sure these changes are
equivalent (\cref{lem:derivatives-up-to-doe}), and as we'll show
that using can be much faster.

We represent function changes as binary functions that generalize
derivatives, so that function changes enable incrementalizing
function application when both function arguments and functions
change. When |a| changes to |a `oplus` da| and additionally |f|
changes to |f `oplus` df|, we can compute the change of |f a|
\emph{incrementally}: That is, instead of computing |(f `oplus`
df) (a `oplus` da) `ominus` f a| (which again applies the updated
function |f `oplus` df| on the whole updated input and is
potentially very slow), we can use change |df| and compute |df a
da|. We'll ensure these changes are equivalent
(\cref{thm:incrementalization})
\[|df a da `doe` (f `oplus` df) (a `oplus` da)
  `ominus` f a|\]
and we'll see that the latter can
be, again, much faster. We will apply this insight in
\cref{ssec:differentiation}.

However, to guarantee correctness we must place requirements on
function changes. \Cref{thm:incrementalization} is not true for
arbitrary functions |df|. Instead, we add it as a requirement in
the definition of function changes. However, we must define the
set of function changes \emph{before} we formally define
|`oplus`| on them, so we need to rephrase
\cref{thm:incrementalization}. We will define |(f `oplus` df) a|
as |f a `oplus` df a (nil(a))|, so \cref{thm:incrementalization}
becomes
\[|df a da `doe` f (a `oplus` da) `oplus` df (a `oplus` da)
  (nil(a `oplus` da)) `ominus` f a|\] or, in terms of equality,
\[|f a `oplus` df a da = f (a `oplus` da) `oplus` df (a `oplus`
  da) (nil(a `oplus` da))|\text{.}\] We use this equation as part
of the definition of function changes
(\cref{def:function-changes:validity}), and which we'll use in
the proof of \cref{thm:incrementalization}.

\begin{definition}
  \label{def:function-changes:change}
  The change set |DtIdx(A -> B) f| is defined for any change
  structures $\chs A$ and $\chs B$ and function |f `elem` A ->
  B|.
  This change set contains all binary functions |df| that satisfy the following conditions:
  \begin{subdefinition}
    \item
      \label{def:function-changes:signature}
      |df a da `elem` DtIdx(B) (f a)| and
    \item
      \label{def:function-changes:validity}
      |f a `oplus` df a da = f (a `oplus` da) `oplus` df (a `oplus` da) (nil(a `oplus` da))|.
  \end{subdefinition}
  for all values |a `elem` A| and corresponding changes
  |da `elem` DtIdx(A) ^ a|.
\end{definition}

\begin{examples}
Suppose $f\in\Fun{\Bag S}{\Bag S}$ and consider a member $\D f$ of
the change set $\Change[A \to B]{f}$. Condition~(a) says that $\D
f$ should map a bag and a bag change to another bag change.
Condition~(b) requires $\D f$ to mimic the incremental behavior
of $f$. Taken together, they codify what we consider appropriate
incremental adjustments to $f$.

In particular, different functions of the same type can have
different sets of changes. Consider two functions of type
$\Fun{\Bag S}{\Bag S}$.
\begin{align*}
\App{f}{x} & = \Empty & \App{\Var{id}}{x} & = x
\end{align*}
The set
$\Change[\Fun{\Bag S}{\Bag S}] f$ contains ``changes'' to $f$,
namely all binary bag functions $df$ satisfying
(b): $\D{f}~a~\D{a}=\D{f}\APP\Upd*{a}\APP\NilC{\Upd*{a}}= \D{f}~(\MERGE~a~\D{a})~\Empty$.
Such binary functions include
$\MERGE$ and all constant functions.

The set $\Change[\Fun{\Bag S}{\Bag S}]\Term{id}$ contains changes to $id$,
namely all binary bag functions $\D{id}$ satisfying
(b):
$\Term{id}\APP a \UPDATE \D{id} \APP a \APP \D{a} =
\Term{id} \APP \Upd*{a} \UPDATE \D{id} \APP \Upd*{a} \APP
\NilC{\Upd*{a}}$, which simplifies to
$\MERGE~a~(\D{id}~a~\D{a})=
\MERGE~(\MERGE~a~\D{a})~(\D{id}~(\MERGE~a~\D{a})~\Empty)$.
Neither $\MERGE$ nor any constant function is a change to
$\Term{id}$,
but the function
$
\D{id}~a~\D a = \Merge{\D a}{\Set{1,2}}
$ is.
\end{examples}

The change-structure operations on functions can now be defined
similarly to a distributive law.

% Maybe reduce subscripts here?
\begin{definition}[Operations on function changes]
  \label{def:function-changes:update}
  \label{def:function-changes:diff}
  Operations |oplusIdx(A -> B)| and |ominusIdx(A -> B)| are defined as follows
  for all change structures $\chs A$ and $\chs B$:
  %
\begin{code}
(f   `oplus` df)   v     = f v                `oplus`   df v (nil(v))
(f2  `ominus` f1)  v dv  = f2 (v `oplus` dv)  `ominus`  f1 v
\end{code}%
  % \begin{alignat*}{5}
  %   &\App{(\Update[A \to B]{f&&}{\D f})}{&&v}
  %     && = \Update[B]{\App{f}{v}&&}{\App{\App{\D f}{v}}{\NilC[A]{v}}}\\
  %   &\App{\App{(\Diff[A \to B]{f_2&&}{f_1})}{&&v}}{\D v}
  %     && = \Diff[B]{\App{f_2}{\Update*[A]{v}{\D v}}&&}{\App{f_1}{v}}\qedAligned
  % \end{alignat*}
\end{definition}


\begin{optionallemma}
  \label{thm:diff-valid}
  Difference |f2 `ominus` f1| belongs to |DtIdx(A -> B) f1|
  for any change structures $\chs A$, $\chs B$ and functions |f1,
  f2 `elem` A -> B|.
\end{optionallemma}

\begin{optionalproof}
  We have to verify the two properties of
  \cref{def:function-changes:change}.

  We first prove \cref{def:function-changes:signature}. It says that
  |(f2 `ominus` f1) a da `elem` DtIdx(B) (f1 a)| for any |a `elem` A|. Since
  |(f2 `ominus` f1) a da| is defined to be |f2 (a `oplus` da) `ominus` f1 a|, the thesis follows from the type of |`ominus`|, that is, \cref{def:diff} for change structure $\chs B$.

  We next prove \cref{def:function-changes:validity}, that is
  \[|f1 a `oplus` (f2 `ominus` f1) a da = f1 (a `oplus` da) `oplus`
  (f2 `ominus` f1) (a `oplus` da) (nil(a `oplus` da))|.\]

  For convenience, let us replace |a| by |a1| and |a `oplus` da|
  by |a2|, where |a1 `elem` A| is an arbitrary value with a
  corresponding change |da `elem` DtIdx(A) a1|, and |a2| is |a1
  `oplus` da|. The thesis becomes then:
  \[|f1 a1 `oplus` (f2 `ominus` f1) a1 da = f1 a2 `oplus` (f2
    `ominus` f1) a2 (nil(a2))|.\]

  Let |a1 `elem` A| be an arbitrary value with a corresponding
  change |da `elem` DtIdx(A) a1|, and let |a2| be
  |a1 `oplus` da|. We prove the thesis by equational reasoning through the following calculation:
\begin{equational}
\begin{code}
   f1 a1 `oplus` (f2 `ominus` f1) a1 da
=  {- by the definition of |`ominus`| on functions (\cref{def:function-changes:diff}) -}
   f1 a1 `oplus` (f2 (a1 `oplus` da) `ominus` f1 a1)
=  {- because |a2 = a1 `oplus` da| -}
   f1 a1 `oplus` (f2 a2 `ominus` f1 a1)
=  {- by change cancellation (\cref{def:update-diff}) -}
   f2 a2
=  {- again by chance cancellation, in reverse -}
   f1 a2 `oplus` (f2 a2 `ominus` f1 a2)
=  {- because |nil(a2)| is a nil change (\cref{thm:update-nil-v2}) -}
   f1 a2 `oplus` (f2 (a2 `oplus` (nil(a2))) `ominus` f1 a2)
=  {- by the definition of |`ominus`| on functions (\cref{def:function-changes:diff}) -}
   f1 a2 `oplus` ((f2 `ominus` f1) a2 (nil(a2)))
\end{code}
\end{equational}
\end{optionalproof}

All these definitions have been carefully set up to ensure that we have
in fact lifted change structures to function spaces.

\begin{theorem}
  \label{thm:func-changestruct}
  The tuple |(A -> B, DtIdx(A -> B), oplusIdx(A -> B),
  ominusIdx(A -> B))| is a change structure, which we denote by
  $\chs A \to \chs B$, for any change structures $\chs A$ and
  $\chs B$.
\end{theorem}

\begin{optionalproof}
  We have to verify the five properties of
  \cref{def:change-struct}.
  \begin{subdefinition}
  \item |A -> B| is a set (\cref{def:base-set}).
  \item By construction, |DtIdx(A -> B) f| is a set for any |f
    `elem` A -> B| (\cref{def:change-set}).
  \item Next we verify the typing of |`oplus`|: we must show that
    |f `oplus` df `elem` A -> B|, and this follows because |(f
    `oplus` df) a = f a `oplus` df a (nil(a)) `elem` B|
    (\cref{def:update}).
  \item We proved in \cref{thm:diff-valid} that |`ominus`|
    produces changes (\cref{def:diff}).
\item It remains to verify
  \cref{def:update-diff}.

  Let |f1, f2 `elem` A -> B| be arbitrary functions. Our thesis
  is that |f1 `oplus` (f2 `ominus` f1) = f2|. We show this
  equality is extensionally true.\pg{Expand on extensionality in
    footnote/earlier.} In other words, we show that |(f1 `oplus`
  (f2 `ominus` f1)) = f2 a| for an arbitrary |a `elem` A|. We
  prove the thesis by equational reasoning through the following
  calculation:
  % $\Apply[A \to B]{\Diff*[A \to B]{f_2}{f_1}}{f_1}$ is
  % extensionally equal to $f_2$.

\begin{equational}
\begin{code}
   (f1 `oplus` (f2 `ominus` f1)) a
=  {- by the definition of |`oplus`| on functions -}
   f1 a `oplus` ((f2 `ominus` f1) a (nil(a)))
=  {- by the definition of |`ominus`| on functions -}
   f1 a `oplus` (f2 (a `oplus` (nil(a))) `ominus` f1 a)
=  {- because |nil(a)| is a nil change (\cref{thm:update-nil-v2} for $\chs A$) -}
   f1 a `oplus` (f2 a `ominus` f1 a)
=  {- by change cancellation (\cref{def:update-diff} for $\chs B$) -}
   f2 a
\end{code}
\end{equational}
\end{subdefinition}
\end{optionalproof}

After defining this change structure, as promised we finally restate
\cref{def:function-changes:validity}: we show that a function
change |df| reacts to input changes |da| like the incremental
version of |f|, that is, |df a da| computes the change from |f a|
to |(f `oplus` df) (a `oplus` da)|:

\begin{theorem}[Incrementalization]
  \label{thm:incrementalization}
  Given change structures $\chs A$ and $\chs B$, a function |f `elem` A -> B|
  and a value |a `elem` A| with corresponding changes |df `elem` Dt f| and
  |da `elem` Dt a|, we have that
  \[|df a da `doe` (f `oplus` df) (a `oplus` da) `ominus` f a|\]
  or equivalently

  \[|(f `oplus` df) (a `oplus` da) = f a `oplus` df a da|\text{.}\qed\]
\end{theorem}

\begin{optionalproof}
  \NewDocumentCommand{\TheNewValue}{}{\Apply*[A]{\D a}{a}}

  Take arbitrary |f|, |a|, |df| and |da|, as in the statement.
  The two forms of the thesis are equivalent by
  \cref{thm:equiv-cancel}. We prove the second form of the thesis
  by equational reasoning:
\begin{equational}
\begin{code}
   (f `oplus` df) (a `oplus` da)
=  {- by the definition of |`oplus`| on functions -}
   f (a `oplus` da) `oplus` df (a `oplus` da) (nil(a `oplus` da))
=  {- by \cref{def:function-changes:validity} -}
   f a `oplus` df a da
\end{code}
\end{equational}
\end{optionalproof}

For instance,
incrementalizing
\[
\APPFun = \Lam{f}{\Lam{x}{\App f x}}
\]
with respect to the input changes $\D f$, $\D x$ amounts to
calling $\D f$ on the original second argument $\Old x$ and on
the change $\D x$. In other words, incrementalizing $\APPFun$ gives
$\Lam{f} {\Lam{\D f} {\Lam{x} {\Lam{\D x} {\App {\App {\D f} x} {\D x}}}}}$.
\begin{oldSec}
We hence solve difficulties described in
section~\ref{ss:pointwise-limit}.
\end{oldSec}

\paragraph{Understanding function changes}
To understand function changes, we can decompose them
into two orthogonal concepts. With a function change $\D f$, we can compute at
once $\App{\App{\D f}{\Old{a}}}{\D a}$, the difference between $\App {\Upd*{f}} {\Upd*{a}}$ and $\App
{{f}} {{a}}$, even though both the function and its argument change.
But the effect of those two changes can be described separately.
We can account for changes to $a$ using $f'$, the derivative of $f$: $\App{{f}} {\Upd*{a}} \DIFF \App{{f}} {{a}} = \App{\App{f'}{{a}}}{\D a}$.
We can account for changes to $f$ using the \emph{pointwise difference} of two functions, $\nabla
f = \Lam{a}{\App{\Upd*{f}}{a} \DIFF \App{{f}}{a}}$; in particular, $\Upd*{f} \APP \Upd*{a} \DIFF {f} \APP \Upd*{a} = \nabla f \APP \Upd*{a}$.
Using then the incrementalization theorem, we can show that a function change simply \emph{combines} a derivative with a pointwise change:
\pg{I don't say ``compose'' because that's overloaded with function composition.}
%
%To account for changes to $a$, we can use
%$f'$, the derivative of $f$. To account for changes to $f$, we
%can use the \emph{pointwise difference} of two functions, $\nabla
%f = \Lam{a}{\App{\New{f}}{a} \DIFF \App{\Old{f}}{a}}$.
%
% Now,
%assuming for the moment the incrementalization theorem, we can
%show the meaning of a function change $df$ in terms of
%derivatives and pointwise changes:
%
\begin{align*}
  & \Update{\App {\Old{f}} {\Old{a}}}{\App{\App{\D f}{\Old{a}}}{\D a}} \\
%= & \App{\New{f}}{\New{a}} = \App{\Old{f}}{\New{a}} \UPDATE \App{\nabla f}{\New{a}} \\
= & \Update{\App{\Old{f}}{\Old{a}}}{\App{\App{f'}{\Old{a}}}{\D a}} \UPDATE \App{\nabla f}{\New{a}}
\end{align*}

One can also compute a pointwise change from a function change:
%In particular, a pointwise change can be obtained from a function
%change by substituting to $da$ a nil change $\NilC{a}$. The result of
%$\App{\App{f'}{\Old{a}}}{\NilC{a}}$ is also a nil change (by
%\cref{thm:deriv-nil}), and $\New{a} = \Old{a}$, so we obtain:
\[
  \Update{\App {f} {a}}{\App{\App{\D f}{a}}{\NilC{a}}}
= \App{f}{a} \UPDATE \App{\nabla f}{a}
\]

%If we substitute $\App{\nabla f}{\New{a}}$ away in the equation before, we obtain the equality:
%\begin{align*}
%  & \Update{\App {\Old{f}} {\Old{a}}}{\App{\App{\D f}{\Old{a}}}{\D a}} \\
%= & \App{\Old{f}}{\New{a}} \UPDATE \App{\nabla f}{\New{a}} \\
%= & \App{\Old{f}}{\New{a}} \UPDATE \App{\App{\D f}{\New{a}}}{\NilC{\New{a}}}
%\end{align*}
%
%The above discussion was informal. To formalize it, we must
%proceed in the opposite way: we incorporate this equality in the
%definition of function changes, define $\UPDATE$ and $\DIFF$ for
%changes, and only then we can finally state and prove the
%incrementalization theorem, since the formal statement depends on
%the definition of change structures.

%% Alternative one: write the actual equation. But that's very complicated.
%% Here a partial one, without the correctness condition.
%Symbolically
%
%\[
%% \Change[\Fun*{\Gs}{\Gt}]{f} =
%\D f \in
%\HasType*{\Old{a}}{\Eval{\Gs}} \to
%            \Change[\Gs]{\Old{a}} \to
%            \Change[\Gt]{\App*{f}{a}}
%\]
%\pg{revise remaining text after adding the above paragraph.}
%
%% Alternative two (what we did in the submission).
%If a function has type $\Fun* \Gs \Gt$, we represent a change to that function
%by a function of type $\Fun{\Gs}{\Fun{\Change\Gs}{\Change\Gt}}$. By syntactically
%abusing $\Delta$ as a type operator, we can write this as:
%\begin{equation}
%\label{eq:conflation-intro}
%\Change{\Fun* \Gs \Gt} = \Fun{\Gs}{\Fun{\Change\Gs}{\Change\Gt}}.
%\end{equation}

%Once we define change structures for
%functions, we will show that a function change produces as output
%the difference between the updated output $\App {\Update*{f}{\D f}}
%{\Update*{a}{\D a}}$ and the original output $\App f a$. This
%difference is caused by two changes: the change to $a$ given by
%$\D a$ and the change of $f$ itself given by $\D f$. \pg{Maybe add
%  one sentence to highlight the importance of this conflation?}

\ILC\ is based on function changes instead of pointwise changes
because a function
change receives strictly more information than a pointwise
change, and is therefore more readily optimized.

\section{Nil changes are derivatives}

We anticipated that function changes generalize derivatives. It
turns out that indeed derivatives are special function changes,
in particular, they are nil changes, and viceversa.

% No clue what this commented out sentence from the paper means.
% \cref{thm:incrementalization} tells us about the form an
% incremental program may take.
If |df| is a nil change for |f|, that is, if
$
\Apply{\D f}{f}= f
$,
then \cref{thm:incrementalization} becomes
\[
 \App {f} {\Apply* {\D a} {a}}
 =
\Apply {\App {\App {\D f} {a}} {\D a}} {\App{f}{a}}.
\]
It says that $\D f$ computes the change upon the output of $f$ 
given a change $\D a$ upon the input $a$ of $f$. In
other words, the nil change to a function is exactly its
derivative (see \cref{def:derivatives}):


\begin{theorem}[Nil changes are derivatives]
  \label{thm:nil-is-derivative}
  Given change structures $\ChangeStruct{A}$ and $\ChangeStruct{B}$ and a function $f \in A \to B$,
  the change $\NilC[A \to B]{f}$ is the derivative $f'$ of $f$.
\end{theorem}

\begin{optionalproof}
  Let $a \in A$ be an arbitrary value with a corresponding change
  $\D a \in \Change[A]{a}$. Then
\begin{equational}
  \begin{code}
   f (a `oplus` da)
=  {- because |nil(f)| is a nil change (\cref{thm:update-nil-v2} for $\chs {A \to B}$) -}
   (f `oplus` (nil(f))) (a `oplus` da)
=  {- by \cref{thm:incrementalization} on |nil(f)| -}
   f a `oplus` nil(f) a da
\end{code}
\end{equational}
So |nil(f)| is a derivative of |f| because it satisfies the appropriate \cref{def:derivatives}.
\end{optionalproof}

\begin{oldSec}
\pg{The following two paragraphs are too verbose, and possibly
  unneeded.}

It is theoretically sound to equate function changes and
incremental functions according to
equation~\ref{eq:conflation-intro}: We prove, in
section~\ref{sec:correctness}, that the differentiation
transformation produces correct incremental programs.

The identification between function changes and incremental functions
is practically feasible. In section~\ref{sec:plugins}, we fully
instantiate the differentiation transformation with a concrete
plugin of ground types and primitive operators, expressive enough
for many use cases of MapReduce. In section~\ref{sec:eval}, we
demonstrate, by benchmark, the efficiency of incremental programs
obtained via differentiation.

\input{pldi14/fig-function-change}
\end{oldSec}


\begin{oldSec}
There is a technical subtlety in interpreting incremental
functions as changes. If we update
$\HasType {\Old f} {\Fun\Gs\Gt}$
according to
$\HasType {\D f} {\Fun \Gs {\Fun {\Change\Gs} {\Change\Gt}}}$,
then we expect the result of updating $\Old f$ according to
$\D f$ would be a function from $\Gs$ to $\Gt$ just like $f$:
\[
\New f = \HasType {\Apply* {\D f} {\Old f}} {\Fun \Gs \Gt}.
\]
How are we to compute the value of $\App* {\New f} x$ on each
argument $x$ of type $\Gs$? The change $\D f$ needs an additional
argument of type $\Change\Gs$ in order to compute a change to the
old result $\App* {\Old f} x$. If we can obtain the nil change
$\HasType {\D x_0} {\Change\Gs}$ such that
\[
\Apply {\D x_0} x = x,
\]
then reading \cref{eq:validity-intro} from right to
left gives
\[
\App {\Apply* {\D f} {\Old f}} x
=
\App {\Apply* {\D f} {\Old f}} {\Apply* {\D x_0} x}
=
\Apply {\App* {\App {\D f} x} {\D x_0}} {\App*{\Old f} x},
\]
which is a reasonable way to define $\APPLY$ recursively on
function types. It remains to procure the nil change $\D x_0$.

It is possible to set up the system in a number of ways to make
$\D x_0$ available. We chose to define an infix difference
operator
\[
\HasType \DIFF {\Fun \Gt {\Fun \Gt {\Change\Gt}}}
\]
such that $\Diff y x$ is the change from $x$ to $y$. The
difference operator $\DIFF$ constrains the choice of $\Change\Gt$
to types with enough inhabitants to describe changes between all
value pairs of type $\Gt$, but this constraint is offset by the
operator's usefulness in the correctness proof. On the practical
side, recomputation on the updated input may be inevitable in
some situations, and the difference operator $\DIFF$ is an
elegant way for the incremental program to proclaim that it
cannot do any better than recomputation.
\pg{$\DIFF$ is/should be introduced earlier.}

\pg{We could have a \texttt{nil-term} type-indexed term / term
  family (we don't write that $\DIFF$ and $\APPLY$ are
  type-indexed). For functions we can use the above definition,
  relying on $\DIFF$, but for all other types we have better
  definitions. Moreover, \texttt{nil-term} fits nicely in the
  algebra of changes.}
\end{oldSec}


In this section, we developed the theory of changes to define
formally what a derivative is (\cref{def:derivatives}) and to
recognize that in order to find the derivative of a function, we
only have to find its nil change
(\cref{thm:nil-is-derivative}). Next, we want to provide a fully
automatic method for finding the nil change of a given function.
