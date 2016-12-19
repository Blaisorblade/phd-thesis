% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\subsection{Function changes}
\label{sec:function-change}

Allowing values to change is useful, but we need to enable also functions to change.
To understand why, think about the curried function
$\Program$: it takes $\Xs$ to a function value (closure) knowing the value of $\Xs$.
Its derivative $\Derivative$ should satisfy
\begin{align*}
& \Program~(\Xs \UPDATE \DXs) = \\
& \Program~\Xs \UPDATE \Derivative~\Xs~\DXs.
\end{align*}
That is, $\Derivative$ must take $\Xs$ and its change to a change
of a closure; updating the closure with this change must give the
same result as $\Program~(\Xs \UPDATE \DXs)$, that is a closure
knowing the value of $\Xs \UPDATE \DXs$.
%
Similarly, since lambda-calculus functions can also take other
functions as arguments, derivatives can take function changes as
arguments.

In this section, we will demonstrate how we can construct change structures
for functions $f \in A
\to B$, assuming change structures for $A$ and $B$.

\paragraph{Definitions}
As seen, the derivative of $f$ computes the change of
$\App f a$ when $a$ becomes $\Upd{a}$. However, also $f$ can
change: As we'll see in \cref{ssec:differentiation},
to incrementalize a function application $f \APP a$ we need to compute the difference $\Upd*{f} \APP
\Upd*{a} \DIFF f \APP a$ without rerunning $\Upd*{f} \APP
\Upd*{a}$. We compute this difference using function changes,
and define change structures on functions precisely to make this possible.
A function change $\D f$ must be a function such that $\Update{\App {f} {a}}{\App{\App{\D f}{a}}{\D a}} = \App
{\Upd*{f}} {\Upd*{a}}$ (\cref{thm:incrementalization})!
Since however $\Upd{f}$ can't be defined yet, we impose a
requirement (\cref{def:function-changes:validity}) that we'll
later show equivalent to \cref{thm:incrementalization}.

% Our definition of function changes
%will guarantee that a function change $\D f$ accepts as arguments
%the original value ${a}$ and a change for it, $\D a \in \Change{{a}}$, and returns a
%change for ${a}$ --- in particular, we will ensure that
%$\Update{\App {f} {{a}}}{\App{\App{\D f}{a}}{\D a}} = \App
%{\Upd*{f}} {\Upd*{a}}$ (\cref{thm:incrementalization}).

% moreover, we impose an additional condition which
%will be equivalent to
%it must be possible to ``flip''
%an element change $\D a$ from a function change to its associated
%function:

\begin{definition}
  \label{def:function-changes:change}
  Given change structures $\ChangeStruct{A}$ and $\ChangeStruct{B}$ and
  $f \in A \to B$,
  the set $\Change[A \to B]{f}$ contains all binary functions $\D
  f$ such that
  \NewDocumentCommand{\TheNewValue}{}{\Upd*{a}}
  \begin{subdefinition}
    \item
      \label{def:function-changes:signature}
      $\App{\App{\D f}{a}}{\D a} \in \Change[B]{\App*{f}{a}}$ and
    \item
      \label{def:function-changes:validity}
      $\App{f}{a} \UPDATE \App{\App{\D f}{a}}{\D a} =
      {\App{f}{\TheNewValue}}
      \UPDATE
      \App{\App{\D f}{\TheNewValue}}{\NilC{\TheNewValue}}$
  \end{subdefinition}
  for all values $a \in A$ and corresponding changes $\D a \in
  \Change[A]{a}$.
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
  Given change structures $\ChangeStruct{A}$ and $\ChangeStruct{B}$,
  the operations $\APPLY[A \to B]$ and $\DIFF[A \to B]$ are
  defined as follows.
  %
  \begin{alignat*}{5}
    &\App{(\Update[A \to B]{f&&}{\D f})}{&&v}
      && = \Update[B]{\App{f}{v}&&}{\App{\App{\D f}{v}}{\NilC[A]{v}}}\\
    &\App{\App{(\Diff[A \to B]{f_2&&}{f_1})}{&&v}}{\D v}
      && = \Diff[B]{\App{f_2}{\Update*[A]{v}{\D v}}&&}{\App{f_1}{v}}\qedAligned
  \end{alignat*}
\end{definition}


\begin{optionallemma}
  \label{thm:diff-valid}
  Given change structures $\ChangeStruct{A}, \ChangeStruct{B}$ and functions $f_1, f_2 \in A
  \to B$, then $\Diff[A \to B]{f_2}{f_1} \in \Change[A \to B]{f_1}$.
\end{optionallemma}

\begin{optionalproof}
  We have to verify the two properties of
  \cref{def:function-changes:change}. The first follows from
  \cref{def:diff} for the change structure $\ChangeStruct{B}$. It remains to
  verify \cref{def:function-changes:validity}.

  Let $a_1 \in A$ be an arbitrary value with a corresponding
  change $\D a \in \Change[A]{a}$, and let $a_2$ be
  $\Apply{\D a}{a_1}$, then
  \begin{align*}
  & \Apply[B]
      {\App{\App{\Diff*[A \to B]{f_2}{f_1}}{a_1}}{\D a}}
      {\App{f_1}{a_1}}\\
  & \quad = \Apply[B]
               {\Diff*[B]
                 {\App{f_2}{a_2}}
                 {\App{f_1}{a_1}}}
               {\App{f_1}{a_1}}\\
  & \quad = \App{f_2}{a_2}\\
  & \quad = \Apply[B]
              {\Diff*[B]
                {\App{f_2}{a_2}}
                {\App{f_1}{a_2}}}
              {\App{f_1}{a_2}}\\
  & \quad = \Apply[B]
              {\Diff*[B]
                {\App{f_2}{\Apply*{\NilC[B]{a_2}}{a_2}}}
                {\App{f_1}{a_2}}}
              {\App{f_1}{a_2}}\\
  & \quad = \Apply[B]
              {\App{\App{\Diff*[A \to B]{f_2}{f_1}}{a_2}}{\NilC{a_2}}}
              {\App{f_1}{a_2}}
  \end{align*}
  by
  \cref{def:function-changes:diff,def:update-diff,thm:update-nil}.
\end{optionalproof}

All these definitions have been carefully set up to ensure that we have
in fact lifted change structures to function spaces.


\begin{theorem}
  \label{thm:func-changestruct}
  Given change structures $\ChangeStruct{A}$ and $\ChangeStruct{B}$, the tuple $(A \to B, \CHANGE[A
  \to B], \UPDATE[A \to B], \DIFF[A \to B])$ is a
  change structure, which we denote by $\ChangeStruct{A} \to \ChangeStruct{B}$.
\end{theorem}

\begin{optionalproof}
  We have to verify the five properties of
  \cref{def:change-struct}. The first two follow by
  construction. \Cref{def:update} follows from the corresponding
  property of the change structure $\ChangeStruct{B}$. \Cref{def:diff} is
  verified in \cref{thm:diff-valid}. It remains to verify
  \cref{def:update-diff}.

  Let $f_1, f_2 \in A \to B$ be arbitrary functions. We show that
  $\Apply[A \to B]{\Diff*[A \to B]{f_2}{f_1}}{f_1}$ is
  extensionally equal to $f_2$. Let $a \in A$ be an arbitrary
  value, then
  \begin{align*}
    & \App{\Apply*[A \to B]{\Diff*[A \to B]{f_2}{f_1}}{f_1}}{a}\\
    & \quad = \Apply[B]
                {\App{\App{\Diff*[A \to B]{f_2}{f_1}}{a}}{\NilC[A]{a}}}
                {\App{f_1}{a}}\\
    & \quad = \Apply[B]
                {\Diff*[B]{\App{f_2}{\Apply*[A]{a}{\NilC[A]{a}}}}{\App{f_1}{a}}}
                {\App{f_1}{a}}\\
    & \quad = \Apply[B]
                {\Diff*[B]{\App{f_2}{a}}{\App{f_1}{a}}}
                {\App{f_1}{a}}\\
    & \quad = \App{f_2}{a}
  \end{align*}
  by the definitions of $\APPLY[A \to B]$ and $\DIFF[A \to B]$,
  \cref{thm:update-nil} for the change structure $\ChangeStruct{A}$ and
  \cref{def:update-diff} for the change structure $\ChangeStruct{B}$.
\end{optionalproof}

After defining this change structure, we can talk about $f
\UPDATE df$. So we can restate \cref{def:function-changes:validity}
to show that a function change $\D f$ reacts to
%
input changes $\D a$ like the incremental version of $f$, that is,
$\App{\App{\D f}{a}}{\D a}$ computes the change from
$\App{f}{a}$ to
$\App{\Apply*{\D f}{f}}{\Apply*{\D a}{a}}$:

\begin{theorem}[Incrementalization]
  \label{thm:incrementalization}
  Given change structures $\ChangeStruct{A}$ and $\ChangeStruct{B}$, a function $f \in A \to B$
  and a value $a \in A$ with corresponding changes $\D f \in
  \Change[A \to B]{f}$ and $\D a \in \Change[A]{a}$, we have that
  \[\App{\Apply*{\D f}{f}}{\Apply*{\D a}{a}}
  = \Apply{\App{\App{\D f}{a}}{\D a}}{\App{f}{a}}\text{.}\qed\]
\end{theorem}

\begin{optionalproof}
  \NewDocumentCommand{\TheNewValue}{}{\Apply*[A]{\D a}{a}}

  Let $f$, $a$, $\D f$ and $\D a$ be arbitrary, as in the statement. Then
  \begin{align*}
    & \App{\Apply*[A \to B]{\D f}{f}}{\Apply*[A]{\D a}{a}}\\
    & \quad = \Apply[B]{\App{\App{\D f}{\TheNewValue}}{\NilC{\TheNewValue}}}{\App{f}{\TheNewValue}}\\
    & \quad = \Apply[B]{\App{\App{\D f}{a}}{\D a}}{\App{f}{a}}
  \end{align*}
  by
  \cref{def:function-changes:update,def:function-changes:validity}
  as required.
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

\subsection{Nil changes are derivatives}

\cref{thm:incrementalization} tells us about the form an
incremental program may take. If $\D f$ doesn't change $f$
at all, that is, if
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
  \begin{align*}
    & \App{f}{\Apply*[A]{\D a}{a}}\\
    & \quad = \App{\Apply*[A \to B]{\NilC[A \to B]{f}}{f}}{\Apply*[A]{\D a}{a}}\\
    & \quad = \Apply[B]{\App{\App{\NilC[A]{f}}{a}}{\D a}}{\App{f}{a}}
  \end{align*}
  holds by \cref{thm:update-nil,thm:incrementalization}, as
  required for derivatives by \cref{def:derivatives}.
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
