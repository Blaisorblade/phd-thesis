% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt


\chapter{Static differentiation for simply-typed \TitleLambda{}-calculus}
%\section{Incrementalizing \TitleLambda{}-calculi}
\label{sec:differentiate}
\label{sec:correctness}

\pg{reformat for new layout, things overlap!}
\input{pldi14/fig-base-derive}

\pg{Here we need an example like the one in Sec. 2.2, using the syntactic counterpart to closures, that is open terms.}
In this chapter, we show how to incrementalize an arbitrary
program in simply-typed $\Gl$-calculus. To this end, we define
the source-to-source transformation $\DERIVE$. Using the
denotational semantics $\Eval{-}$ we define later (in
\cref{sec:denotational-sem}), we can specify $\DERIVE$'s intended
behavior: to ensure \cref{eq:correctness},
$\Eval{\Derive{f}}$ must be the derivative of $\Eval{f}$
for any closed term $\HasType{f}{A \to B}$. We will overload the word
``derivative'' and say simply that $\Derive{f}$ is the derivative of
$f$.

It is easy to define derivatives of arbitrary functions as:
\[\App{\App{f'}{x}}{\D x} = \Diff{\App{f}{\Update*{x}{\D x}}}{\App f x}\text{.}\]
We could implement $\DERIVE$ following the same strategy.
However, the resulting incremental programs would be no faster
than recomputation. We cannot do better for arbitrary mathematical functions,
since they are (in general) infinite objects which we cannot fully inspect.
%
\pg{Revise - I reordered sentences to sort them logically with minimal rewriting.}%
Therefore, we resort to a source-to-source transformation
on simply-typed $\Gl$-calculus (STLC).
We recall the syntax and typing rules of STLC in \cref{fig:syntax,fig:typing}. In this section, we focus on the
incrementalization of the features that are shared among all
instances of the plugin interface, that is, function types and the
associated syntactic forms, $\Gl$-abstraction, application and
variable references.

The sets of base types and primitive
constants, as well as the typing rules for primitive constants, are
on purpose left unspecified and only defined by plugins --- they are \emph{extensions points}.
%
We use ellipses (``$\ldots$'') for some extension points, and
give names to others when needed to refer to them.
%
Defining different plugins allows to experiment with sets of base
types, associated primitives and incrementalization strategies.
Making plugin requirements explicit clarifies what is required to
extend the framework beyond our formalization.
%
We summarize requirements on plugins in \cref{ssec:plugin}:
Satisfying these requirements is sufficient to ensure
correct incrementalization.
We show an example plugin in our case study
(\cref{sec:plugins}).

\section{Change types and erased change structures}
\label{ssec:change-types}

\input{pldi14/fig-change-operations}
\input{pldi14/fig-diff-apply}

We developed the theory of change structures in the previous
section to guide our implementation of $\DERIVE$. By
\cref{thm:nil-is-derivative}, $\DERIVE$ has only to find the nil
change to the program itself, because nil changes \emph{are}
derivatives. However, the theory of change structures is not
directly applicable to the simply-typed $\Gl$-calculus, 
because a precise implementation of
change structures requires dependent types. For instance,  
we cannot describe the set of
changes $\Change[\Gt]{v}$ precisely as a non-dependent type, because it depends on the value we plan
to update with these changes. 




To work around this limitation of
our object language, we use a form of \emph{erasure} of dependent types
to simple types. In \cref{fig:change-operations} and \cref{fig:correctness:change-types}, we
define change types $\Change{\Gt}$ as an approximate description
of change sets $\Change[\Gt]{v}$ (\cref{fig:correctness:changes}). 
In particular, all changes in $\Change[\Gt]{v}$ correspond to values of terms with type $\Change{\Gt}$,
but not necessarily the other way around. 
For instance, in the
change structure for natural numbers described in \cref{ssec:change-structures}, we would
have $\Change{\Nat} = \Int$, even though not every
integer is a change for every natural number.
For primitive types $\iota$, 
$\Change{\iota}$ and its associated $\UPDATE$ and $\DIFF$ operator
must be provided by the plugin developer.
For function types, erased change structures are given by \cref{fig:diff-apply}.
%
Erasing dependent types in all components of a change structure,
we obtain \emph{erased change structures}, which represent change
structures as simply-typed $\Gl$-terms
where $\UPDATE$ and $\DIFF$ are
families of $\Gl$-terms. 

Erased change structures are not change structures themselves.
However, we will show how change structures and erased changes
structures have ``almost the same'' behavior
(\cref{sec:differentiate-correct}). We will hence be able to
apply our theory of changes.

\section{Differentiation}
\label{ssec:differentiation}
% The following should explain the invariant for \DERIVE.

When $f$ is a closed term of function type,
$\Derive{f}$ should be its derivative, that is its nil change.
Since $\DERIVE$ recurses on open terms, we need a more general
specification.
%
% We don't need to mention parameters, and not mentioning them
% simplifies the discussion. We will mention them again in the case for abstraction.
We require that if $\Typing{t}{\tau}$, then $\Derive{t}$
represents the change in $t$ (of type $\Change{\Gt}$) in terms of
changes to the values of its free variables. As a special case,
when $t$ is a closed term, there is no free variable to change;
hence, the change to $t$ will be, as desired, the nil change of
$t$.

The following typing rule shows the static semantics of
$\DERIVE$:
\begin{typing}
\Rule[Derive]
  {\Typing{t}{\tau}}
  {\Typing[\Append{\GG}{\DeltaContext{\GG}}]{\Derive{t}}{\DeltaType{\tau}}}
\end{typing}

We see that $\Derive{t}$ has access both to the
free variables in $t$ (from $\GG$) and to their changes (from
$\DeltaContext{\GG}$, defined in
\cref{fig:correctness:change-contexts}).
For example, if a
well-typed term $t$ contains $x$ free, then $\GG$ contains an
assumption $\HasType{x}{\Gt}$ for some $\Gt$ and
$\DeltaContext{\GG}$ contains the corresponding assumption
$\HasType{\D x}{\DeltaType{\Gt}}$. Hence, $\Derive{t}$ can
access the change of $x$ by using $\D x$. For simplicity, 
we assume that the original program contains no variable names
that start with $\D{}$.%
%
\footnote{Alternatively, we could define a mapping from base
  variables $x$ of the original program to change variables
  $d(x)$, and use $d(x)$ instead of $\D x$. To produce the
  intended bindings structure in |derive(t)|, $d$ must be a
  function that evaluates to a fresh object variable $d(x)$ for
  each variable $x$, but it must evaluates to the same variable
  when called with the same input.}
%
As a consequence of the above typing rule, if |t| is closed (that
is, $\Gamma = \emptyset$) then the all the new $\D x$ variables
will be bound.

Let us analyzes each case of the definition of $\Derive{u}$
(\cref{fig:correctness:derive}):
\begin{itemize}
\item If $u = x$, $\Derive{x}$ must be the change of $x$, that is
$\D x$.
\item If $u = \Lam{x}{t}$, $\Derive{t}$ is the change of
  $u$ given the change in its free variables. The change of $u$
  is then the change of $t$ as a function of the \emph{base input}
  $x$ and its change
  $\D x$, with respect to changes in other open variables. Hence,
  we simply need to bind $\D x$ by defining $\Derive{\Lam{x}{t}}
  = \Lam{x}{\Lam{\D x}{\Derive{t}}}$.
\item If $u = \App{s}{t}$, $\Derive{s}$ is the change of $s$ as a function
  of its base input and change. Hence, we simply apply $\Derive{s}$ to 
  the actual base input $t$ and change $\Derive{t}$, giving
  $\Derive{\App{s}{t}} =
  \App{\App{\Derive{s}}{t}}{\Derive{t}}$.
\item If $t = c$: since $c$ is a closed term, its
  change is a nil change, hence (by \cref{thm:nil-is-derivative}) $c$'s derivative. We can
  obtain a correct derivative for constants by setting:
  \[
  \Derive{c} =
  \Diff{c}{c} = \NilC{c} = c'
  \]
  This definition is inefficient for functional constants; hence
  plugins must provide derivatives of the primitives they define.
  We require plugins to define, for each $\ConstTyping{c}{\tau}$,
  a closed term $\DeriveConst(c)$ such that
  $\Typing[\EmptyContext]{\DeriveConst(c)}{\GD \Gt}$.
\end{itemize}

This might seem deceptively simple. But $\lambda$-calculus only
implements binding of values, leaving ``real work'' to
primitives; likewise, differentiation for $\lambda$-calculus only
implement binding of changes, leaving ``real work'' to
derivatives of primitives.
However, our support for
$\Gl$-calculus allows to \emph{glue} the primitives together.

\begin{examples}
Let us apply the transformation on the program $\Program$ defined
in \cref{sec:motiv-example} and repeated here:
\begin{code}
grand_total  = \ xs ys -> fold (+) 0 (merge xs ys)
derive(grand_total) =
  \ xs dxs ys dys ->
    dfold  (+) (d+) 0 d0
           (merge xs ys)
           (dmerge xs dxs ys dys)
\end{code}

The names |dfold|, |dmerge|, |d+|, |d0| stand for the
derivatives of the corresponding primitives. The variables
|dxs| and |dys| are systematically named after |xs|
and |ys| to stand for their changes. As we shall see in
\cref{ssec:plugin},
\begin{code}
dmerge = \ u du v dv -> merge du dv
\end{code}
so the derivative of |grand_total| is $\beta$-equivalent to
\begin{code}
  \ xs dxs ys dys ->
    dfold  (+) (d+) 0 d0
           (merge xs ys)
           (merge dxs dys)
\end{code}
This derivative is inefficient because it needlessly recomputes
|merge xs ys|. We could save this value while running the base program and reuse it here; we will discuss in \cref{sec:static-caching} why this is a generally valid solution and how to do it. However, remembering results from base programs has some overhead which in this case can be avoided! Indeed, we still need to inline the derivatives of
$\FOLD$ and other primitives to complete derivation. We'll
complete the derivation process and see how to avoid either recomputation or caching in
\cref{ssec:self-maint}.
\end{examples}

We have now informally
derived the definition of $\DERIVE$ (\cref{fig:correctness:derive})
from its specification (\cref{eq:correctness}) and
its typing. But formally speaking,
$\DERIVE$ is instead a \emph{definition}. So in the rest of this section,
we'll have to
prove that $\DERIVE$ satisfies \cref{eq:correctness}.

\input{pldi14/sec-correctness}


\section{Plugins}\label{ssec:plugin}

Both our correctness proof and the differentiation framework (which is the 
basis for our implementation) are parametric in the plugin. 
Instantiating the differentiation framework requires a \emph{differentiation plugin};
instantiating the correctness proof for it  requires a \emph{proof           plugin}, containing additional definitions and lemmas.

To allow executing and differentiating $\Gl$-terms, a differentiation plugin must
provide:
\begin{itemize}
\item base types, and for each base type $\Gi$, the erased change structure of $\Gi$ as specified in
\cref{fig:change-operations},
\item primitives, and for each primitive $c$, the term $\DeriveConst{c}$.
\end{itemize}
\begin{examples}
With bags of numbers as a primitive type, and a change structure
erased from $\ChangeStruct{\Bag S}$ (defined in
\cref{ssec:change-structures}), the derivative of $\MERGE$ is
easy to write down:
\[
\Derive{\MERGE}=\Lam{u}{\Lam{\D u}{\Lam{v}{\Lam{\D v}{\Merge{\D u}{\D v}}}}}
\]
In other words, the change to the merge of two bags is the merge of changes to
each bag.
\end{examples}

For each base type $\Gi$, a proof plugin must provide:
\begin{itemize}
\item a semantic domain $\Eval{\Gi}$,
\item a change structure $\ChangeStruct{C}_\Gi$ such that $\forall v. \Change[\Gi]{v} \subseteq \Eval{\Change{\Gi}}$,
\item a proof that $\ChangeStruct{C}_\Gi$ erases to the corresponding erased change structure in the differentiation plugin.
\end{itemize}
For each primitive $\HasType c \Gt$, the proof plugin must provide:
\begin{itemize}
\item its value $\Eval{c}$ in the domain $\Eval{\Gt}$,
\item a proof that |nil(evalConst(c))| erases to the term $\DeriveConst{c}$.
\end{itemize}

To show that the interface for proof plugins
can be implemented, we wrote a small proof plugin with
integers and bags of integers\yc{link to agda}.
To show that differentiation plugins are practicable, we 
have implemented the transformation and a differentiation plugin
which allows the incrementalization of non-trivial programs.
This is presented in the next section.
