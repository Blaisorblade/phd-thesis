% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\input{pldi14/fig-correctness}


\section{Architecture of the proof}

$\Derive{t}$ is defined using change types. As discussed in
\cref{ssec:change-types}, change types impose on their members
less restrictions than corresponding change structures -- they
contain ``junk'' (such as the change $-5$ for the natural number $3$). 
We cannot constrain the behavior of
$\Derive{t}$ on such junk; a direct correctness proof fails. To
avoid this problem, our proof defines a version of $\DERIVE$
which uses change structures instead.


To this end, we first present a standard denotational semantics
$\Eval{-}$ for simply-typed $\Gl$-calculus. Using our theory of
changes, we associate change structures to our domains. We define
a non-standard denotational semantics $\EvalInc{-}$, which is
analogous to $\DERIVE$ but operates on elements of change
structures, so that it needn't deal with junk. As a consequence,
we can prove that $\EvalInc{t}$ is the derivative of $\Eval{t}$:
this is our key result.

Finally, we define a correspondence between change sets and
domains associated with change types, and show that whenever
$\EvalInc{t}$ has a certain behavior on an input,
$\Eval{\Derive{t}}$ has the corresponding behavior on the
corresponding input. Our correctness property follows as a
corollary.

\section{Denotational semantics}
\label{sec:denotational-sem}

In order to prove that incrementalization preserves the meaning
of terms, we define a denotational semantics of the object
language. We first associate a domain with every type, given the
domains of base types provided by the plugin. Since our calculus
is strongly normalizing and all functions are total, we can
avoid using domain theory to model partiality: our domains are
simply sets. Likewise, we can use functions as the domain of function types.


\begin{definition}[Domains]
  The domain $\Eval{\Gt}$ of a type $\Gt$ is defined as in
  \cref{fig:correctness:values}.
\end{definition}

\pg{Don't mix semantics and evaluation!!!}
Given this domain
construction, we can now define an evaluation function for
terms. The plugin has to provide the evaluation function for
constants. In general, the evaluation function |eval(t)| computes the value of a
well-typed term |t| given the values of all free variables in
|t|. The values of the free variables are provided in an
environment.

\begin{definition}[Environments]
  An environment $\Gr$ assigns values to the names of free
  variables.

  \begin{syntax}
    \Gr ::= \EmptyContext \mid \ExtendEnv{x}{v}
  \end{syntax}

  We write $\Eval{\GG}$ for the set of environments that assign
  values to the names bound in $\GG$ (see
  \cref{fig:correctness:environments}).
\end{definition}

\begin{definition}[Evaluation]
  \label{def:evaluation}
  Given $\Typing{t}{\tau}$, the meaning of $t$ is defined by the
  function $\Eval{t}$ of type $\Fun{\Eval{\GG}}{\Eval{\tau}}$
  in \cref{fig:correctness:evaluation}.
\end{definition}

This is the standard semantics of the simply-typed
$\Gl$-calculus.

For each constant |c : tau|, the plugin provides |evalConst(c) :
eval(tau)|, the semantics of |c|; since constants don't contain
free variables, |evalConst(c)| does not depend on an environment.

We can now specify what it means to incrementalize the
simply-typed $\Gl$ calculus with respect to this semantics.

\section{Change semantics}
The informal specification of differentiation is to map
changes in a program's input to changes in the program's
output. In order to formalize this specification in terms of
change structures and the denotational semantics of the object
language,
we now define a non-standard denotational semantics of the object
language that computes changes. The evaluation function
$\EvalInc{t}$ computes how the value of a well-typed term $t$
changes given both the values and the changes of all free
variables in $t$.
In the special case that none of the free variables change,
$\EvalInc{t}$ computes the nil change. By
\cref{thm:nil-is-derivative}, this is the derivative of
$\Eval{t}$ which maps changes to the input of $\Eval{t}$ to
changes of the output of $\Eval{t}$, as required.

First, we define a change structure on $\Eval{\Gt}$ for all
$\Gt$. The carrier $\Change[\Gt]$ of these change structures will
serve as non-standard domain for the change semantics. The plugin
provides a change structure $\ChangeStruct{C}_\Gi$ on base type
$\Gi$ such that $\forall v. \Change[\Gi]{v} \subseteq \Eval{\Change{\Gi}}$.


\begin{definition}[Changes]
  Given a type $\Gt$, we define a change structure
  $\ChangeStruct{C}_\Gt$ for $\Eval{\Gt}$ by induction on the
  structure of $\Gt$. If $\Gt$ is a base type $\Gi$, then
  the result $\ChangeStruct{C}_\Gi$ is supplied by the plugin.
  Otherwise we use the construction from \cref{thm:func-changestruct} and
  define
  \begin{align*}
%    \ChangeStruct{C}_{\Gi} & = \ChangeStruct{C}_\Gi\\
    \ChangeStruct{C}_{\Fun{\Gs}{\Gt}} & = \ChangeStruct{C}_{\Gs} \to \ChangeStruct{C}_{\Gt}.
  \qedAligned
  \end{align*}
\end{definition}

To talk about the derivative of $\Eval{t}$, we need a change
structure on its domain, the set of environments.
Since environments are (heterogeneous) lists of values, we
can lift operations on change structures to change structures on
environments acting pointwise.

\begin{definition}[Change environments]
  \label{def:change-environments}
  Given a context $\GG$, we define a change
  structure $\ChangeStruct{C}_\GG$ on the corresponding
  environments $\Eval{\GG}$ and change environments $\Change[\GG]{\Gr}$
  in \cref{fig:correctness:change-environments}.

  The operations $\APPLY[\Gr]$ and $\DIFF[\Gr]$ are defined as follows.
%
  \begin{align*}
    \Apply{\EmptyContext}{\EmptyContext} &= {\EmptyContext} \\
    \Apply{\ExtendEnv*[\D \Gr]{\D x}{\D v}}{\ExtendEnv*{x}{v}} &= \ExtendEnv[\Apply*{\D \Gr}{\Gr}]{x}{\Apply*{\D v}{v}} \\[\eqsep]
    \Diff{\EmptyContext}{\EmptyContext} &= {\EmptyContext} \\
    \Diff{\ExtendEnv*[\Gr_2]{x}{v_2}}{\ExtendEnv*[\Gr_1]{x}{v_1}} &= \ExtendEnv[\Diff*{\Gr_2}{\Gr_1}]{x}{\Diff*{v_2}{v_1}}
  \end{align*}
%
  The properties in \Cref{def:change-struct} follow directly from the same properties
  for the underlying change structures $\ChangeStruct{C}_\Gt$.
\end{definition}

At this point, we can define the change semantics of terms and
prove that $\EvalInc{t}$ it is the derivative of $\Eval{t}$.

\begin{definition}[Change semantics]
  \label{def:change-evaluation}
  The function |evalInc(t)| is defined in
  \cref{fig:correctness:change-evaluation}.
\end{definition}
% \begin{lemma}
%   \label{def:change-evaluation-is-change}
%   Evaluating |evalInc(t) rho drho| results in a change to |eval(t) rho|, for
%   any well-typed term $\Typing{t}{\Gt}$, for any environment
%   $\Gr \in \Eval{\GG}$ and environment change
%   $\D\Gr \in \Delta \Gr$.
% \end{lemma}
% \begin{optionalproof}
  % To show the thesis, we need to prove that
  % the definition of |evalInc(t)| produces indeed a valid change.

  % We proceed by
  % structural induction on the typing derivation for
  % $\Typing{t}{\Gt}$. The only substantial case is for abstraction.
  % \Case |c|: The thesis is that |evalInc(c) rho drho = nil(eval(c) rho)| is a change for |eval(t) rho|, which is true because |nil(v)| is a change for |v|.
  % \Case |x|: The thesis is that |evalInc(x) rho drho = \textit{lookup $\D x$ in $\D \Gr$}| is a change for |eval(x) rho = \textit{lookup $x$ in $\Gr$}|. This follows because $\D\Gr$ is a change for $\Gr$.

  % \Case |s t1|: The type |tau| must be |sigma -> tau1|. The thesis is that
  % \begin{code}
  %   evalInc(s t1) rho drho = (evalInc(s) rho drho) (eval(t1) rho) (evalInc(t1 rho drho)
  % \end{code}
  % is a change for |eval(s t1) rho : eval(sigma) -> eval(tau1)|.

  % First, |evalInc(s) rho drho| is a valid change for |eval(s) rho| by the induction hypothesis, so it has type |Dt ^ (eval(s) rho) = (v : eval(sigma)) -> Dt ^ v -> Dt ^ (eval(s) rho v)|.

  % Second, by the induction hypothesis |evalInc(t1) rho drho| is a
  % change for |eval(t1) rho|, so |(evalInc(s) rho drho) (eval(t1)
  % rho) (evalInc(t1 rho drho)| has type |Dt ^ (eval(s) rho
  % (eval(t1) rho)) = eval(s t1) rho| as desired.

  % \Case \Lam{x}{t_1}: This case is the most interesting. We need to prove that
  % |eval(\x -> t1) (rho `oplus` drho) (v `oplus` dv) `oplus` evalInc(\x -> t1) (rho `oplus` drho) (nil (rho `oplus` drho)) ≡ eval(\x -> t1) rho `oplus` evalInc(\x -> t1) rho drho|

        % ⟦ t ⟧ (v `oplus` dv • ρ)  `oplus`₍ τ ₎
        % ⟦ t ⟧Δ (v `oplus` dv • ρ) (nil (v `oplus` dv) • dρ) ==
        % ⟦ t ⟧ (v • ρ)  `oplus`  ⟦ t ⟧Δ (v • ρ) (dv • dρ)

% \end{optionalproof}
\begin{lemma}
  \label{lem:change-semantics-correct}
  The change semantics $\EvalInc{t}$ is the derivative of the standard semantics $\Eval{t}$ for any well-typed term $t$ with $\Typing{t}{\Gt}$.
%   Evaluating |evalInc(t) rho drho| results in a change to |eval(t) rho|, for
%   any well-typed term $\Typing{t}{\Gt}$, for any environment
%   $\Gr \in \Eval{\GG}$ and environment change
%   $\D\Gr \in \Delta \Gr$.
\end{lemma}

\begin{optionalproof}
  We proceed by induction on the structure of the derivation of
  $\Typing{t}{\Gt}$. There is one case for each of the typing
  rules in \cref{fig:typing}.

  Pick arbitrarily a derivation of $\Typing{t}{\Gt}$, an environment
  |rho `elem` eval(Gamma)| , and a corresponding change environments
  |drho `elem` Dt ^ rho|. The thesis has then two parts:
  \begin{enumerate}
  \item |evalInc(t) : (rho : eval(Gamma)) -> (drho : Dt ^ rho) -> Dt (eval(t) rho)|, that is |evalInc(t) rho drho| is a change for |eval(t) rho|, and that
  \item |evalInc(t)| is indeed a derivative for |eval(t)|, hence
    \begin{code}
    eval(t) rho `oplus` evalInc(t)^ rho drho = eval(t) (rho `oplus` drho)
    \end{code}
  \end{enumerate}
  The first part ensures |evalInc(t)| has the correct typing to be a derivative.
  It is proved in Agda simply by typechecking the definition of |evalInc(t)|, in
  all cases except for |t = \x -> t1|.%
  %
  There, |evalInc(t)^ rho drho| is defined as |\v dv -> evalInc(t1)^ (rho, x =
  v) (drho, dx = dv)|; we must check its validity
  (\cref{def:function-changes:validity}).

  The two proofs are mutually recursive.

  \Case \Lam{x}{t_1}:
  In this case, $\Gt = \Fun{\Gs}{\Gt_1}$.
  We need to prove, first, that |evalInc(\x -> t1) rho drho| is a change for |eval(\x -> t1) rho|. Hence we must show that
  \begin{code}
    eval(\x -> t1) rho (v `oplus` dv) `oplus` evalInc(\x -> t1)^ rho drho (v `oplus` dv) (nil (v `oplus` dv)) =
    eval(\x -> t1) rho v `oplus` evalInc(\x -> t1) rho drho v dv
  \end{code}

  Since we're proving both parts of the thesis together by mutual induction,
  we can assume as induction hypothesis that |evalInc(t1)| is a derivative for |eval(t1)|.

  We proceed by equational reasoning:
\begin{equational}
  \begin{code}
    eval(\x -> t1) rho (v `oplus` dv) `oplus` evalInc(\x -> t1)^ rho drho (v `oplus` dv) (nil (v `oplus` dv))
=   {- by definition of (change) evaluation -}
    eval(t1) (rho, x = v `oplus` dv) `oplus` evalInc(t1)^ (rho, x = v `oplus` dv) (drho, dx = nil (v `oplus` dv))
=   {- since |evalInc(t1)| is a derivative of |eval(t1)| -}
    eval(t1) ((rho, x = v `oplus` dv) `oplus` (drho, dx = nil (v `oplus` dv)))
=   {- by the definition of |`oplus`| on environments -}
    eval(t1) (rho `oplus` drho, x = v `oplus` dv `oplus` nil (v `oplus` dv))
=   {- by properties of nil changes -}
    eval(t1) (rho `oplus` drho, x = v `oplus` dv)
=   {- by the definition of |`oplus`| on environments -}
    eval(t1) ((rho, x = v) `oplus` (drho, dx = dv))
=   {- since |evalInc(t1)| is a derivative of |eval(t1)| -}
    eval(t1) (rho, x = v) `oplus` evalInc(t1)^ (rho, x = v) (drho, dx = dv)
=   {- by definition of (change) evaluation -}
    eval(\x -> t1) rho v `oplus` evalInc(\x -> t1)^ rho drho v dv
  \end{code}
\end{equational}

  Second we must prove that
  \begin{code}
    eval(\x -> t1) rho `oplus` evalInc(\x -> t1)^ rho drho =
    eval(\x -> t1) (rho `oplus` drho)
  \end{code}

  The thesis states the equality of two functions, and we prove
  it using extensional function equality: that is, we apply both
  sides to an arbitrary argument $v \in \Eval{\Gs}$ and prove the
  results are equal. We have
\begin{equational}
\begin{code}
    (eval(\x -> t1) rho `oplus` evalInc(\x -> t1) rho drho) v
=   {- by the definition of |`oplus`| on functions (\cref{def:function-changes:update}) -}
    (eval(\x -> t1) rho v `oplus` evalInc(\x -> t1) rho drho v (nil v))
=   {- by the definitions of (change) evaluation (\cref{def:evaluation,def:change-evaluation}) -}
    (eval(t1) (rho, x = v) `oplus` evalInc(t1) (rho, x = v) (drho, dx = (nil v)))
=   {- by the induction hypothesis on |t1| -}
    (eval(t1) ((rho, x = v) `oplus` (drho, dx = (nil v))))
=   {- by the definition of |`oplus`| on environments (\cref{def:change-environments}) -}
    eval(t1) (rho `oplus` drho, x = v `oplus` (nil v))
=   {- because |nil v| is a nil change (\cref{thm:update-nil-v2,def:nil-change-v2}) -}
    eval(t1) (rho `oplus` drho, x = v)
=   {- by the definition of evaluation (again) -}
    eval(\x -> t1) (rho `oplus` drho) v
\end{code}
\end{equational}
  \Case \App{s}{t_1}: We have
\begin{equational}
\begin{code}
    eval(s t1) rho `oplus` evalInc(s t1) rho drho
=   {- by the definitions of (change) evaluation (\cref{def:evaluation,def:change-evaluation}) -}
    (eval(s) rho) (eval (t1) rho) `oplus` (evalInc(s) rho drho) (eval(t1) rho) (evalInc(t1) rho drho)
=   {- by incrementalization on function change |evalInc(s) rho drho| (\cref{thm:incrementalization}) -}
    (eval(s) rho `oplus` evalInc(s) rho drho) (eval (t1) rho `oplus` evalInc(t1) rho drho)
=   {- by the induction hypothesis on |s| and |t1| -}
    eval(s) (rho `oplus` drho) (eval (t1) (rho `oplus` drho))
=   {- by the definition of evaluation (again) -}
    eval(s t1) (rho `oplus` drho)
\end{code}
\end{equational}

  \Case \Var{x}:
  Since $\Typing{x}{\Gt}$, we know that the typing assertion $x : \Gt$
  appears in typing context $\Gamma$, hence the variable $x$ appears also in
  environment $\Gr$ and variable $\D x$ appears in change environment $\D\Gr$.
  Let $v$ be the entry for $\Var{x}$ in $\Gr$ (so that |eval(x) rho = v|), and
  let $\D v$ be the entry for $\Var{\D x}$ in $\D \Gr$ (so that |evalInc(x) rho
  drho = dv|). The entry for $\Var{x}$ in $\Apply{\D \Gr}{\Gr}$ is
  $\Apply{\D v}{v}$ (so that |eval(x) (rho `oplus` drho) = v `oplus` dv|), so we
  have
  \begin{align*}
    & \quad   \Apply
                {\EvalIncWith*{\Var{x}}{\Gr}{\D \Gr}}
                {\EvalWith*{\Var{x}}{\Gr}}\\
    & \quad = \Apply{\D v}{v}\\
    & \quad = \EvalWith{\Var{x}}{\Apply*{\D \Gr}{\Gr}}
  \end{align*}
  as required.

  \Case \Const{c}: We proceed by computing the derivative of
  |eval(c)|, that is |nil(eval(c))|, and rewriting it to
  |evalInc(c)|. Steps use the definitions of (change) evaluation,
  $\beta\eta$-equality and properties of nil changes.
  \begin{equational}
  \begin{code}
           nil(eval(c))
    =      {- by definition of nil changes -}
           eval(c) `ominus` eval(c)
    =      {- by definition of |`ominus`| on functions -}
           \rho drho -> eval(c) (rho `oplus` drho) `ominus` eval(c) rho)
    =      {- by definition of evaluation -}
           \rho drho -> evalConst(c) `ominus` evalConst(c)
    `doe`  {- by properties of nil changes -}
           \rho drho -> nil(evalConst(c))
    =      {- by definition of change evaluation -}
           evalInc(c)
  \end{code}
\end{equational}
  Since nil changes are derivatives, |nil(eval(c))| is the derivative of |eval(c)| as desired. This completes the proof.

  % For constants, the proof is essentially delegated to plugins. We demand that
  % $\Eval{\Const{c}}$ does not depend on $\Gr$ and that $\EvalInc{\Const{c}}$ does not depend on $\Gr$ and $\D \Gr$.
  % Hence, we simply require that $\EvalInc{\Const{c}}$ is a derivative of $\Eval{\Const{c}}$.
  % \pg{Clear this up.}
  % We have
  % \begin{align*}
  %   & \quad   \Apply
  %               {\EvalIncWith*{\Const{c}}{\Gr}{\D \Gr}}
  %               {\EvalWith*{\Const{c}}{\Gr}}\\
  %   & \quad = \Apply
  %               {\EvalIncConst
  %                 {\Const{c}}}
  %               {\EvalConst
  %                 {\Const{c}}}\\
  %   & \quad = \EvalConst
  %               {c} \\
  %   & \quad = \EvalWith
  %               {\Const{c}}
  %               {\Apply*{\D \Gr}{\Gr}}
  % \end{align*}
  % by \cref{def:change-evaluation}.
% \pg{Drop arguments here to update the proof!}
%   \Case \Const{c}{\List{t}}: We have
%   \begin{align*}
%     & \quad   \Apply
%                 {\EvalIncWith*{\Const{c}{\List{t}}}{\Gr}{\D \Gr}}
%                 {\EvalWith*{\Const{c}{\List{t}}}{\Gr}}\\
%     & \quad = \Apply
%                 {\EvalIncConst*
%                   {\Const{c}}
%                   {\List*{\EvalWith{t}{\Gr}}}
%                   {\List*{\EvalIncWith{t}{\Gr}{\D \Gr}}}}
%                 {\EvalConst*
%                   {\Const{c}}
%                   {\List*{\EvalWith{t}{\Gr}}}}\\
%     & \quad = \EvalConst
%                 {c}
%                 {\List*{\EvalIncWith{t}{\Gr}{\D \Gr}}}\\
%     & \quad = \EvalConst
%                 {c}
%                 {\List*{\EvalWith{t}{\Apply*{\D \Gr}{\Gr}}}}\\
%     & \quad = \EvalWith
%                 {\Const{c}{\List{t}}}
%                 {\Apply*{\D \Gr}{\Gr}}
%   \end{align*}
%   by \cref{def:change-evaluation} and
%   the induction hypotheses on the terms $\List{t}$.
\end{optionalproof}

\pg{Examples? Maybe when we introduce evalConst and deriveConst?}
As readers might have noticed, plugins define the derivatives of
constants used by the term transformation $\DERIVE$ but not the
derivatives of constants used by the change semantics. This
simplifies the mechanized proof without weakening resulting
theorems.
To write custom derivatives for the change semantics, we'd have to
define derivatives in the semantic domain, which
requires proving tedious lemmas.

\section{Correctness of differentiation}
\label{sec:differentiate-correct}
\label{sec:erasure}
\DeclareFixedFootnote{\EmptyEmptyNote}{%
To evaluate a closed term $t$, we need no environment entries, so
the empty environment $\EmptyEnv$ suffices:
$\EvalWith*{t}{\EmptyEnv}$ is the value of $t$ in the empty environment, and
$\;\EvalIncSmashWith*{t}{\EmptyEnv}{\EmptyEnv}$
is the value of $t$ using the change semantics, the empty environment and the empty change
environment.}

We can now
prove that the behavior of $\Eval{\Derive{t}}$ is consistent with
the behavior of $\EvalInc{t}$. This leads us to the proof of the
correctness theorem mentioned in the introduction.

The logical relation~\citep[Chapter 8]{Mitchell1996foundations}
of \emph{erasure} captures the idea that an
element of a change structure stays almost the same after we
erase all traces of dependent types from it.

\begin{definition}[Erasure]\label{def:erasure}
Let $\D v \in \Change[\Gt]v$ and $\D v' \in \Eval{\Change\Gt}$.
We say $\D v$ erases to $\D v'$, or
$\Implements[\Gt][v]{\D v}{\D v'}$,
if one of the following holds:
\begin{subdefinition}
\item $\Gt$ is a base type and $\D v=\D v'$.
\item $\Gt=\Fun{\Gs_0}{\Gs_1}$ and for all $w$, $\D w$, $\D w'$
such that $\Implements[\Gs_0][w]{\D w}{\D w'}$, we have
$\Implements[\Gs_1][\App* v w]
{\App*{\App{\D v}w}{\D w}}
{\App*{\App{\D v'}w}{\D w'}}$. \qed
\end{subdefinition}
\end{definition}

Sometimes we shall also say that $\D v \in \Change[\Gt] v$ erases
to a closed term $\HasType{\D t}{\GD t}$, in which case we mean
$\D v$ erases to $(\EvalWith{\D t}{\EmptyEnv})$.\EmptyEmptyNote

The following lemma makes precise what we meant by
``almost the same''.

\begin{lemma}\label{lem:almost-the-same}
Suppose $\Implements[\Gt][v]{\D v}{\D v'}$. If $\UPDATE'$ is the
erased version of the update operator $\UPDATE$ of the change
structure of $\Gt$ (\cref{ssec:change-types}), then
\[
v \UPDATE \D v = v \UPDATE' \D v'. \qed
\]
\end{lemma}

It turns out that $\EvalIncWith{t}$ and $\Derive{t}$ are ``almost the
same''. For closed terms, we make this precise by:

\begin{lemma}
  \label{lem:derive-correct}
If $(\HasType t \Gt)$ is closed, then $\EvalIncSmashWith*{t}\EmptyEnv\EmptyEnv$ erases to
$\Derive{t}$.
\end{lemma}

\begin{optionalproof}
  \pg{Say that we omit the proof because it's extremely boring.
    The recursion scheme seems less obvious than I'd have
    expected since it uses a logical relation but also deals with open terms.}
\end{optionalproof}

We omit for lack of space a more general version of
\cref{lem:derive-correct}, which holds also for open terms, but
requires defining erasure on environments.
The main correctness theorem is a corollary of
\cref{lem:almost-the-same,lem:derive-correct,lem:change-semantics-correct}.

\begin{theorem}[Correctness of differentiation]
\label{thm:main}
Let $\HasType{f}{\Fun \Gs \Gt}$ be a closed term of function
type. For every closed base term $\HasType{s}{\Gs}$ and for every closed change term
$\HasType{\D s}{\Change\Gs}$ such that some change
$\D v\in\Change[\Gs]{\Eval{s}}$ erases to $\D s$, we
have
\[
  \App{f}{\Update*{s}{\D s}}
\cong
  \Update{\App*{f}{s}}{\App*{\App{\Derive f}{s}}{\D s}},
\]
where $\cong$ is denotational equality ($a \cong b$ iff $\Eval{a} = \Eval{b}$).
\end{theorem}
\cref{thm:main} is a more precise restatement of
\cref{eq:correctness}. Requiring the existence of $\D v$ ensures
that $\D s$ evaluates to a change, and not to junk in
$\Eval{\Change\Gs}$.

\begin{oldSec}
\begin{parameter}
  \label{def:implements-base}
  For every base type $\Gi$ and base value $b \in \Eval{\Gi}$,
  base changes $\D b \in \Change[\Gi]{b}$ and values $v' \in
  \Eval{\Change{\Gi}}$ that implement the same change are related
  by $\Implements[\Gi][b]{\D b}{v'}$.
\end{parameter}

\begin{parameter}
  \label{lem:carry-over-base}
  If $\Implements[\Gi][b]{\D b}{v'}$,
  then $\Apply{\D b}{b} = \Apply{v'}{b}$.
\end{parameter}

\begin{parameter}
  \label{lem:diff-implements-diff-base}
  \[\Implements[\Gi][b_1]{\Diff{b_2}{b_1}}{\Diff{b_2}{b_1}}\]
\end{parameter}

\begin{definition}
  \label{def:implements}
  For every type $\Gt$ and value $v \in \Eval{\Gt}$, changes $\D
  v \in \Change[\Gt]{v}$ and values $v' \in \Eval{\Change{\Gt}}$
  that implement the same change are related by
  $\Implements[\Gt][v]{\D v}{v'}$. This relation is defined
  inductively in the structure of $\Gt$ as follows.

  \begin{itemize}
  \item $\Implements[\Gi][b]{\D b}{v'}$ 
    if and only if
    $\Implements[\Gi][b]{\D b}{v'}$.
  \item $\Implements[\Fun{\Gs}{\Gt}][f]{\D f}{f'}$
    if and only if
    \[
      \Implements[\Gs][v]
        {\D v}
        {v'}
      \implies
      \Implements[\Gt][\App*{f}{v}] 
        {\App{\App{\D f}{\D v}}{v}}
        {\App{\App{f'}{v'}}{v}}
    \]
    for all
    $v \in \Eval{\Gs}$,
    $\D v \in \Change[\Gs]{v}$, and
    $v' \in \Eval{\Change{\Gs}}$.
  \end{itemize}
\end{definition}

\begin{lemma}
  \label{lem:carry-over}
  If $\Implements[\Gt][v]{\D v}{v'}$,
  then $\Apply{\D v}{v} = \Apply{v'}{v}$.
  \tr{That should be different $\APPLY$, somehow.}
\end{lemma}
\end{oldSec}

\begin{oldSec}

% \section{An alternative logical relation}

% Proofs of change validity hide a logical relation.

% % As we have seen in this proof, we prove validity of function
% % changes when we introduce new ones.

% % Pre-changes are just the meanings of syntactic changes.
% To introduce function changes, we must prove their validity. Alternatively, in
% this section we define pre-changes without validity requirements and treat
% proofs of validity of a pre-change |dv| for a base value |v| as separate
% entities.
% We then adapt the defininition of |`oplus`| to operate on pre-changes.
% %
% Validity is now a binary logical relation |valid tau dv v|, where |v :
% eval(tau)| and |dv : eval (Dt ^ tau)|, defined as follows:
% \begin{code}
% valid (sigma -> tau) df f =
%   forall a da. ^^ valid (sigma) da a ->
%     (valid (tau) (df a da) (f a) `and`
%       (f `oplus` df) (a `oplus` da) = f a `oplus` df a da)
% valid iota dv v = ...
% \end{code}

% We have a choice between our purely semantics methods and using
% logical relations and more syntactic methods, because:
% \begin{itemize}
% \item we can define function changes to include their validity proofs
% \item logical relations must be defined by induction on types.
%   it's unclear how to define a logical relation in type
%   theory without having an inductive datatype of types (a
%   universe construction \pg{cite}) to perform induction on
%   them. So with syntactic methods it would be hard to use a logical relation to
%   describe validity of changes~\pg{term never
%     introduced}.
% \end{itemize}


\section{Old contents of this section}

\begin{theorem}[correctness of differentiation]
\label{thm:main-findiff}
if $s$ is a closed term of type $\Fun*\Gs\Gt$ and $t_0$, $t_1$
closed terms of type $\Gs$, then
\[
\Eval{\App s{t_1}}
=
\Eval{\Apply
{\App*{\App{\Derive s}{t_0}}{\Diff*{t_1}{t_0}}}
{\App* s{t_0}}}.
\]
\end{theorem}

Although theorem~\ref{thm:main-findiff} is quantified over
programs with all types of inputs and outputs, in practice we
care only about programs that take values of base type (i.\ e.,
numbers, bags and other non-functions) as input
and produce concrete data as output.
\yc{Here be a justification for using the term difference
operator to produce input change. Any idea how to formulate it
succinctly?}

To prove theorem~\ref{thm:main-findiff}, we need two lemmas about derivatives.

First, consider an open term $t$, its derivative
$\Derive{t}$ and an environment $\Gr$ which closes $\Derive{t}$.
Then, $\Derive{t}$ is the change of $t$ with respect to changes
to values denoted by its free variables in an environment $\Gr$.
This property can be expected to hold
%
only if the environment $\Gr$ does not assign garbage to some $\D
x$ that cannot be interpreted as a \emph{valid} change to
$\Gr(x)$. We defer defining when a change is valid for a
value; assuming this notion, we define when an environment
is \emph{consistent}:
%
\pg{variable pairs have not been defined, so I commented out the definition
%
''
if it assigns variable pairs to values valid
for each other.
''}

\begin{definition}
\label{def:consistency}
An environment $\Gr$ is consistent if $\Gr(\D x)$ is a valid
change to $\Gr(x)$ for every variable $x$.
\end{definition}

\begin{lemma}
\label{lem:freevars}
Let $t$ be a well-typed term, $\Gr$ a consistent environment, and
$\Gr'$ the updated version of $\Gr$. Then
\[
\EvalWith{ \Apply{\Derive t}{t} } \Gr = \EvalWith{t}{\Gr'}.
\]
\end{lemma}

Second, the value denoted by the
derivative responds correctly to changes to all future
arguments.

\begin{lemma}
\label{lem:future-args}
Let $t$ be a term of type $\Fun*\Gs\Gt$ and $\Gr$ a consistent
environment. If $\D v\in\Dom{\GD\Gs}$ is a valid change to
$v\in\Dom\Gs$, then
\begin{alignat*}{2}
&&&
(\EvalWith{\Apply{\Derive t}t}{\Gr})(\Apply{\D v}{v})\\
&=\;&&
\Apply
{(\EvalWith{\Derive t}{\Gr})(v)(\D v)}
{(\EvalWith{t}{\Gr})(v)}.
\end{alignat*}
\end{lemma}

Theorem~\ref{thm:main-findiff} is a consequence of lemmas
\ref{lem:freevars}~and \ref{lem:future-args} on closed terms. It
is difficult to prove the two lemmas directly. We shall encode
the idea behind lemma~\ref{lem:future-args} into a logical
relation on the semantic domains that allows us to show both
lemmas by one induction on typing judgements. A logical relation
$R$ has the characteristic that if two functions are related by
$R$, then they map $R$-related arguments to $R$-related results.
Let us call our logical relation the \emph{validity} of changes.
It makes precise the notion of meaningful changes to a value.

\begin{definition}[validity of changes]\label{def:valid}
The validity of changes is the union of relations between
$\Dom{\Gs}$ and $\Dom{\GD\Gs}$ defined inductively on the type
$\Gs$ thus:
\begin{itemize}
\item Every integer in $\Dom{\Int}$ is a valid change to every
integer in $\Dom{\Int}$.
\item Every bag in $\Dom{\Bag}$ is a valid change to every bag in
$\Dom{\Bag}$.
\item
A function $\D f \in \Dom{\Fun\Gs{\Fun{\GD\Gs}{\GD\Gt}}}$ is a
valid change to $f \in \Dom{\Fun\Gs\Gt}$ if for every
$v\in\Dom\Gs$ and every change $\D v\in\Dom{\GD\Gs}$ valid for
$v$ we have
\begin{enumerate}[(1)]
\item the result $\D f(v)(\D v)$ in the domain $\Dom{\GD\Gt}$ is
a valid change to $f(v)\in\Dom\Gt$,
\item the following equation holds:
\[
\Apply*{\D f}{f}(\Apply{\D v}{v}) = \Apply{f(v)}{\D f(v)(\D v)}.
\]
\end{enumerate}
\end{itemize}
\end{definition}

Intuitively, a valid change to a function $f$ must not only
modify the result at every point of input, but also respond to
changes to input in a manner similar to the incremental version
of $f$. We are ready to write down the induction hypothesis
strong enough to give us lemmas \ref{lem:freevars}~and
\ref{lem:future-args}.

\begin{lemma}[inductive reformulation of lemmas
\ref{lem:freevars}~and \ref{lem:future-args}]
\label{lem:hypothesis}
Let $t$ be a well-typed term, $\Gr$ a consistent environment and
$\Gr'$ the updated version of $\Gr$.
\begin{enumerate}[(i)]
\item\label{itm:freevars}
We have
$\EvalWith*{t}{\Gr'}=
\Apply{\EvalWith*{\Derive t}\Gr}{\EvalWith*{t}\Gr}$.
\item\label{itm:future-args}
$\EvalWith*{\Derive t}\Gr$ is a valid change to
$\EvalWith*{t}\Gr$.
\end{enumerate}
\end{lemma}

\begin{proof}[Proof fragment]
We prove it by induction on a typing judgement of the term $t$.
Here we show only the most nontrivial case where $t=\Lam x s$.

Suppose $\Gs\r\Gt$ is the type of $t$. Choose arbitrary $v\in
\Dom\Gs$ and let $\D v\in\Dom{\GD\Gs}$ be a valid change to $v$.
Define these shorthands:
\begin{align*}
f     & = \mean[\Gr]{\Lam{x} s} \\
\D f  & = \mean[\Gr]{\Lam{x}{\Lam{\D x}{\Derive s}}} \\
v'    & = \Apply{\D v}v,\\
\Gr_1 & = \Gr[x\mapsto v,\D x\mapsto\D v]
\end{align*}

For part~\itref{itm:freevars}, let
\begin{align*}
\Gr_2  & = \Gr[x\mapsto v,\D x\mapsto \Diff vv],\\
\Gr_2' & = \Gr'[x\mapsto v',\D x\mapsto \Diff{v'}{v'}].
\end{align*}
It is clear that $\Gr_2'$ is the updated version of $\Gr_2$. By
induction hypothesis on $s$,
\begin{align*}
\mean*[\Gr']t(v)
& = \mean[\Gr_2']s\\
& = \Apply{\mean*[\Gr_2]{\Derive s}}{\mean*[\Gr_2]s}\\
& = \Apply{\D f(v)(\Diff vv)}{f(v)}\\
& = \Apply*{\mean*[\Gr]{\Derive t}}{\mean*[\Gr]t}(v).
\end{align*}
Since $v$ is arbitrary, $\mean*[\Gr']t$ and
$\Apply*{\mean*[\Gr]{\Derive t}}{\mean*[\Gr]t}$ are equal as
functions.

For part~\itref{itm:future-args},
notice that
\begin{align*}
\D f(v')(\Diff{v'}{v'})
& = \mean[\Gr[x\mapsto v',\D x\mapsto\Diff{v'}{v'}]]{\Derive
s},\\
f(v')
& = \mean[\Gr[x\mapsto v']]s,
\end{align*}
and by induction hypothesis on $s$ and lemma \pg{was ref{lem:apply-diff}},
\begin{align*}
(\Apply{\D f}f)(\Apply{\D v}v)
& = (\Apply{\D f}f)(v')\\
& = \Apply{\D f(v')(\Diff{v'}{v'})}{f(v')}\\
& = \mean[\Gr'[x\mapsto\Apply{\Diff*{v'}{v'}}{v'}]]{s}\\
& = \mean[\Gr'[x\mapsto\Apply{\D v}{v}]]s\\
& = \Apply{\mean*[\Gr_1]{\Derive s}}
          {\mean*[\Gr_1]s}\\
& = \Apply{\D f(v)(\D v)}{f(v)}.
\end{align*}
Together with the validity of $\D f(v)(\D v)$ as a change to
$f(v)$ given by the induction hypothesis on $s$, we obtain
part~\itref{itm:future-args} of the lemma.
\end{proof}

%The reader may find a more complete version of the development of
%this section in appendix~\ref{sec:STLC-correct}.

Although we use a fixed set of primitives in the formalization,
the proof of the main correctness theorem does not depend on the
primitives beyond that their derivatives satisfy the
theorem themselves. It is possible to generalize the most
important induction steps, those on abstractions and
applications, to calculi with any suitable primitives. Thus, the
choice of primitives is unimportant; it serves mostly as an
understanding aid. A planned future work is to express this idea
in Agda by making our calculi and proofs parametric in term
constructors. \yc{or simply parametric in terms of primitives?}
\yc{This paragraph is intended to discourage objections of our
choice of primitives. Where is the best place to put it?}

\yc{If we have examples involving merge and sum alone, it is
possible to solve them right here.}

\end{oldSec}
