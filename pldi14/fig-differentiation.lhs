% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\begin{figure}

  \begin{subfigure}[c]{0.5\textwidth}
\RightFramedSignature{\Delta\Gt}
\begin{align*}
  |Dt ^ iota| &= \ldots\\
  |Dt ^ (sigma -> tau)| &= |sigma -> Dt ^ sigma -> Dt ^ tau|
\end{align*}
\caption{Change types (\cref{def:change-types}).}
\label{fig:change-types}
\label{fig:correctness:change-types}
\end{subfigure}
%
\hfill
%
\begin{subfigure}[c]{0.45\textwidth}
\RightFramedSignature{\Delta\Gamma}
\begin{align*}
  \Delta\EmptyContext &= \EmptyContext \\
  \Delta\Extend*{x}{\tau} &= \Extend[\Extend[\Delta\Gamma]{x}{\tau}]{\D x}{\Delta\tau}
\end{align*}
\caption{Change contexts (\cref{def:change-contexts}).}
\label{fig:correctness:change-contexts}
\end{subfigure}
\vskip \baselineskip

\begin{subfigure}[c]{0.5\textwidth}
  \RightFramedSignature{|derive(t)|}
 \deriveDefCore
\caption{Differentiation (\cref{def:derive}).}
\label{fig:correctness:derive}
\end{subfigure}
%
\hfill
%
\begin{subfigure}[c]{0.45\textwidth}
  \begin{typing}
    \Rule[Derive]
    {|Gamma /- t : tau|}
    {|Dt ^ Gamma /- derive(t) : Dt ^ tau|}
\end{typing}
\caption{Differentiation typing (\cref{lem:derive-typing}).}
\label{fig:derive}
\end{subfigure}

\vskip \baselineskip
\begin{subfigure}[c]{1.0\textwidth}
  \RightFramedSignature{|fromto tau v1 dv v2|\text{ with }|v1, v2 : eval(tau), dv : eval(Dt^tau)|}
\begin{align*}
  |fromto iota v1 dv v2| &= \ldots \\
  |fromto (sigma -> tau) f1 df f2| &=
  |forall (fromto sigma a1 da a2) . ^^ fromto tau (f1 a1) (df a1 da) (f2 a2)|
  \end{align*}

  \RightFramedSignature{|fromto Gamma rho1 drho rho2|\text{ with }|rho1, rho2 : eval(Gamma), drho : eval(Dt^Gamma)|}
\begin{typing}
  \Axiom
  {\validfromto{\EmptyContext}{\EmptyEnv}{\EmptyEnv}{\EmptyEnv}}

  \Rule{|fromto Gamma rho1 drho rho2|\\
    |fromto tau a1 da a2|}{
  \validfromto{\Extend{x}{\tau}}
  {\ExtendEnv*[\rho_1]{x}{a_1}}
  {\ExtendEnv*[\ExtendEnv[\D\rho]{x}{a_1}]{dx}{\D{a}}}
  {\ExtendEnv*[\rho_2]{x}{a_2}}}
\end{typing}

\caption{Validity (\cref{def:ch-validity,def:env-ch-validity}).}
\label{fig:validity}
\label{fig:correctness:change-environments}
\end{subfigure}

\vskip 2\baselineskip
\begin{subfigure}[c]{1.0\textwidth}
  \centering
If |Gamma /- t : tau| then
% \[|fromto (eval(Gamma) -> eval(tau)) (eval t) (evalInc t) (eval t)|\]
% that is
\[|forall (fromto Gamma rho1 drho rho2) . ^^
  fromto tau (eval(t) rho1) (eval(derive(t)) drho) (eval(t) rho2)|.\]
\caption{Correctness of |derive(param)| (from \cref{thm:derive-correct}).}
\label{fig:correctness:derive-correct}
\end{subfigure}
\pg{Say this is a summary of definitions throughout the chapter.}
\caption{Defining differentiation and proving it correct. The rest of this chapter explains and motivates the above definitions.}
  \label{fig:differentiation}
\end{figure}
