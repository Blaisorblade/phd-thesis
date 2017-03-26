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
\caption{Change types}
\label{fig:change-types}
\label{fig:correctness:change-types}
\end{subfigure}
%
\hfill
%
\begin{subfigure}[c]{0.5\textwidth}
\RightFramedSignature{\Delta\Gamma}
\begin{align*}
  \Delta\EmptyContext &= \EmptyContext \\
  \Delta\Extend*{x}{\tau} &= \Extend[\Extend[\Delta\Gamma]{x}{\tau}]{\D x}{\Delta\tau}
\end{align*}
\caption{Change contexts}
\label{fig:correctness:change-contexts}% \pg{Does not match the original one!}
\end{subfigure}
\vfill

\begin{subfigure}[c]{0.5\textwidth}
  \RightFramedSignature{|derive(t)|}
\begin{align*}
  |derive(\x -> t)| &= |\x dx -> derive(t)| \\
  |derive(s t)| &= |derive(s) t (derive(t))| \\
  |derive(x)| &= |dx| \\
  |derive(c)| &= |deriveConst(c)|
\end{align*}
\caption{Differentiation}
\label{fig:correctness:derive}
\end{subfigure}
%
\begin{subfigure}[c]{0.5\textwidth}
  \begin{typing}
    \Rule[Derive]
    {|Gamma /- t : tau|}
    {|Dt ^ Gamma /- derive(t) : Dt ^ tau|}
\end{typing}
\subcaption{Differentiation typing}
\label{fig:derive}
\end{subfigure}
%
\begin{subfigure}[c]{1.0\textwidth}
  \RightFramedSignature{|fromto tau v1 dv v2|\text{ with }|v1, v2 : eval(tau), dv : eval(Dt^tau)|}
\begin{align*}
  |fromto iota v1 dv v2| &= \ldots \\
  |fromto (sigma -> tau) f1 df f2| &=
  |forall a1 a2 : eval(sigma), da : eval(Dt ^ sigma) .| \\
  &\text{if }|fromto (sigma) a1 da a2| \text{ then }
    |fromto (tau) (f1 a1) (df a1 da) (f2 a2)|
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

\caption{Validity}
\label{fig:validity}
\label{fig:correctness:change-environments}
\end{subfigure}

\vskip 2\baselineskip
\begin{subfigure}[c]{1.0\textwidth}
  \centering
  \deriveCorrect*
\end{subfigure}
\caption{Defining differentiation and proving it correct.}
  \label{fig:differentiation}
\end{figure}
