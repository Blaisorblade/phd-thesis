% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

%{
\begin{figure}[h]
  \small
\begin{subfigure}[c]{0.5\textwidth}
\begin{code}
  p     ::=  succ | add | ...
  m, n  ::=  ... -- numbers
  c     ::=  n | ...
  w     ::=  x | \x -> t | pair w w | c
  s, t  ::=  w | w w | p w | lett x = t in t
  v     ::=  rho[\x -> t] | pair v v | c
  rho   ::=  x1 := v1 , ... , xn := vn
\end{code}
\caption{Base terms (\ilcUntau).}
\label{sfig:anf-syntax}
\end{subfigure}
%
\hfill
%
\begin{subfigure}[c]{0.5\textwidth}
\begin{code}
  dc      ::=  0
  dw      ::=  dx | \x dx -> dt | pair dw dw | dc
  ds, dt  ::=  dw | dw w dw | p w dw |
               lett x = t; dx = dt in dt
  dv      ::=  rho `stoup` drho[\x dx -> dt] | pair dv dv | dc
  drho    ::=  dx1 := dv1 , ..., dxn := dvn
\end{code}
\caption{Change terms (\dilcUntau).}
\label{sfig:anf-change-syntax}
\end{subfigure}

\begin{subfigure}[t]{0.5\textwidth}
\begin{align*}
  |deriveConst n| &= |0|\\
  \\
  |derive x| &= |dx| \\
  |derive(\x -> t)| &= |\x dx -> derive(t)| \\
  |derive (pair wa wb)| &= |pair (derive wa) (derive wb)|\\
  |derive c| &= |deriveConst c|\\
  \\
  |derive(wf wa)| &= |(derive wf) wa (derive wa)| \\
  |derive(p w)| &= |p w (derive w)| \\
  |derive(lett x = s in t)| &= |lett x = s; dx = derive s in derive t|
\end{align*}
\caption{Differentiation.}
%\caption{Differentiation, from base terms to change terms}
\label{sfig:anf-derive}
\end{subfigure}
%
\begin{subfigure}[t]{0.5\textwidth}
\begin{code}
  tau ::= Nat | taua `times` taub | sigma -> tau

  Dt^Nat                  = Nat
  Dt^(taua `times` taub)  = Dt^taua `times` Dt^taub
  Dt^(sigma -> tau)       = sigma -> Dt^sigma -> Dt^tau

  Dt^emptyCtx             = emptyCtx
  Dt^(Gamma, x : tau)     = Dt^Gamma, dx : Dt^tau
\end{code}
\caption{Types and contexts.}
\label{sfig:anf-types}
\end{subfigure}

\caption{ANF $\lambda$-calculus: \ilcUntau{} and \dilcUntau{}.}
\label{fig:anf-lambda-calculus}
\end{figure}

\begin{figure}
  \footnotesize
\begin{subfigure}[t]{\textwidth}
\begin{typing}
\Axiom[T-Lit]{|`vdashConst` n : Nat|}

\Axiom[T-Succ]{|`vdashPrim` succ : Nat -> Nat|}

\Axiom[T-Add]{|`vdashPrim` add : (Nat `times` Nat) -> Nat|}
\end{typing}
\begin{typing}
\noindent
\Rule[T-Var]
  {|x : tau `elem` Gamma|}
  {|Gamma /- x : tau|}

\Rule[T-Const]
 {|`vdashConst` c : tau|}
 {|Gamma /- c : tau|}

\raisebox{0.5\baselineskip}{\fbox{|Gamma /- t : tau|}}

\Rule[T-App]
  {|Gamma /- wf : sigma -> tau|\\
  |Gamma /- wa : sigma|}
  {|Gamma /- wf wa : tau|}

\Rule[T-Lam]
  {|Gamma , x : sigma /- t : tau|}
  {|Gamma /- \(x : sigma) -> t : sigma -> tau|}

\Rule[T-Let]
  {|Gamma /- s : sigma|\\
  |Gamma , x : sigma /- t : tau|}
  {|Gamma /- lett x = s in t : tau|}

\Rule[T-Pair]
  {|Gamma /- wa : taua|\\
  |Gamma /- wb : taub|}
  {|Gamma /- pair wa wb : taua `times` taub|}

\Rule[T-Prim]
  {|`vdashPrim` p : sigma -> tau|\\
   |Gamma /- w : sigma|}
 {|Gamma /- p w : tau|}
\end{typing}
\caption{\ilcTau{} base typing.}
\label{sfig:anf-base-typing}
\end{subfigure}

\begin{subfigure}[t]{\textwidth}
\begin{typing}
\Rule[T-DVar]
  {|x : tau `elem` Gamma|}
  {|Gamma /-- dx : tau|}

\Rule[T-DConst]
 {|`vdashConst` c : Dt^tau|}
 {|Gamma /-- c : tau|}

\raisebox{0.5\baselineskip}{\fbox{|Gamma /-- dt : tau|}}

\Rule[T-DApp]
  {|Gamma /-- dwf : sigma -> tau|\\
    |Gamma /- wa : sigma|\\
    |Gamma /-- dwa : sigma|}
  {|Gamma /-- dwf wa dwa : tau|}

\Rule[T-DLet]{
  |Gamma /- s : sigma|\\
  |Gamma /-- ds : sigma|\\
  |Gamma , x : sigma /-- dt : tau|}
  {|Gamma /-- lett x = s ; dx = ds in dt : tau|}

\Rule[T-DLam]
  {|Gamma , x : sigma /-- dt : tau|}
  {|Gamma /-- \x dx -> dt : sigma -> tau|}

\Rule[T-DPair]
  {|Gamma /-- dwa : taua|\\
  |Gamma /-- dwb : taub|}
  {|Gamma /-- pair dwa dwb : taua `times` taub|}

\Rule[T-DPrim]
  {|`vdashPrim` p : sigma -> tau|\\
    |Gamma /- w : sigma|\\
    |Gamma /-- dw : sigma|}
 {|Gamma /-- p w dw : tau|}
\end{typing}
\caption{\dilcTau{} change typing. Judgement |Gamma /-- dt : tau| means that variables from
  both |Gamma| and |Dt^Gamma| are in scope in |dt|, and the final type is in fact
  |Dt^tau|.}
\label{sfig:anf-change-typing}
\end{subfigure}

\caption{ANF $\lambda$-calculus, \ilcTau{} and \dilcTau{} type system.}
\label{fig:anf-lambda-calculus-typing}
\end{figure}

%format ns = n "_s"
%format nt = n "_t"
%format vs = v "_s"
%format vt = v "_t"

\begin{figure}
  \footnotesize
\begin{subfigure}[t]{\textwidth}
\begin{typing}
  \Axiom[E-Prim]{|ibseval (p w) rho 1 (evalPrim p (evalVal w rho))|}

  \Axiom[E-Val]{|ibseval w rho 0 (evalVal w rho)|}

  \raisebox{0.5\baselineskip}{\fbox{|ibseval t rho n v|}}

  \Rule[E-Let]{|ibseval s rho ns vs|\\|ibseval t (rho, x := vs) nt vt|}{|ibseval (lett x = s in t) rho (1 + ns + nt) vt|}

  \Rule[E-App]{
    |ibseval wf rho 0 vf|\\
    |ibseval wa rho 0 va|\\
    |vapply vf va (downto n) v|
  }{|ibseval (wf wa) rho (1 + n) v|}
\end{typing}
\begin{code}
  vapply (rho'[\x -> t]) va  = envpair ((rho', x := va)) t

  evalVal x rho              = rho(x)
  evalVal (\x -> t) rho      = rho[\x -> t]
  evalVal (pair wa wb) rho   = pair (evalVal wa rho) (evalVal wb rho)
  evalVal c rho              = c

  evalPrim succ n            = 1 + n
  evalPrim add (m, n)        = m + n
\end{code}
\caption{Base semantics.
  Judgement |envpair rho t (downto n) v| says that |envpair rho t|, a pair of
  environment |rho| and term |t|, evaluates to value |v| in |n| steps, and
  |vapply vf va (downto n) v| constructs the pair to evaluate via |vapply vf va|.}
\label{sfig:anf-base-semantics}
\end{subfigure}

\begin{subfigure}[t]{\textwidth}
\begin{typing}
  \Axiom[E-DVal]{|dbseval dw rho drho (devalVal dw rho drho)|}

\raisebox{0.5\baselineskip}{\fbox{|dbseval dt rho drho dv|}}

  \Axiom[E-DPrim]{|dbseval (p w dw) rho drho
    (devalPrim p (evalVal w rho) (devalVal dw rho drho))|}

  \Rule[E-DApp]{%
    |dbseval dwf rho drho dvf|\\
    |bseval  wa  rho va|\\
    |dbseval dwa rho drho dva|\\
    |dvapply dvf va dva ddown dv|}
  {|dbseval (dwf wa dwa) rho drho dv|}

  \Rule[E-DLet]{
    |bseval  s  rho vs|\\
    |dbseval ds rho drho dvs|\\
    |dbseval dt (rho, x := vs) (drho; dx := dvs) dvt|}
  {|dbseval (lett x = s; dx = ds in dt) rho drho dvt|}
\end{typing}
\begin{code}
  dvapply (rho' `stoup` drho' [\x dx -> dt]) va dva  = denvpair ((rho', x := va)) ((drho' , dx := dva)) dt

  devalVal dx rho drho                               = drho(dx)
  devalVal (\x dx -> dt) rho drho                    = rho `stoup` drho[\x dx -> dt]
  devalVal (pair dwa dwb) rho drho                   = pair (devalVal dwa rho drho) (devalVal dwb rho drho)
  devalVal c rho drho                                = c

  devalPrim succ n dn                                = dn
  devalPrim add (pair m n) (pair dm dn)              = dm + dn
\end{code}
\caption{Change semantics.
  Judgement |denvpair rho drho t ddown dv| says that |denvpair rho drho dt|, a triple of environment
  |rho|, change environment |drho| and change term |t|, evaluates to change value |dv|. and |dvapply dvf va dva
  ddown dv| constructs the triple to evaluate via |dvapply dvf va dva|.}
\label{sfig:anf-change-semantics}
\end{subfigure}

\caption{ANF $\lambda$-calculus (\ilcUntau{} and \dilcUntau{}), CBV semantics.}
\label{fig:anf-lambda-calculus-semantics}
\end{figure}
%}
