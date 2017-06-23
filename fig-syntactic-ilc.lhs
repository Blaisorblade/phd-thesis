% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\begin{figure}[h]
  \small
\begin{subfigure}[c]{0.5\textwidth}
\begin{code}
  p     ::=  succ | add | ...
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
\caption{Base typing for \ilcTau{}.}
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
\caption{Change typing for \dilcTau{}. Judgement |Gamma /-- dt : tau| means that variables from
  both |Gamma| and |Dt^Gamma| are in scope in |dt|, and the final type is in fact
  |Dt^tau|.}
\label{sfig:anf-change-typing}
\end{subfigure}

\caption{ANF $\lambda$-calculus, type system: \ilcTau{} amd \dilcTau{}.}
\label{fig:anf-lambda-calculus-typing}
\end{figure}

\begin{figure}
  \footnotesize
\begin{subfigure}[t]{\textwidth}
\begin{typing}
  \Axiom[E-Prim]{|ibseval (p w) rho 1 (evalPrim p (evalVal w rho))|}

  \Axiom[E-Val]{|ibseval w rho 0 (evalVal w rho)|}

  \raisebox{0.5\baselineskip}{\fbox{|ibseval t rho n v|}}

  \Rule[E-Let]{|ibseval t1 rho n1 v1|\\|ibseval t2 (rho, x := v1) n2 v2|}{|ibseval (lett x = t1 in t2) rho (1 + n1 + n2) v2|}

  \Rule[E-App]{|ibseval w1 rho 0 rho'[\x -> t]|\\|ibseval w2 rho 0 v2|\\|ibseval t (rho', x := v2) n v|}{|ibseval (w1 w2) rho (1 + n) v|}
\end{typing}
\begin{code}
  evalVal x rho             = rho(x)
  evalVal (\x -> t) rho     = rho[\x -> t]
  evalVal (pair w1 w2) rho  = pair (evalVal w1 rho) (evalVal w2 rho)
  evalVal c rho             = c

  evalPrim succ n           = 1 + n
  evalPrim add (n1, n2)     = n1 + n2
\end{code}
\caption{Base semantics.}
\label{sfig:anf-base-semantics}
\end{subfigure}

\begin{subfigure}[t]{\textwidth}
\begin{typing}
  \Axiom[E-DVal]{|dbseval dw rho drho (devalVal dw rho drho)|}

\raisebox{0.5\baselineskip}{\fbox{|dbseval dt rho drho dv|}}

  \Axiom[E-DPrim]{|dbseval (p w dw) rho drho
    (devalPrim p (evalVal w rho) (devalVal dw rho drho))|}

  \Rule[E-DApp]{%
    |dbseval dw1 rho drho (rho' `stoup` drho'[\x dx -> dt])|\\
    |bseval  w2  rho v2|\\
    |dbseval dw2 rho drho dv2|\\
    |dbseval dt  (rho', x := v2) (drho', dx := dv2) dv|}
  {|dbseval (dw1 w2 dw2) rho drho dv|}

  \Rule[E-DLet]{
    |bseval  t1  rho v1|\\
    |dbseval dt1 rho drho dv1|\\
    |dbseval dt2 (rho, x := v1) (drho; dx := dv1) dv2|}
  {|dbseval (lett x = t1; dx = dt1 in dt2) rho drho dv2|}
\end{typing}
\begin{code}
  devalVal dx rho drho                       = drho(dx)
  devalVal (\x dx -> dt) rho drho            = rho `stoup` drho[\x dx -> dt]
  devalVal (pair dw1 dw2) rho drho           = pair (devalVal dw1 rho drho) (devalVal dw2 rho drho)
  devalVal c rho drho                        = c

  devalPrim succ n dn                        = dn
  devalPrim add (pair n1 n2) (pair dn1 dn2)  = dn1 + dn2
\end{code}
\caption{Change semantics.}
\label{sfig:anf-change-semantics}
\end{subfigure}

\caption{ANF $\lambda$-calculus (\ilcUntau{} and \dilcUntau{}), CBV semantics.}
\label{fig:anf-lambda-calculus-semantics}
\end{figure}