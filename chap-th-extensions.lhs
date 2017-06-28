% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\chapter{Extensions and theoretical discussion}
\label{ch:misc-extensions}
In this chapter we collect discussion of a few additional topics related to ILC.

\section{A change structure for sums}
\label{sec:chs-sums}
We can define change structures on disjoint sums |A + B|, given
change structures on |A| and |B|.
\pg{resume.}

\section{Language plugins for products and sums}
\label{ch:prod-sums}

In this section, we show language plugins for sum and product
types.

\pg{Extend by showing the base semantics of these plugins.}
We give ways to give change structures for products and sums.
As primitives, we use the introduction and elimination forms for
these types. Then, we show how to obtain derivatives for these
primitives.

\pg{Consider recursive types, and recursion?}



\section{General recursion}
\label{sec:general-recursion}
\pg{write, and put somewhere. Use the example with |map| on lists.}

This section discusses informally how to differentiate terms
using general recursion and what is the behavior of the resulting terms.

\subsection{Differentiating general recursion}
%format letrec = "\mathbf{letrec}"
%format fix = "\mathbf{fix}"

Earlier we gave a rule for deriving (non-recursive) |lett|:
\begin{code}
derive(lett x = t1 in t2) =
  lett  x = t1
        dx = derive(t1)
  in    derive(t2)
\end{code}
It turns out that we can use the same rule also for recursive
|lett|-bindings, which we write here |letrec| for clarity:
\begin{code}
derive(letrec x = t1 in t2) =
  lett  x = t1
        dx = derive(t1)
  in    derive(t2)
\end{code}

\pg{Reorganize. This order makes no sense.}
\begin{example}
  In \cref{ex:syn-changes-map} we presented a derivative for
  |map|.
  We now rewrite |map| using fixpoint combinators and derive the
  |dmap| applying the rule for deriving |fix|.
% \begin{code}
% map f = fix go
%   where
%     go self Nil = Nil
%     go self (Cons x xs) = Cons (f x) (self xs)
% \end{code}

% Applying the derivation rules, we get that
% |dmap f df = fix ((derive go) (fix go))|,
% and since |fix go = map f| we can write:
% \begin{code}
% dmap f df = fix (dgo (map f))
%   where
%     dgo self dself Nil Nil = Nil
%     dgo self dself (Cons x xs) (Cons dx dxs) =
%       Cons (df x dx) (dself xs dxs)
% \end{code}
We can finally show that
\begin{code}
dmap f df Nil Nil = Nil
dmap f df (Cons x xs) (Cons dx dxs) =
  Cons (df x dx) (dmap f df xs dxs)
\end{code}
\end{example}

\subsection{Justification}
However, we justify this rule using fixpoint operators.

Let's consider STLC extended with a family of standard fixpoint
combinators $\Varid{fix}_{|tau|}|: (tau -> tau) -> tau|$, with
|fix|-reduction defined by equation |fix f -> f (fix f)|; we
search for a definition of |derive (fix f)|.

Using informal equational reasoning, if a correct definition of
|derive (fix f)| exists, it must be
\begin{code}
  derive (fix f) = fix ((derive f (fix f)))
\end{code}
\pg{use |`cong`|?}

We can proceed as follows:
% We recall that the derivative of a closed term is its nil change.
\begin{equational}
\begin{code}
   derive (fix f)
=  {- imposing that |derive| respects |fix|-reduction here -}
   derive (f (fix f))
=  {- using rules for |derive| on application -}
   (derive f) (fix f) (derive (fix f))
\end{code}
\end{equational}

This is a recursive equation in |derive (fix f)|, so we can try
to solve it using |fix| itself:
\begin{code}
  derive (fix f) = fix (\dfixf -> (derive f (fix f) dfixf))
\end{code}

Indeed, this rule gives a correct derivative.
Formalizing our reasoning using denotational semantics would
presumably require the use of domain theory. We leave
such a formalization for future work.
However, we do prove correct a variant of |fix| in
\cref{ch:bsos}, but using operational semantics.

% In particular
% \begin{code}
%    derive (fix (\ff -> t))
% =
%    fix (\dff -> (derive (\ff -> t) (fix (\ff -> t)) dff))
% =
%    fix (\dff -> derive t [ff := fix (\ff -> t)])
% \end{code}

% % |let ffact = fix (\ffact n -> n * ffact (n - 1)) in t2 =
% % letrec ffact = \n -> n * ffact (n - 1) in t2|
% % |
% % This rule is equivalent

% We can also derive the rule for |letrec|, based on this rewrite rule:
% |let ff = fix (\ff -> t) in t2 = letrec ff = t in t2|.
% We proceed as follows:
% \begin{equational}
% \begin{code}
%    derive(letrec ff = t in t2)
% =  {- -}
%    derive(lett ff = fix (\ff -> t) in t2)
% =  {- deriving |let| -}
%    let
%      ff   = fix (\ff -> t)
%      dff  = derive (fix (\ff -> t))
%    in derive t2
% =  {- deriving |fix| -}
%    let
%      ff   = fix (\ff -> t)
%      dff  = fix (\dff -> derive t [ff := (fix (\ff -> t))])
%    in derive t2
% =  {- deinline binding of |ff| -}
%    let
%      ff   = fix (\ff -> t)
%      dff  = fix (\dff -> derive t)
%    in derive t2
% =  {- |let| to |letrec| -}
%    letrec
%      ff   = t
%    in let
%      dff  = fix (\dff -> derive t)
%    in derive t2
% =  {- |let| to |letrec| -}
%    letrec
%      ff   = t
%      dff  = derive t
%    in derive t2
% \end{code}
% \end{equational}
