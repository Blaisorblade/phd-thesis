% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes.fmt

\appendix
\chapter{More on our formalization}
\section{Mechanizing plugins modularly and limitations}
\label{sec:modularity-limits}
Next, we discuss our mechanization of language plugins in Agda, and its
limitations. For the concerned reader, we can say these limitations affect
essentially how modular our proofs are, and not their cogency.

In essence, it's not possible to express in Agda the correct interface for
language plugins, so some parts of language plugins can't be modularized as desirable.
Alternatively, we can mechanize any fixed language plugin together with
the main formalization, which is not truly modular, or mechanize a core
formulation parameterized on a language plugin, which that runs into a few
limitations, or encode plugins so they can be modularized and deal with encoding
overhead.

This section requires some Agda knowledge not provided here, but
we hope that readers familiar with both Haskell and Coq will be
able to follow along.

Our mechanization is divided into multiple Agda modules. Most
modules have definitions that depend on language plugins,
directly or indirectly. Those take definitions from language
plugins as \emph{module parameters}.

For instance, STLC object types are formalized through Agda type
|Type|, defined in module |Parametric.Syntax.Type|. The latter is
parameterized over |Base|, the type of base types.

For instance, |Base| can support a base type of integers, and a
base type of bags of elements of type |iota| (where |iota :
Base|). Simplifying a few details, our definition is equivalent
to the following Agda code:
\begin{code}
module Parametric.Syntax.Type (Base : Set) where
  data Type : Set where
    base  :  ^^(iota : Base)                   -> Type
    _=>_  :  ^^(sigma : Type)  -> (tau : Type) -> Type

-- Elsewhere, in plugin:

data Base : Set where
  baseInt  :  ^^Base
  baseBag  :  ^^(iota : Base) -> Base
-- ...
\end{code}

But with these definitions, we only have bags of elements of base type. If
|iota| is a base type, |base (baseBag iota)| is the type of bags with elements
of type |base iota|. Hence, we have bags of elements of base type. But we don't
have a way to encode |Bag tau| if |tau| is an arbitrary non-base type, such as
|base baseInt => base baseInt| (the encoding of object type |Int -> Int|).
%
Can we do better? If we ignore modularization, we can define types through the
following mutually recursive datatypes:

\begin{code}
mutual
  data Type : Set where
    base  :  ^^(iota : Base Type)              -> Type
    _=>_  :  ^^(sigma : Type)  -> (tau : Type) -> Type

  data Base : Set where
    baseInt  :  ^^Base
    baseBag  :  ^^(iota : Type) -> Base
\end{code}

So far so good, but these types have to be defined together. We
can go a step further by defining:

\begin{code}
mutual
  data Type : Set where
    base  :  ^^(iota : Base Type)              -> Type
    _=>_  :  ^^(sigma : Type)  -> (tau : Type) -> Type

  data Base (Type : Set) : Set where
    baseInt  :  ^^Base Type
    baseBag  :  ^^(iota : Type) -> Base Type
\end{code}

Here, |Base| takes the type of object types as a parameter, and
|Type| uses |Base Type| to tie the recursion. This definition
still works, but only as long as |Base| and |Type| are defined together.

If we try to separate the definitions of |Base| and |Type| into
different modules, we run into trouble.
\begin{code}
module Parametric.Syntax.Type (Base : Set -> Set) where
  data Type : Set where
    base  :  ^^(iota : Base Type)              -> Type
    _=>_  :  ^^(sigma : Type)  -> (tau : Type) -> Type

-- Elsewhere, in plugin:

data Base (Type : Set) : Set where
  baseInt  :  ^^Base Type
  baseBag  :  ^^(iota : Type) -> Base Type
\end{code}

Here, |Type| is defined for an arbitrary function on types |Base
: Set -> Set|. However, this definition is rejected by Agda's
\emph{positivity checker}. Like Coq, Agda forbids defining
datatypes that are not strictly positive, as they can introduce
inconsistencies.
\pg{Add the ``Bad'' example from Agda's wiki, with link for credit.}

The above definition of |Type| is \emph{not} strictly positive,
because we could pass to it as argument |Base = \tau -> (tau ->
tau)| so that |Base Type = Type -> Type|, making |Type| occur in
a negative position. However, the actual uses of |Base| we are
interested in are fine. The problem is that we cannot inform the
positivity checker that |Base| is supposed to be a strictly
positive type function, because Agda doesn't supply the needed
expressivity.

This problem is well-known. It could be solved if Agda function spaces supported
positivity annotations,\footnote{As discussed in
  \url{https://github.com/agda/agda/issues/570} and
  \url{https://github.com/agda/agda/issues/2411}.} or by encoding a universe of
strictly-positive type constructors. This encoding is not fully transparent and
adds hard-to-hide noise to
development~\citep{Schwaab2013modular}.\footnote{Using pattern synonyms and
  \texttt{DISPLAY} pragmas might successfully hide this noise.}
Few alternatives remain:
\begin{itemize}
\item We can forbid types from occurring in base types, as we did in our
  original paper~\citep{CaiEtAl2014ILC}. There we did not discuss at all a
  recursive definition of base types.
\item We can use the modular mechanization, disable positivity checking and risk
  introducing inconsistencies. We tried this successfully in a branch of that
  formalization. We believe we did not introduce inconsistencies in that branch
  but have no hard evidence.
\item We can simply combine the core formalization with a sample plugin. This is
  not truly modular because the core modularization can only be reused by
  copy-and-paste. Moreover, in dependently-typed languages the content of a
  definition can affect whether later definitions typecheck, so alternative
  plugins using the same interface might not typecheck.\footnote{Indeed, if
    |Base| were not strictly positive, the application |Type Base| would be
    ill-typed as it would fail positivity checking, even though |Base: Set ->
    Set| does not require |Base| to be strictly positive.}
\end{itemize}

Sadly, giving up on modularity altogether appears the more conventional choice.
Either way, as we claimed at the outset, these modularity concerns only limit
the modularity of the mechanized proofs, not their cogency.
