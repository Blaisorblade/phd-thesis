% Emacs, this is -*- latex -*-!
%include polycode.fmt
%include changes-popl.fmt

\section{Related work}
\label{sec:cts-rw}
Of all research on incremental computation in both programming languages and
databases~\citep{Gupta99MMV,Ramalingam93}, we discuss the most closely related works.
\begin{poplForThesis}
Other related work, more closely to cache-transfer style, is
discussed in \cref{sec:rw}.
\end{poplForThesis}

\paragraph{Previous work on cache-transfer-style}
\citet{Liu00}'s work has been the fundamental inspiration to this work, but
her approach has no correctness proof and is restricted to a first-order untyped
language (in part because no absence analysis for higher-order languages was
available). Moreover, while the idea of cache-transfer-style is similar, it's
unclear if her approach to incrementalization would extend to higher-order
programs.
% while her approach to absence analysis was based on available
% technology that did not extend to higher-order programs unlike
% \citet{Sergey2014modular}'s.

\citet{Firsov2016purely} also approach incrementalization by code
transformation, but their approach does not deal with changes to functions.
Instead of transforming functions written in terms of primitives, they provide
combinators to write CTS functions and derivatives together. On the other hand,
they extend their approach to support mutable caches, while restricting to
immutable ones as we do might lead to a logarithmic slowdown.

\paragraph{Finite differencing}
Incremental computation on collections or databases by finite differencing has a long
tradition~\citep{Paige82FDC,Blakeley:1986:EUM}. The most recent and
impressive line of work is the one on DBToaster~\citep{Koch10IQE,Koch14}, which
is a highly efficient approach to incrementalize queries over bags by combining
iterated finite differencing with other program transformations. They show
asymptotic speedups both in theory and through experimental evaluations.
Changes are only allowed for datatypes that form groups (such as bags or certain
maps), but not for instance for lists or sets. Similar ideas were recently
extended to higher-order and nested computation~\citep{Koch2016incremental},
though still restricted to datatypes that can be turned into groups.
% DBToaster relies on iterated differentiation to

% Like
\paragraph{Logical relations}
To study correctness of incremental programs we use a logical relation among
initial values |v1|, updated values |v2| and changes |dv|.
To define a logical relation for an untyped $\lambda$-calculus we use a
\emph{step-indexed} logical relation,
following~\citep{Appel01,Ahmed2006stepindexed};
in particular, our definitions are closest to the ones by \citet{Acar08}, who
also works with an untyped language, big-step semantics and (a different form
of) incremental computation. However, their logical relation does not mention
changes explicitly, since they do not have first-class status in their system.
Moreover, we use environments rather than substitution, and use a slightly
different step-indexing for our semantics.

% \paragraph{Other work not using change structures}

% in other approaches, a change for an atomic value |a1| simply describes an
% atomic value |a1| replacing it.
% %Self-adjusting computation
% In ILC, we can define changes for |a1 :: A| using a richer language, but the richer
% this language is, the more effort is needed to perform case analysis on it. This
% affects derivatives of primitives handling changes of type |Dt ^ T|.
% % there is a tension between  tradeoff between

% % A precedent is used by
% % \citet{Cicek2016type} to study a type system that describes complexity of
% % self-adjusting computation in the presence of control flow changes during
% % incremental evaluation.

\paragraph{Dynamic incrementalization}
The approaches to incremental computation with the widest applicability are
in the family of self-adjusting computation~\citep{Acar05,Acar09}, including its
descendant Adapton \citep{Hammer2014adapton}.
These approaches incrementalize programs by combining memoization and change
propagation: after creating a trace of base computations, updated inputs are
compared with old ones in $O(1)$ to find corresponding outputs, which are
updated to account for input modifications. Compared to self-adjusting
computation, Adapton only updates results when they are demanded. As usual,
incrementalization is not efficient on arbitrary programs.
To incrementalize efficiently a program must be designed so that input changes
produce small changes to the computation trace; refinement type systems have
been designed to assist in this task~\citep{Cicek2016type,Hammer2016typeda}.
Instead of comparing inputs by pointer equality, Nominal
Adapton~\citep{Hammer2015} introduces first-class labels to identify matching
inputs, enabling reuse in more situations.

Recording traces has often significant overheads in both space and time
(slowdowns of ~20-30$\times$ are common), though
\citet{Acar10TDT} alleviate that by with datatype-specific support for tracing
higher-level operations, while \citet{Chen2014} reduce that overhead by
optimizing traces to not record redundant entries, and by logging chunks of
operations at once, which reduces memory overhead but also potential speedups.
