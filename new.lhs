\documentclass{book}

\usepackage{natbib}
\usepackage{comment}
\bibliographystyle{abbrvnat}
\input{packages}
\input{macros}
\usepackage{amsthm}

%include polycode.fmt
\begin{document}

%%%
%%% XXX Integrate properly in rest of document. Will be possible.
%%%
\chapter{Incrementalizing more programs}
\pg{Only a sketch for now}

While the basic framework we presented is significant, applying it in practice
to incrementalize programs is hard because of a few problems.
\begin{enumerate}
\item The incremental computation does not have accesss to intermediate results from the original computation.
\item Since function changes are represented as functions, the derivative cannot
  test if a function change is nil. In fact, while a function change can replace
  a function with an arbitrary other function, actual changes often simply
  replace a closure with another closure using the same code but closing over a
  changed environment.
\end{enumerate}

A few other annoyances
\begin{enumerate}
\item Applying a derivative to a nil change always produce a nil change, but we
  never take advantage of this to optimize derivatives, except sometimes at
  compile time.
\item We do not support change composition.
\item Change structures must provide a difference operation, even though most
  often we are not supposed to use it.
\end{enumerate}

\begin{code}
\end{code}
\end{document}
