\PassOptionsToPackage{kerning=true}{microtype}
\PassOptionsToPackage{unicode}{hyperref}
%% For double-blind review submission
\documentclass[acmsmall,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission
%\documentclass[acmsmall,review]{acmart}\settopmatter{printfolios=true}
%\documentclass[sigplan,10pt,review]{acmart}\settopmatter{printfolios=true}

%% For final camera-ready submission
%\documentclass[acmlarge]{acmart}\settopmatter{}

% Directives for lhs2TeX formatting

%include polycode.fmt

% Shrink a bit lhs2TeX code  this hook is there for this reason:
\renewcommand{\hscodestyle}{\small}
% If we're desperate, but it looks bad:
%\renewcommand{\hscodestyle}{\footnotesize}
%
\input{macros}
\usepackage{thesis-defs}

% Local packages

\usepackage{syntaxmacros,multicol}
\usepackage{tikz}
\usepackage{pgfplots}
\usepackage{subcaption}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\input{paperInfo}

%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission
\setcopyright{none}             %% For review submission
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2017}           %% If different from \acmYear

%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
\citestyle{acmauthoryear}

% \title[Incremental λ-Calculus in Cache-Transfer Style]{Incremental λ-Calculus in Cache-Transfer Style: Static Memoization by Program Transformation}
\title{Incremental λ-Calculus in Cache-Transfer Style}
\subtitle{Static Memoization by Program Transformation}

\author{Paolo G. Giarrusso}
\affiliation{
  %\position{Position1}
  \department{Wilhelm-Schickard-Institut}              %% \department is recommended
  \institution{University of Tübingen}            %% \institution is required
  % \streetaddress{Street1 Address1}
  \city{Tübingen}
  % \state{State1}
  % \postcode{Post-Code1}
  \country{Germany}
}

\author{Yann Régis-Gianas}
\affiliation{
  \department{IRIF, PPS, {\pi}r^2}              %% \department is recommended
  \institution{University of Paris Diderot, INRIA}            %% \institution is required
  \city{Paris}
  \country{France}
}
\author{Philipp Schuster}
\affiliation{
  \department{Wilhelm-Schickard-Institut}              %% \department is recommended
  \institution{University of Tübingen}            %% \institution is required
  \city{Tübingen}
  \country{Germany}
}

\begin{abstract}
  % TODO: more general abstract, this is too technical.
Incremental computation requires propagating changes and reusing intermediate
results of base computations.
Derivatives, as produced by static differentiation~\citep{CaiEtAl2014ILC}, propagate
changes but do not reuse intermediate results.
We introduce additional program transformations producing purely functional
programs that create and maintain nested tuples of intermediate results. We
avoid remembering values needed by self-maintainable derivatives.
To prove correctness of our transformation, we extend the correctness proof of
static differentiation from STLC to untyped $\lambda$-calculus via
\emph{step-indexed logical relations}, and prove correctness of the additional
transformation via simulation theorems.

We evaluate incrementalization performance via case studies.
We provide derivatives of primitives for operations on collections,
differentiate our case studies using those primitives,
and already on input sizes less than $10^3$ we measure speedups of two orders of
magnitude, up to 180x; computing output changes can be up to 370x faster.
% We augment derivatives to maintain intermediate results while
% introduce a
% program transformation, that produces purely functional programs that produce
% and remember nested tuples of intermediate results and avoid remembering
% values that are only used by self-maintainable derivatives.
\end{abstract}

%\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
%\terms
%term1, term2

%\keywords
%keyword1, keyword2


\maketitle
\input{static-caching-content}

\bibliography{../Bibs/ProgLang,../Bibs/DB,../Bibs/own,../Bibs/SoftEng}

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
