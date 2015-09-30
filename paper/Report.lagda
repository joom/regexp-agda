\documentclass{scrartcl}
% \documentclass[12pt]{article}

\def\textmu{}

%include agda.fmt
\usepackage{textgreek} % not reproducible without textgreek

\usepackage{fullpage}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{amssymb}
\usepackage{enumerate}
\usepackage{wasysym}

\newcommand{\set}[1]{\{#1\}}
\newcommand{\standardize}{\text{standardize}}
\newcommand{\SRE}{\text{StdRegExp}}
\newcommand{\RE}{\text{RegExp}}

\linespread{1.2}

\title{Regular Expression Matching with Dependent Types}
\author{Joomy Korkut, Maksim Trifunovski, Dan Licata}
\date{August 2015}

\begin{document}

\maketitle

% StdRegExp description
% Intrinsic defun
% Intrinsic HOF
% Conversion from RegExp to StdRegExp
    % Show why it is enough to match on StdRegExp

\medskip

% StdRegExp description


% Conversion
In order to guarantee the termination of the matching function, the input regular expression is converted to a standard form regular expression. We define a function $\standardize : \RE \to \SRE$ such that

$$L( \standardize (r)) = L(r) - L(\varepsilon)$$

We do not have a definition for the language itself, but we can define the requirements of a string being in the language of a regular expression. Hence, we should prove
$$(\forall s) \;\; s \in L(r) \Longleftrightarrow \left[ (\delta(r) = true \land s = []) \lor s \in L( \standardize (r))\right]$$

We are going to prove the previously stated theorem in Agda.

\begin{code}
∈L-soundness : (s : List Char)
             → (r : RegExp)
             → ((δ r ≡ true) × (s ≡ [])) ⊎ (s ∈Lˢ (standardize r))
             → s ∈L r

∈L-completeness : (s : List Char)
                → (r : RegExp)
                → s ∈L r
                → ((δ r ≡ true) × (s ≡ [])) ⊎ (s ∈Lˢ (standardize r))
\end{code}

\end{document}
