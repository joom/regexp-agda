% \documentclass{scrartcl}
\documentclass[10pt]{article}

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
\newcommand{\standardize}{|standardize|}
\newcommand{\SRE}{|StdRegExp|}
\newcommand{\RE}{|RegExp|}

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

Let's define $\SRE$ as follows:

\begin{code}
data StdRegExp : Set where
  ∅ˢ : StdRegExp
  Litˢ : Char → StdRegExp
  _·ˢ_ : StdRegExp → StdRegExp → StdRegExp
  _⊕ˢ_ : StdRegExp → StdRegExp → StdRegExp
  _⁺ˢ : StdRegExp → StdRegExp
\end{code}

Each of the constructors correspond to these languages:

\begin{itemize}
  \item $L(|∅ˢ|) = \emptyset$.
  \item $L(|Litˢ 'a'|) = \set{s \in |List Char| : s=|"a"|}$.
  \item $L(|r₁ ·ˢ r₂|) = \set{s \in |List Char| : \exists (s_1 s_2 = s) \ s_1 \in L(r_1) \land s_2 \in L(r_2) }$.
  \item $L(|r₁ ⊕ˢ r₂|) = \set{s \in |List Char| : s \in L(r_1) \lor s \in L(r_2)}$.
  \item $L(|r ·ˢ|) = \set{s \in |List Char| : s \in L(r) \lor \exists (s_1 s_2 = s) \ s_1 \in L(r) \land s_2 \in L(|r ·ˢ|) }$.
\end{itemize}

We encode these languages in Agda in the following way:

\begin{code}
_∈Lˢ_ : List Char → StdRegExp → Set
data _∈L⁺_ : List Char → StdRegExp → Set

  _ ∈Lˢ ∅ˢ = ⊥
  s ∈Lˢ (Litˢ c) = s ≡ c ∷ []
  s ∈Lˢ (r₁ ⊕ˢ r₂) = (s ∈Lˢ r₁) ⊎ (s ∈Lˢ r₂)
  s ∈Lˢ (r₁ ·ˢ r₂) = Σ (List Char × List Char) (λ { (p , q)  → (p ++ q ≡ s) × (p ∈Lˢ r₁) × (q ∈Lˢ r₂) })
  s ∈Lˢ (r ⁺ˢ) = s ∈L⁺ r

data _∈L⁺_ where
  S+ : ∀ {s r} → s ∈Lˢ r → s ∈L⁺ r
  C+ : ∀ {s s₁ s₂ r} → s₁ ++ s₂ ≡ s → s₁ ∈Lˢ r → s₂ ∈L⁺ r → s ∈L⁺ r
\end{code}


% Conversion
In order to guarantee the termination of the matching function, the input regular expression is converted to a standard form regular expression. We define a function $\standardize : \RE \to \SRE$ such that

$$L( \standardize (r)) = L(r) \setminus L(\varepsilon)$$

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
