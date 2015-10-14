\documentclass{jfp1}

\def\textmu{}

%include agda.fmt
\usepackage{textgreek} % not reproducible without textgreek

\usepackage{color}

\title{Regular Expression Matching with Dependent Types}
\author{Joomy Korkut, Maksim Trifunovski, Dan Licata}

% Editorial commands
\newcommand{\Red}[1]{{\color{red} #1}}
\newcommand{\ToDo}[1]{{\color{blue} ToDo: #1}}
\newcommand{\nb}[1]{$\lhd$ \Red{#1} $\rhd$}
\newcommand{\tocite}[0]{{\color{red} [cite]}\xspace}

\newcommand{\XXX}{\Red{XXX}}


% Math and code commands
\newcommand{\set}[1]{\{#1\}}
\newcommand{\standardize}{|standardize|}
\newcommand{\SRE}{|StdRegExp|}
\newcommand{\RE}{|RegExp|}

% Unicode chars not supported by lhs2TeX
\DeclareUnicodeCharacter{738}{$^s$}
\DeclareUnicodeCharacter{7503}{$^k$}

\begin{document}

\maketitle

\begin{abstract}
(This paper describes ...)
\end{abstract}

\tableofcontents

\section{Introduction}

Before we move on the definitions of the matchers, we should remember the
definitions of the monadic functions we use in our code:

\begin{code}
return : ∀ {A} → A → Maybe A
return = just

fail : ∀ {A} → Maybe A
fail = nothing

_>>=_ : ∀ {A B} → Maybe A → (A → Maybe B) → Maybe B
(just x) >>= f = f x
nothing >>= f = nothing

_∣_ : ∀ {A} → Maybe A → Maybe A → Maybe A
(just x) ∣ _ = just x
nothing | y = y
\end{code}


\section{StdRegExp description}

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
  s ∈Lˢ (r₁ ·ˢ r₂) =
    Σ (List Char × List Char) (λ { (p , q)  → (p ++ q ≡ s) × (p ∈Lˢ r₁) × (q ∈Lˢ r₂) })
  s ∈Lˢ (r ⁺ˢ) = s ∈L⁺ r

data _∈L⁺_ where
  S+ : ∀ {s r} → s ∈Lˢ r → s ∈L⁺ r
  C+ : ∀ {s s₁ s₂ r} → s₁ ++ s₂ ≡ s → s₁ ∈Lˢ r → s₂ ∈L⁺ r → s ∈L⁺ r
\end{code}

\section{Defunctionalized intrinsic matcher}

The main function for the defunctionalized intrinsic matcher is defined as following:

\begin{code}
match : (r : StdRegExp)
      → (s : List Char)
      → (k : List StdRegExp)
      → Maybe (Σ (List Char × List Char)
              (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
match ∅ˢ s k = fail
match (Litˢ c) [] k = fail
match (Litˢ c) (x ∷ xs) k =
    (isEqual x c) >>=
      (λ p → (match-helper k xs) >>=
        (λ pf → return (((c ∷ [] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf))))
match (r₁ ·ˢ r₂) s k =
    (match r₁ s (r₂ ∷ k)) >>= collect-left (λ inL inL' → _ , refl , inL , inL')
match (r₁ ⊕ˢ r₂) s k =
  ((match r₁ s k) >>= change-∈L inj₁) ∣
  ((match r₂ s k) >>= change-∈L inj₂)
match (r ⁺ˢ) s k =
  ((match r s k) >>= change-∈L S+) ∣
  ((match r s ((r ⁺ˢ) ∷ k)) >>= collect-left (λ inL inL' → C+ refl inL inL'))
\end{code}

To verify that our matcher works correctly for a match that we have a proof for,
we should write a completeness proof:

\begin{code}
match-completeness : (r : StdRegExp)
                   → (s : List Char)
                   → (k : List StdRegExp)
                   → Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k})
                   → isJust (match r s k )
\end{code}

\section{Higher-order intrinsic matcher}

The main function for the higher-order intrinsic matcher is defined as following:

\begin{code}
match : (C : Set)
      → (r : StdRegExp)
      → (s : List Char)
      → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
      → RecursionPermission s
      → Maybe C
match C ∅ˢ s k perm = nothing
match C (Litˢ x) [] k perm = nothing
match C (Litˢ x) (y ∷ ys) k perm with y Data.Char.≟ x
... | no _ = nothing
... | yes p = k {y ∷ []} {ys} refl (cong (λ q → q ∷ []) p)
match C (r₁ ·ˢ r₂) s k (CanRec f) =
  match C r₁ s
        (λ {p}{s'} eq inL →
          match C r₂ s' (λ {p'}{s''} eq' inL' →
                          k {p ++ p'}{s''} (replace-right p s' p' s'' s eq' eq) ((p , p') , refl , inL , inL'))
                        (f _ (suffix-continuation eq inL))) (CanRec f)
match C (r₁ ⊕ˢ r₂) s k perm =
  match C r₁ s (λ eq inL → k eq (inj₁ inL)) perm ∣
  match C r₂ s (λ eq inL → k eq (inj₂ inL)) perm
match C (r ⁺ˢ) s k (CanRec f) =
  match C r s (λ eq inL → k eq (S+ inL)) (CanRec f) ∣
  match C r s (λ {p}{s'} eq inL →
                match C (r ⁺ˢ) s' (λ {p'}{s''} eq' inL' →
                                    k (replace-right p s' p' s'' s eq' eq) (C+ refl inL inL') )
                      (f _ (suffix-continuation eq inL))) (CanRec f)
\end{code}

To verify that our matcher works correctly for a match that we have a proof for,
we should write a completeness proof:

\begin{code}
match-completeness : (C : Set)
                   → (r : StdRegExp)
                   → (s : List Char)
                   → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
                   → (perm : RecursionPermission s)
                   → Σ _ (λ { (p , s') → Σ _ (λ eq → Σ _ (λ inL → isJust (k {p}{s'} eq inL))) })
                   → isJust (match C r s k perm)
\end{code}

\section{Conversion from RegExp to StdRegExp}

In order to guarantee the termination of the matching function, the input regular expression is converted to a standard form regular expression. We define a function $\standardize : \RE \to \SRE$ such that

$$L( \standardize (r)) = L(r) \setminus L(\varepsilon)$$

We do not have a definition for the language itself, but we can define the requirements of a string being in the language of a regular expression. Hence, we should prove
$$(\forall s) \; \big[ s \in L(r) \Longleftrightarrow \left[ (\delta(r) = true \land s = []) \lor s \in L( \standardize (r))\right] \big]$$

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

Once we prove these this theorem, we can present the overall theorem we want from this theorem:

$$(\forall r)(\forall s) \; \big[ r \; |accepts| \;  s = |true| \Longleftrightarrow s \in L(r) \big]$$

The Agda representation of this theorem would correspond to the following types:

\begin{code}
correct-soundness : (r : RegExp)
                  → (s : String.String)
                  → r accepts s ≡ true
                  → (String.toList s) ∈L r
correct-completeness : (r : RegExp)
                     → (s : String.String)
                     → (String.toList s) ∈L r
                     → r accepts s ≡ true
\end{code}

\section{Conclusion}


\bibliographystyle{jfp}
\bibliography{paper}

\end{document}
