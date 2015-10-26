\RequirePackage{amsmath}
\documentclass{jfp1}

\def\textmu{}

%include agda.fmt
\usepackage{textgreek} % not reproducible without textgreek
\usepackage{bussproofs}

\usepackage{color}

% Editorial commands
\newcommand{\Red}[1]{{\color{red} #1}}
\newcommand{\ToDo}[1]{{\color{blue} ToDo: #1}}
\newcommand{\nb}[1]{$\lhd$ \Red{#1} $\rhd$}
\newcommand{\tocite}[0]{{\color{red} [cite]}\xspace}

\newcommand{\XXX}{\Red{XXX}}


% Math and code commands
\newcommand{\set}[1]{\left\{#1\right\}}
\newcommand{\standardize}{|standardize|}
\newcommand{\SRE}{|StdRegExp|}
\newcommand{\RE}{|RegExp|}

% Unicode chars not supported by lhs2TeX
\DeclareUnicodeCharacter{738}{$^\text{s}$}
\DeclareUnicodeCharacter{7503}{$^\text{k}$}

\title{Regular Expression Matching with Dependent Types}
\author[Joomy Korkut, Maksim Trifunovski, Daniel R. Licata]
       {JOOMY KORKUT, MAKSIM TRIFUNOVSKI, DANIEL R. LICATA\\
        Wesleyan University}


\begin{document}

\maketitle

\begin{abstract}
The matching algorithm described by Harper requires the input regular expressions
to be in standard form to guarantee the termination of the algorithm. In this paper,
we use Agda, a total programming language, to prove termination.
Harper's algorithm just checks if the regex matches the string but in practice,
one often needs to know how the regex matches the string to extract parts of the string.
For that purpose, we wrote an intrinsic version of the algorithm that also
returns which part of the string matched which part of the regex.
We created two different types of matchers which are explained in more detail in this paper.
One uses higher-order functions to pass the continuation, while the other one
is a defunctionalized version which uses lists of StdRegExps instead.
In conclusion, we have proven the correctness of both.
\end{abstract}

\tableofcontents

\section{Introduction}

% A derivation isn't just being in set, it contains things
% Show how different derivations (x : s \inL r) can contain different stuff

% Skip regex, but explain standard, explain Kleene plus

\section{Background}

\subsection{Regular Expressions and Languages}

\subsection{Monadic Functions}

Before we move on the definitions of the matchers, we should remember the
definitions of the monadic functions we use in our code, for the |Maybe| type:

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

|∅ˢ| is the empty set, |Litˢ| is the character literal, |_·ˢ_| is concatenation,
|_⊕ˢ_| is alternation. Concatenation and alternation are closed in standard
regular expressions. Lastly, |_⁺ˢ| is the Kleene plus case.

We can define the rules for a string to be in the language of Kleene plus as such:
\begin{prooftree}
  \AxiomC{$s \in L(|r|)$}
  \UnaryInfC{$s \in L(|r ⁺ˢ|)$}
\end{prooftree}

\begin{prooftree}
  \AxiomC{$s_1 s_2 = s$}
  \AxiomC{$s_1 \in L(|r|)$}
  \AxiomC{$s_2 \in L(|r ⁺ˢ|)$}

  \TrinaryInfC{$s \in L(|r ⁺ˢ|)$}
\end{prooftree}

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

Note that, if we are given a list of characters $x$ and two derivations of
the same type, both telling us that |x ∈Lˢ r|, we cannot assume the
derivations are equivalent. \\
An example of this is the following:\\ Let |x = 'a' ∷ 'a' ∷ 'a' ∷ []| and
|r = ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))|, then a derivation of type |x ∈Lˢ r| can
have two different values: One of them can match one character in the first |a⁺|
of the concatenation and match two characters in the second |a⁺|. The other value
can match two characters in the first |a⁺| and match one character in the second
|a⁺|. Hence derivations of the same type are not necessarily equivalent.
The same argument can be made for derivations of non-standard regular expressions.

% two different values in the same type written in Agda

% \begin{code}
% ex₁ : ('a' ∷ 'a' ∷ 'a' ∷ []) ∈Lˢ ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))
% ex₂ : ('a' ∷ 'a' ∷ 'a' ∷ []) ∈Lˢ ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))
% ex₁ = ('a' ∷ [] , 'a' ∷ 'a' ∷ []) , refl , S+ refl , C+ refl refl (S+ refl)
% ex₂ = ('a' ∷ 'a' ∷ [] , 'a' ∷ []) , refl , C+ refl refl (S+ refl) , S+ refl
% \end{code}

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
        (λ pf → return ((([ c ] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf))))
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
... | yes p = k {[ y ]} {ys} refl (cong (λ q → [ q ]) p)
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


\subsection{Conversion}
In order to guarantee the termination of the matching function, the input
regular expression is converted to a standard form regular expression.
We define a function $\standardize : \RE \to \SRE$ such that

$$L( \standardize (r)) = L(r) \setminus L(\varepsilon)$$

We do not have a definition for the language itself, but we can define the
requirements of a string being in the language of a regular expression.
Hence, we should prove
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
