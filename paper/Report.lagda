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

% Skip regex, but explain standard, explain Kleene plus
% Explain RecursionPermission and Suffix ?

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
mutual
  _∈Lˢ_ : List Char → StdRegExp → Set
  _ ∈Lˢ ∅ˢ = ⊥
  s ∈Lˢ (Litˢ c) = s ≡ c ∷ []
  s ∈Lˢ (r₁ ⊕ˢ r₂) = (s ∈Lˢ r₁) ⊎ (s ∈Lˢ r₂)
  s ∈Lˢ (r₁ ·ˢ r₂) = Σ (List Char × List Char) (λ { (p , q)  → (p ++ q ≡ s) × (p ∈Lˢ r₁) × (q ∈Lˢ r₂) })
  s ∈Lˢ (r ⁺ˢ) = s ∈L⁺ r

  data _∈L⁺_ : List Char → StdRegExp → Set where
      S+ : ∀ {s r} → s ∈Lˢ r → s ∈L⁺ r
      C+ : ∀ {s s₁ s₂ r} → s₁ ++ s₂ ≡ s → s₁ ∈Lˢ r → s₂ ∈L⁺ r → s ∈L⁺ r
\end{code}

Note that, if we are given a list of characters $x$ and two derivations of
of the type |x ∈Lˢ r|, the derivations are not necessarily the same.
An example of this is the following:

% write them as derivation trees with inference rules

\begin{prooftree}
    \AxiomC{$``a" \in L(|Litˢ 'a'|)$}
\LeftLabel{Derivation A}
  \UnaryInfC{$``a" \in L(|Litˢ 'a' ⁺ˢ|)$}
\end{prooftree}

\begin{prooftree}
    \AxiomC{$``a" \plus ``a" = ``aaa"$}
    \AxiomC{$``a" \in L(|Litˢ 'a'|)$}
    \AxiomC{Derivation A}
\LeftLabel{Derivation B}
  \TrinaryInfC{$``aa" \in L(|Litˢ 'a' ⁺ˢ|)$}
\end{prooftree}

\begin{prooftree}
  \AxiomC{$``a" \plus ``aa" = ``aaa"$}
  \AxiomC{Derivation A}
  \AxiomC{Derivation B}
\LeftLabel{Derivation C}
  \TrinaryInfC{$``aaa" \in L(|(Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ)|)$}
\end{prooftree}

\begin{prooftree}
  \AxiomC{$``aa" \plus ``a" = ``aaa"$}
  \AxiomC{Derivation B}
  \AxiomC{Derivation A}
\LeftLabel{Derivation D}
  \TrinaryInfC{$``aaa" \in L(|(Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ)|)$}
\end{prooftree}

As you can see in derivations C and D, the same string can have different
derivations for the same regular expression.
The same argument can be made for derivations of non-standard regular expressions.

% two different values in the same type written in Agda

% \begin{code}
% ex₁ : ('a' ∷ 'a' ∷ 'a' ∷ []) ∈Lˢ ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))
% ex₂ : ('a' ∷ 'a' ∷ 'a' ∷ []) ∈Lˢ ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))
% ex₁ = ('a' ∷ [] , 'a' ∷ 'a' ∷ []) , refl , S+ refl , C+ refl refl (S+ refl)
% ex₂ = ('a' ∷ 'a' ∷ [] , 'a' ∷ []) , refl , C+ refl refl (S+ refl) , S+ refl
% \end{code}

\section{Defunctionalized intrinsic matcher}

% some introduction about list based continuation

Before we start the |match| function, we should define a type for a string
to be in the language of a list of regular expressions:

\begin{code}
_∈Lᵏ_ : List Char → List StdRegExp → Set
s ∈Lᵏ [] = s ≡ []
s ∈Lᵏ (r ∷ rs) =
  Σ (List Char × List Char) (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × (s' ∈Lᵏ rs) })
\end{code}

There are two possibilities for a string to be in the language of a list of
regular expressions. If the list is empty, the string also has to be empty.
If the list has a head, then a prefix of the string should match the head of
the list and the rest of the list should match with the rest of the string.

Now that we know how to handle the continuation list, we can define the main
function for the defunctionalized intrinsic matcher case by case as following:

\begin{code}
match : (r : StdRegExp)
      → (s : List Char)
      → (k : List StdRegExp)
      → Maybe (Σ (List Char × List Char)
              (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
\end{code}

This is the type of our defunctionalized intrinsic matcher.
It takes a regular expression |r|, a list of characters |s| and
a list of StdRegExps |k|, and creates a splitting of the original list
|s| into lists |p| and |s'| and returns an equality |(p ++ s' ≡ s)|,
a derivation that |p| is in the language of |r| and a derivation
that |s' ∈Lᵏ k|, which is defined to mean that if |k| is empty,
then |s'| has to be empty as well, otherwise |k = r'::rs| and there is
a splitting of |s'|, |s' ≡ p' ++ s''|, such that |p' ∈Lˢ r'| and |s'' ∈Lᵏ rs|.

\begin{code}
match ∅ˢ s k = fail
\end{code}

The empty language does not accept any string.

\begin{code}
match (Litˢ c) [] k = fail
match (Litˢ c) (x ∷ xs) k =
    (isEqual x c) >>=
      (λ p → (match-helper k xs) >>=
        (λ pf → return ((([ c ] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf))))
\end{code}

If we are trying to match an empty list with a regular expression that requires a character, the matcher fails.
If not, we try to match the first character of the string to |c| and then
match the continuation using the function |match-helper| which is
mutually recursive with our matcher and is defined as follows:

\begin{code}
match-helper : (k : List StdRegExp) → (s : List Char) → Maybe (s ∈Lᵏ k)
match-helper [] [] = return refl
match-helper [] (x ∷ s) = fail
match-helper (r ∷ rs) s = match r s rs
\end{code}

Now if the first character in our list matches the character literal |c|,
then we call |match-helper| on the continuation and the rest of the list.
Then from |match-helper| we will get a derivation of the type |s ∈Lᵏ k|
if the rest of the list indeed matches the rest of the |StdRegExp|s in |k|.

\begin{code}
match (r₁ ·ˢ r₂) s k =
    (match r₁ s (r₂ ∷ k)) >>= collect-left (λ inL inL' → _ , refl , inL , inL')
\end{code}

\begin{code}
match (r₁ ⊕ˢ r₂) s k =
  ((match r₁ s k) >>= change-∈L inj₁) ∣
  ((match r₂ s k) >>= change-∈L inj₂)
\end{code}

\begin{code}
match (r ⁺ˢ) s k =
  ((match r s k) >>= change-∈L S+) ∣
  ((match r s ((r ⁺ˢ) ∷ k)) >>= collect-left (λ inL inL' → C+ refl inL inL'))
\end{code}

\subsection{Verification}

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

% introduction about function based continuation

A problem that arises with the function based continuations is regarding the
totality checker. It is not evident to Agda that our |match| function terminates,
because there is no obviously diminishing list of continuations like the
defunctionalized matcher. This is why we have to show Agda that our recursive
function really terminates, by providing an extra argument that is obviously
diminishing. We define it as following:

\begin{code}
data RecursionPermission {A : Set} : List A → Set where
  CanRec : {ys : List A}
         → ((xs : List A) → Suffix xs ys → RecursionPermission xs)
         → RecursionPermission ys
\end{code}

The main function for the higher-order intrinsic matcher is defined case by case as following:

\begin{code}
match : (C : Set)
      → (r : StdRegExp)
      → (s : List Char)
      → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
      → RecursionPermission s
      → Maybe C
\end{code}

The |match| function is now taking an extra argument |C| that helps us define the continuation function and the return type.
The purpose for having |C| as an argument is to be able to refer to the top level of the recursive calls in every sub recursive call.

Notice that the continuation |k| is a function, unlike the defunctionalized version,
but similar to Harper's matcher. It is a function that possibly gives a derivation
(hence the |Maybe| type) for the entire string given that there is a split of it
such that the first part is in the language of |r|.

We also need an extra argument of type |RecursionPermission s| to explicitly
show Agda that the string |s| gets shorter in each recursive call. Remember that
to get a new |RecursionPermission s'| depending on an existing |RecursionPermission s|,
it has to be that |s'| is a strict suffix of |s|.

\begin{code}
match C ∅ˢ s k perm = fail
\end{code}

Just like the defunctionalized version, the empty language does not accept any string.

\begin{code}
match C (Litˢ x) [] k perm = fail
match C (Litˢ x) (y ∷ ys) k perm with y Data.Char.≟ x
... | no _ = fail
... | yes p = k {[ y ]} {ys} refl (cong (λ q → [ q ]) p)
\end{code}

The character literal language should only accept the string if the
first character is the same as the one required by |r| and the continuation
returns a derivation for the rest of the string.

\begin{code}
match C (r₁ ·ˢ r₂) s k (CanRec f) =
  match C r₁ s
        (λ {p}{s'} eq inL →
          match C r₂ s' (λ {p'}{s''} eq' inL' →
                          k {p ++ p'}{s''} (replace-right p s' p' s'' s eq' eq) ((p , p') , refl , inL , inL'))
                        (f _ (suffix-continuation eq inL))) (CanRec f)
\end{code}

In the concatenation case of the defunctionalized version,
we could add |r₂| to the list of continuations to be matched later.
However, the higher-order matcher needs to construct a new
continuation function. Once |r₁| was matched with the beginning of the string,
the continuation would match the rest of the string with |r₂|.

Notice that to be able to call |match| with |r₂|, you need to prove that the
rest of the string is a strict suffix of the entire string so that you can get
a |RecursionPermission| for the rest. The function |suffix-continuation| does exactly that.

\begin{code}
match C (r₁ ⊕ˢ r₂) s k perm =
  match C r₁ s (λ eq inL → k eq (inj₁ inL)) perm ∣
  match C r₂ s (λ eq inL → k eq (inj₂ inL)) perm
\end{code}

The alternation case is similar to the defunctionalized version except the continuations.
The matcher first tries to match |r₁| with |s| and
tries to match |r₂| only if the first one does not match.

\begin{code}
match C (r ⁺ˢ) s k (CanRec f) =
  match C r s (λ eq inL → k eq (S+ inL)) (CanRec f) ∣
  match C r s (λ {p}{s'} eq inL →
                match C (r ⁺ˢ) s' (λ {p'}{s''} eq' inL' →
                                    k (replace-right p s' p' s'' s eq' eq) (C+ refl inL inL') )
                      (f _ (suffix-continuation eq inL))) (CanRec f)
\end{code}

The structure of the Kleene plus case is similar to the defunctionalized version except the continuations.
The matcher first tries to match |r| with |s| and tries to match the concatenation
of |r| and |r ⁺ˢ| only if the first try fails. Observe that the second try is
similar to the |·ˢ| case.

\subsection{Verification}

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

We also want to prove decidability:

\begin{code}
decidability : (r : RegExp)
             → (s : String.String)
             → ((String.toList s) ∈L r) ⊎ (¬ ((String.toList s) ∈L r))
\end{code}

\section{Conclusion}


\bibliographystyle{jfp}
\bibliography{paper}

\end{document}
