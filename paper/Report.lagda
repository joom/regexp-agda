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
\DeclareUnicodeCharacter{739}{$^\text{x}$}
\DeclareUnicodeCharacter{8709}{$\varnothing$} % overwriting \emptyset

\title{Regular Expression Matching \break with Dependent Types}
\author[Joomy Korkut, Maksim Trifunovski, Daniel R. Licata]
       {JOOMY KORKUT, MAKSIM TRIFUNOVSKI, DANIEL R. LICATA\\
        Wesleyan University}


\begin{document}

\maketitle

\begin{abstract}
The matching algorithm described by Harper requires the input regular
expressions to be in standard form to guarantee the termination of the
algorithm. In this paper, we use Agda, a total programming language, to prove
termination.  Harper's algorithm just checks if the regex matches the string
but in practice, one often needs to know how the regex matches the string to
extract parts of the string.  For that purpose, we wrote an intrinsic version
of the algorithm that also returns which part of the string matched which part
of the regex.  We created two different types of matchers which are explained
in more detail in this paper.  One uses higher-order functions to pass the
continuation, while the other one is a defunctionalized version which uses
lists of standard form regular expressions instead.  In conclusion, we have
proven the correctness of both.
\end{abstract}

\tableofcontents

\section{Introduction}

Robert Harper's paper ``Proof-Directed Debugging" presents a simple
implementation of a regular expression matching algorithm that has a flaw which
is revealed during its correctness proof; it turns out that the algorithm does
not terminate for all regular expressions. Harper fixes this flaw by changing
the specification and allowing only the standard form regular expressions as an
argument to the matching function. The paper also proves that the new
specification suffices to cover all regular expressions and hence solve the
original problem.

The algorithm described by Harper is simple, however its termination depends on
preconditions about its arguments, not its type. Therefore, in a total language
like Agda, proving the termination of the algorithm becomes a problem. We have
to define a new type to encode the precondition of regular expressions we want
as an argument and then handle the type conversions to show that our program
manages to solve the original problem. We use Agda as a proof checker to prove
this.

The matcher functions described by Harper have the type signatures:

\vspace{4mm}
|match: RegExp → List Char → (List Char → Bool) → Bool|

|_accepts_ : RegExp → String → Bool|
\vspace{4mm}

Obviously, |_accepts_| takes a regular expression and a string, and returns
|true| if the regular expression accepts the string or it returns |false|
otherwise.  The other function |match| takes a regular expression, a list of
characters and a continuation as arguments. It returns |true| if a prefix of
the list of characters matches the given regular expression and the
continuation called with the the rest of the string returns |true|. It returns
|false| otherwise. In our implementation of these functions in Agda, we will
keep the type signature of |_accepts_| as it is, but we will have to modify the
type of |match| to be able to show Agda that it definitely terminates.

When we prove the soundness of our matcher function, we will have to create a
proof that the given string is in the language of the given regular expression.
There is a value we can get out of our soundness proof; we can have capture
groups in our regular expressions and extract which part of the string matched
which part of our regular expression.

Yet this would not be an efficient implementation of grouping in regular
expressions, because we would have to run the matcher twice in this case: one
to check if the regular expression matches the string, and once again to get
the soundness proof.

However, if we decide to verify our matcher intrinsically, rather than
extrinsically, we can get away with running the matcher only once. Our matcher
in this case would return the proof of the string being in the language of the
regular expression, in an option type (|Maybe| in Haskell and Agda). This would
mean defining the matcher function and the soundness proof at the same time.

If our matcher function is going to return a derivation that proves that a
string is the language of a regular expression, then we cannot simple have a
continuation function |String → Bool| anymore; we have to enhance the
continuation so that it returns a part of the derivation that we can use to
construct the entire derivation.  This turns out to be a complex task, so we
tried defunctionalizing the matcher and using list based continuations instead
of higher-order functions.  For comparison, we will present both the
defunctionalized and higher-order continuation versions of the matcher in this
paper.

\section{Background}

\ToDo{Some note about using the term "string" and "list of characters" interchangably. |String| and |List Char| are different types in Agda and even though converting between them is trivial, |List Char| allows direct pattern matching.}

\subsection{Regular Expressions and Languages}

We will not review regular expressions, but we should remember
that the Kleene plus is defined as $\Sigma^+ = \Sigma \Sigma^* $, where
$\Sigma^*$ is the Kleene star.

\subsection{Monadic Functions}

Before we move onto the definitions of the matchers, we should remember the
definitions of the monadic functions we use in our code, for the |Maybe| type:

\begin{code}
return : ∀ {A} → A → Maybe A
return = just

fail : ∀ {A} → Maybe A
fail = nothing

_>>=_ : ∀ {A B} → Maybe A → (A → Maybe B) → Maybe B
just x >>= f = f x
nothing >>= f = nothing

_∣_ : ∀ {A} → Maybe A → Maybe A → Maybe A
just x ∣ _ = just x
nothing | y = y

map : ∀ {A B} → (A → B) → Maybe A → Maybe B
map f (just x) = just (f x)
map _ nothing  = nothing
\end{code}

With Haskell terminology, |_∣_| is |mplus| and |map| is |fmap|.

\section{StdRegExp description}

The standard form regular expressions defined by Harper do not accept the empty
string. Our new type for such regular expressions will closely resemble the
usual regular expressions, however it will vary in the cases that accept the
empty string. We will omit the $\varepsilon$ case in usual regular expressions,
and replace Kleene star with Kleene plus.

Let's define |StdRegExp| as follows:

\begin{code}
data StdRegExp : Set where
  ∅ˢ : StdRegExp
  Litˢ : Char → StdRegExp
  _·ˢ_ : StdRegExp → StdRegExp → StdRegExp
  _⊕ˢ_ : StdRegExp → StdRegExp → StdRegExp
  _⁺ˢ : StdRegExp → StdRegExp
\end{code}

|∅ˢ| is the empty set, |Litˢ| is the character literal, |_·ˢ_| is
concatenation, |_⊕ˢ_| is alternation. Concatenation and alternation are closed
in standard regular expressions. Lastly, |_⁺ˢ| is the Kleene plus case.

We can define the rules for a string to be in the language of Kleene plus as
such:

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

We encode these languages and the others in Agda in the following way:

\begin{code}
mutual
  _∈Lˢ_ : List Char → StdRegExp → Set
  _ ∈Lˢ ∅ˢ = ⊥
  s ∈Lˢ (Litˢ c) = s ≡ c ∷ []
  s ∈Lˢ (r₁ ⊕ˢ r₂) = (s ∈Lˢ r₁) ⊎ (s ∈Lˢ r₂)
  s ∈Lˢ (r₁ ·ˢ r₂) =
    Σ (List Char × List Char) (λ { (p , q)  → (p ++ q ≡ s) × (p ∈Lˢ r₁) × (q ∈Lˢ r₂) })
  s ∈Lˢ (r ⁺ˢ) = s ∈L⁺ r

  data _∈L⁺_ : List Char → StdRegExp → Set where
      S+ : ∀ {s r} → s ∈Lˢ r → s ∈L⁺ r
      C+ : ∀ {s s₁ s₂ r} → s₁ ++ s₂ ≡ s → s₁ ∈Lˢ r → s₂ ∈L⁺ r → s ∈L⁺ r
\end{code}

Note that, if we are given a list of characters $x$ and two derivations of of
the type |x ∈Lˢ r|, the derivations are not necessarily the same.  An example
of this is the following:

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
derivations for the same regular expression.  The same argument can be made for
derivations of non-standard regular expressions.

% two different values in the same type written in Agda

% \begin{code}
% ex₁ : ('a' ∷ 'a' ∷ 'a' ∷ []) ∈Lˢ ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))
% ex₂ : ('a' ∷ 'a' ∷ 'a' ∷ []) ∈Lˢ ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))
% ex₁ = ('a' ∷ [] , 'a' ∷ 'a' ∷ []) , refl , S+ refl , C+ refl refl (S+ refl)
% ex₂ = ('a' ∷ 'a' ∷ [] , 'a' ∷ []) , refl , C+ refl refl (S+ refl) , S+ refl
% \end{code}

We will now define the matcher functions using only standard regular expressions.

\section{Defunctionalized intrinsic matcher}

Harper's solution to the regular expression matching problem uses higher-order
functions to manage the continuation-passing. Since proving the termination of
higher-order continuations in Agda is a more difficult task, we decided
to first defunctionalize the algorithm described by Harper and use list based
continuations instead.

Before we start the |match| function, we should define a type for a string to
be in the language of a list of regular expressions:

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

\subsection{Definition}

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

\subsubsection{Base cases}

\begin{code}
match ∅ˢ s k = fail
\end{code}

The empty language does not accept any string.

\begin{code}
match (Litˢ c) (x ∷ xs) k =
  (isEqual x c) >>=
    (λ p → map (λ pf → ((([ c ] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf)))
               (match-helper k xs))
\end{code}

If we are trying to match an empty list with a regular expression that requires
a character, the matcher fails.  If not, we try to match the first character of
the string to |c| and then match the continuation using the function
|match-helper| which is mutually recursive with our matcher and is defined as
follows:

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

\subsubsection{Concatenation}

\begin{code}
match (r₁ ·ˢ r₂) s k =
  map (reassociate-left {R = _·ˢ_} (λ inL inL' → _ , refl , inL , inL'))
    (match r₁ s (r₂ ∷ k))
\end{code}

If we have one |StdRegExp| to match to the beginning of the string and another
one to match to the rest of the string, we try to match the first one first,
and add the second one to the continuation list of regular expressions |k|. Now
calling match on |r₁ s (r₂ ∷ k)| will give us a split |xs ++ ys ≡ s| and
derivations of the type |xs ∈Lˢ r₁| and |ys ∈Lᵏ (r₂ ∷ k)|. If we unpack the
second derivation (provided by our definition of |∈Lᵏ| and the fact that our
continuation list contains at least one element, |r₂|), we will have another
split |as ++ bs ≡ ys| and derivations |as ∈Lˢ r₂| and |bs ∈Lᵏ k|. Our helper
function |reassociate-left| states that if we have such a situation, we should
be able to state that |xs ++ as| matches the entire regular expression, in
this case, |r₁ ·ˢ r₂|.

\subsubsection{Alternation}

\begin{code}
match (r₁ ⊕ˢ r₂) s k =
  (map (change-∈L inj₁) (match r₁ s k)) ∣
  (map (change-∈L inj₂) (match r₂ s k))
\end{code}

We define the alternation case by trying to match the string with the first
part of the alternation, and if that fails we try to match with the second
part.

Notice that if the call |match r₁ s k| does not fail, it will contain a
derivation of type |s ∈Lˢ r₁|. However the return type for the alternation case
should contain a derivation of type |s ∈Lˢ (r₁ ⊕ˢ r₂)|. Our helper function
|change-∈L| allows us to do that.

\begin{code}
change-∈L : {a b d : List Char → Set} {c : List Char → List Char → Set}
          → (∀ {s} → a s → b s)
          → (Σ _ (λ {(p , s') → (c p s') × (a p) × (d s')}))
          → (Σ _ (λ {(p , s') → (c p s') × (b p) × (d s')}))
change-∈L f (x , eq , inL , rest) = (x , eq , f inL , rest)
\end{code}

We use |change-∈L| to apply |inj₁| or |inj₂| to the derivation, depending on
which part of the alternation successfully matched the string.

\subsubsection{Kleene plus}

\begin{code}
match (r ⁺ˢ) s k =
  (map (change-∈L S+) (match r s k)) ∣
  (map (reassociate-left {R = λ r _ → r ⁺ˢ} (λ inL inL' → C+ refl inL inL'))
    (match r s ((r ⁺ˢ) ∷ k)))
\end{code}

In the Kleene plus case, we first try to match |s| with just |r| and if that
succeeds we apply |change-∈L S+| to the derivation since we matched from the
single |r| case. If this fails, then similar to the |·ˢ| case, we try to match
a prefix of the string to |r| and then the suffix that follows with the
continuation which now includes |r ⁺ˢ|. Just like in the |·ˢ| case, we use
|reassociate-left| in order to get that our splitting of |s| matches the entire
starting |r|.

\subsection{Verification}

To verify that our matcher works correctly for a match that we have a proof
for, we should write a completeness proof:

\begin{code}
match-completeness : (r : StdRegExp)
                   → (s : List Char)
                   → (k : List StdRegExp)
                   → Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × (s' ∈Lᵏ k)})
                   → isJust (match r s k)
\end{code}

We are going to prove that if we have |r|, |s|, |k| and a split of
|p ++ s' ≡ s| such that there are derivations of type |p ∈Lˢ r| and |s' ∈Lᵏ k|,
then we know that our |match| function does not fail. Notice that we cannot
make a stronger claim and say that it returns the same derivations, because as
we showed before, derivations of the same type are not necessarily the same.

The base cases |∅ˢ| and |Litˢ| are trivial. Since the Kleene plus case captures
the essence of both concatenation and alternation cases, we will only explain
the completeness proof of the Kleene plus case.

\begin{code}
match-completeness (r ⁺ˢ) s k ((xs , ys) , eq , S+ x , rest)
  with match r s k | match-completeness r s k ((xs , ys) , eq , x , rest)
... | nothing | ()
... | just _  | _ = tt
\end{code}

The constructor |S+| corresponds to the first derivation rule of Kleene plus.
In that case, if we have a derivation of type |xs ∈Lˢ (r ⁺ˢ)|, then it is
trivial to show that we can get a derivation of type |xs ∈Lˢ r|.

\begin{code}
match-completeness (r ⁺ˢ) .((s₁ ++ s₂) ++ ys) k
    ((._ , ys) , refl , C+ {._}{s₁}{s₂} refl y inL , rest)
  with match r ((s₁ ++ s₂) ++ ys) k
... | just _ = tt
... | nothing
  with match r ((s₁ ++ s₂) ++ ys) ((r ⁺ˢ) ∷ k)
     | match-completeness r ((s₁ ++ s₂) ++ ys) ((r ⁺ˢ) ∷ k)
        (_ , append-assoc s₁ s₂ ys , y , (_ , ys) , refl , inL , rest)
... | nothing | ()
... | just _  | _ = tt
\end{code}

The constructor |C+| corresponds to the second derivation rule of Kleene plus.
We already had a split |xs ++ ys ≡ s|, so we can replace |s| with |xs ++ ys|.
The constructor |C+| gives us another split |s₁ ++ s₂ ≡ xs|, so we can replace
|xs| with |s₁ ++ s₂|. This means now we have |(s₁ ++ s₂) ++ ys| instead of |s|.

The definition of the Kleene plus case uses |_∣_|, which has to try and fail
the first case to return the second case. To satisfy that, we make a call to
|match r ((s₁ ++ s₂) ++ ys) k|.  If the call succeeds, then we satisfy the
first case of |_∣_|. If the call fails, then we verify that |s₁| matches |r|
and |s₂ ++ ys| matches the continuation.  We use the associative property of
appending lists to show that it is the same string.

\section{Higher-order intrinsic matcher}

The intrinsic matcher using list based continuation achieves what we want to
achieve with our matcher, but our initial question was to reimagine Harper's
continuation-passing style algorithm in Agda. Therefore we will also attempt
to write an intrinsic matcher that has functions as continuations.

A problem that arises with the function based continuations is regarding the
totality checker. It is not evident to Agda that our |match| function
terminates, because there is no obviously diminishing list of continuations
like the defunctionalized matcher. This is why we have to show Agda that our
recursive function really terminates, by providing an extra argument that is
obviously diminishing. We define it as following:

\begin{code}
data RecursionPermission {A : Set} : List A → Set where
  CanRec : {ys : List A}
         → ((xs : List A) → Suffix xs ys → RecursionPermission xs)
         → RecursionPermission ys
\end{code}

\subsection{Definition}

The main function for the higher-order intrinsic matcher is defined case by case as following:

\begin{code}
match : (C : Set)
      → (r : StdRegExp)
      → (s : List Char)
      → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
      → RecursionPermission s
      → Maybe C
\end{code}

The |match| function is now taking an extra argument |C| that helps us define
the continuation function and the return type.  The purpose for having |C| as
an argument is to be able to refer to the top level of the recursive calls in
every sub recursive call.

Notice that the continuation |k| is a function, unlike the defunctionalized
version, but similar to Harper's matcher. It is a function that possibly gives
a derivation (hence the |Maybe| type) for the entire string given that there is
a split of it such that the first part is in the language of |r|.

We also need an extra argument of type |RecursionPermission s| to explicitly
show Agda that the string |s| gets shorter in each recursive call. Remember
that to get a new |RecursionPermission s'| depending on an existing
|RecursionPermission s|, it has to be that |s'| is a strict suffix of |s|.

\subsubsection{Base cases}

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

\subsubsection{Concatenation}

\begin{code}
match C (r₁ ·ˢ r₂) s k (CanRec f) =
  match C r₁ s
        (λ {p}{s'} eq inL →
          match C r₂ s' (λ {p'}{s''} eq' inL' →
                          k {p ++ p'}{s''} (replace-right p s' p' s'' s eq' eq) ((p , p') , refl , inL , inL'))
                        (f _ (suffix-continuation eq inL))) (CanRec f)
\end{code}

In the concatenation case of the defunctionalized version, we could add |r₂| to
the list of continuations to be matched later.  However, the higher-order
matcher needs to construct a new continuation function. Once |r₁| was matched
with the beginning of the string, the continuation would match the rest of the
string with |r₂|.

Notice that to be able to call |match| with |r₂|, you need to prove that the
rest of the string is a strict suffix of the entire string so that you can get
a |RecursionPermission| for the rest. The function |suffix-continuation| does
exactly that.

\subsubsection{Alternation}

\begin{code}
match C (r₁ ⊕ˢ r₂) s k perm =
  match C r₁ s (λ eq inL → k eq (inj₁ inL)) perm ∣
  match C r₂ s (λ eq inL → k eq (inj₂ inL)) perm
\end{code}

The alternation case is similar to the defunctionalized version except the
continuations.  The matcher first tries to match |r₁| with |s| and tries to
match |r₂| only if the first one does not match.

\subsubsection{Kleene plus}

\begin{code}
match C (r ⁺ˢ) s k (CanRec f) =
  match C r s (λ eq inL → k eq (S+ inL)) (CanRec f) ∣
  match C r s (λ {p}{s'} eq inL →
                match C (r ⁺ˢ) s' (λ {p'}{s''} eq' inL' →
                                    k (replace-right p s' p' s'' s eq' eq) (C+ refl inL inL') )
                      (f _ (suffix-continuation eq inL))) (CanRec f)
\end{code}

The structure of the Kleene plus case is similar to the defunctionalized
version except the continuations.  The matcher first tries to match |r| with
|s| and tries to match the concatenation of |r| and |r ⁺ˢ| only if the first
try fails. Observe that the second try is similar to the |·ˢ| case.

\subsubsection{Accepting a string}
\begin{code}
  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = is-just (match _ r s empty-continuation (well-founded s))
\end{code}

We use the function |_acceptsˢ_| to see if a given |StdRegExp r| accepts a list
of characters |s| by calling our HOF matcher with |r,s| and an empty
continuation as well as a recursive permission for our list |s|. We define the
empty-continuation and the well-foundness of any list as follows:

\begin{code}
empty-continuation : ∀ {p' s' s'' r} → (p' ++ s'' ≡ s') → (p' ∈Lˢ r) → Maybe (s' ∈Lˢ r)
\end{code}

\begin{code}
well-founded : {A : Set} (ys : List A) → RecursionPermission ys
\end{code}


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

The type above translates to this: Suppose we have |C|, |r|, |s|, |k| and
|perm|. Suppose there exists a split of |p ++ s' ≡ s| such that there exists a
derivation of type |p ∈Lˢ r| such that the continuation called with those
arguments does not return |nothing|. Then we have to show that |match| function
does not fail.

Notice that we cannot make a stronger claim and say that the calls to the
continuation and the |match| function return the same derivations, because as
we showed before, derivations of the same type are not necessarily the same.

The base cases |∅ˢ| and |Litˢ| are trivial. Since the Kleene plus case captures
the essence of both concatenation and alternation cases, we will only explain
the completeness proof of the Kleene plus case.

\begin{code}
match-completeness C (r ⁺ˢ) s k (CanRec f) ((xs , ys) , eq , S+ x , m) =
  or-just (inj₁ (match-completeness C r s (λ {p}{s'} eq' inL' → k eq' (S+ inL')) (CanRec f) (_ , eq , x , m)))
\end{code}

\begin{code}
match-completeness C (r ⁺ˢ) ._ k (CanRec f) ((._ , ys) , refl , C+ {._}{s₁}{s₂} refl inL inL2 , m)
  with match-completeness C (r ⁺ˢ) (s₂ ++ ys) _ (f _ (suffix-continuation (append-assoc s₁ s₂ ys) inL))
                          (_ , refl , inL2 , subst (λ H → isJust (k H (C+ refl inL inL2))) (sym (uip _)) m)
... | pf = or-just {_}{match C r _ (λ eq inL → k eq (S+ inL)) (CanRec f)}
                    (inj₂ (match-completeness C r ((s₁ ++ s₂) ++ ys) _ _ (_ , append-assoc s₁ s₂ ys , inL , pf)))
\end{code}

\section{Overall matcher}

\subsection{Conversion from RegExp to StdRegExp}

\subsubsection{Definitions}

Notice that we defined our |match| functions in terms of standard form regular
expressions, in order to guarantee the termination. What we want at the end is
an |_accepts_| function in terms of |RegExp|, like Harper's. Therefore we should
define a new type |RegExp| and a function to convert |RegExp| to |StdRegExp|.

\begin{code}
data RegExp : Set where
  ∅ : RegExp
  ε : RegExp
  Lit : Char → RegExp
  _·_ : RegExp → RegExp → RegExp
  _⊕_ : RegExp → RegExp → RegExp
  _* : RegExp → RegExp
  G : RegExp → RegExp
\end{code}

|∅| is the empty set, |ε| is the empty string, |Lit| is the literal character,
|_·_| is concatenation, |_⊕_| is alternation, |_*| is Kleene star and |G| is
capturing group.

Capturing groups are not included in Harper's paper, but it is an operation we
often want to do with regular expressions and it is trivial to implement with
our intrinsic matchers. We will elaborate on this in the next section.

Similarly to |_∈Lˢ_|, we also define a notion of a string being in the language
of a regular expression:

\begin{code}
mutual
  _∈L_ : List Char → RegExp → Set
  _ ∈L ∅ = ⊥
  s ∈L ε = s ≡ []
  s ∈L (Lit c) = s ≡ c ∷ []
  s ∈L (r₁ ⊕ r₂) = (s ∈L r₁) ⊎ (s ∈L r₂)
  s ∈L (r₁ · r₂) =
    Σ (List Char × List Char) (λ { (p , q) → (p ++ q ≡ s) × (p ∈L r₁) × (q ∈L r₂) })
  s ∈L (r *) = s ∈Lˣ r
  s ∈L (G r) = s ∈L r

  data _∈Lˣ_ : List Char → RegExp → Set where
    Ex : ∀ {s r} → s ≡ [] → s ∈Lˣ r
    Cx : ∀ {s s₁ s₂ r} → s₁ ++ s₂ ≡ s → s₁ ∈L r → s₂ ∈Lˣ r → s ∈Lˣ r
\end{code}

Before we define the conversion function, we need a helper function that checks
if a regular expression accepts the empty string. Even though we can simply
define this as a function |RegExp → Bool|, proving it will be helpful for the
correctness of our overall program.

\begin{code}
δ' : (r : RegExp) → ([] ∈L r) ⊎ (¬ ([] ∈L r))
\end{code}

Using |δ'|, we can trivially define |δ : RegExp → Bool|.  We define a function
$\standardize$ as follows:

\begin{code}
standardize : RegExp → StdRegExp
standardize ∅ = ∅ˢ
standardize ε = ∅ˢ
standardize (Lit x) = Litˢ x
standardize (r₁ · r₂) with standardize r₁ | standardize r₂ | δ r₁ | δ r₂
... | x₁ | x₂ | false | false = x₁ ·ˢ x₂
... | x₁ | x₂ | false | true = x₁ ⊕ˢ (x₁ ·ˢ x₂)
... | x₁ | x₂ | true | false = x₂ ⊕ˢ (x₁ ·ˢ x₂)
... | x₁ | x₂ | true | true = x₁ ⊕ˢ x₂ ⊕ˢ (x₁ ·ˢ x₂)
standardize (r₁ ⊕ r₂) = standardize r₁ ⊕ˢ standardize r₂
standardize (r *) = (standardize r) ⁺ˢ
standardize (G r) = standardize r
\end{code}

Observe that the empty string language |ε| becomes the empty set |∅ˢ| and
Kleene star becomes Kleene plus. This definition directly follows
Harper's definition of standardization except the concatenation case.

Harper's definition of |δ| returns either |∅| or |ε|, hence the type of |δ| would be |RegExp → RegExp|.

If we try to directly follow Harper's standardization for concatenation, we
would have to write
% \ToDo{Harper's paper has a typo in that section, I don't know how to deal with that}
\begin{code}
standardize (r₁ · r₂) =
  ((δ r₁) ·ˢ (standardize r₂)) ⊕ˢ
  ((standardize r₁) ·ˢ (δ r₂)) ⊕ˢ
  ((standardize r₁) ·ˢ (standardize r₂))
\end{code}

Observe that this does not type check, because |_·ˢ_| requires two
|StdRegExp|s, yet Harper's definition of |δ| returns a |RegExp|.
Also observe that, if it did type check, for any |r|, both |∅ ·ˢ r| and
|r ·ˢ ∅| would effectively be equal to |∅|. Likewise, for any |r|, both
|ε ·ˢ r| and |r ·ˢ ε| would effectively be equal to |r|. Hence we can
simplify the parts of the alternation in Harper's concatenation standardization
process. In fact, it a given part is equal to |∅|, we do not have to include it
in the alternation at all.

If |r₁| accepts the empty string but |r₂| does not, using Harper's
standardization that does not type check in Agda, we would have
\begin{code}
(ε ·ˢ (standardize r₂)) ⊕ˢ ((standardize r₁) ·ˢ ∅) ⊕ˢ ((standardize r₁) ·ˢ (standardize r₂))
\end{code}
Using the observations we made above, we can simplify this to
\begin{code}
(standardize r₂) ⊕ˢ ((standardize r₁) ·ˢ (standardize r₂))
\end{code}
The simple version does type check, and it is what how we define the
concatenation case of |standardize|, where |δ r₁| is |true| but |δ r₂| is
|false|. The other cases are defined using the same observation.

Now that we have a complete |standardize| function, we can define |_accepts_| as follows:

\begin{code}
_accepts_ : RegExp → String → Bool
r accepts s with δ r | standardize r | String.toList s
... | true  | r' | xs = (null xs) ∨ (r' acceptsˢ xs)
... | false | r' | xs = r' acceptsˢ xs
\end{code}

If |r| accepts empty string, we return |true| if |xs| is empty or the
standardization of |r| accepts |xs|. If |r| does not accept the empty string,
then we only have the latter option.

\subsubsection{Verification}

We should prove
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
                  → (s : String)
                  → r accepts s ≡ true
                  → (String.toList s) ∈L r
correct-completeness : (r : RegExp)
                     → (s : String)
                     → (String.toList s) ∈L r
                     → r accepts s ≡ true
\end{code}

We also want to prove decidability:

\begin{code}
decidability : (r : RegExp)
             → (s : String)
             → ((String.toList s) ∈L r) ⊎ (¬ ((String.toList s) ∈L r))
\end{code}

\subsection{Capturing groups}

Capturing groups tell us which substring matches which part of the regular
expressions. For example, if our regular expression checks if a string is a
valid e-mail address, we might want to extract parts before and after the |@|
sign. Suppose we have a regular expression that accepts a single alphanumeric
character, namely |alphanumeric : RegExp|. Now we can define a very simple
regular expression for e-mail addresses, such as

\begin{code}
e-mail : RegExp
e-mail = G (alphanumeric *) · Lit '@' · G (alphanumeric *) · Lit '.' · G (alphanumeric *)
\end{code}

Now, if we match the string ``jdoe|@|wesleyan.edu" with |e-mail|, we want to be
able to extract ``jdoe", ``wesleyan" and ``edu".

One of the advantages of generating a derivation of type |xs ∈L r| for some
|xs| and |r| is that the derivation directly tells you which substring of |xs|
is matched by which part of |r|. All we have to do is to traverse the
derivation tree and add the ones matched by a capturing group to a list. We
want to obtain a list of strings at the end. The function to do this can be
defined as follows:

\begin{code}
extract : {r : RegExp} → {xs : List Char} → xs ∈L r → List (List Char)
extract {∅} ()
extract {ε} refl = []
extract {Lit x} refl = []
extract {r₁ · r₂} ((as , bs) , eq , a , b) = extract {r₁}{as} a ++ extract {r₂}{bs} b
extract {r₁ ⊕ r₂} (inj₁ x) = extract {r₁} x
extract {r₁ ⊕ r₂} (inj₂ y) = extract {r₂} y
extract {r *} (Ex refl) = []
extract {r *} (Cx {s}{s₁}{s₂} x x₁ inL) = extract {r} x₁ ++ extract {r *} inL
extract {G r}{xs} inL = xs ∷ extract {r} inL
\end{code}

To collect all the strings matched by capturing groups, we traverse the entire
derivation. Base cases |∅|, |ε|, |Lit| will return an empty list because if
they are captured by a group, the substring is already added to the list
in the previous recursive calls to |extract|. In concatenation, we make
two recursive calls and append the results because |r₁| and |r₂| match
different substrings and they may have different capturing groups inside
them. In alternation, the entire string matches either |r₁| or |r₂|, so we
make one recursive call to the one it matches. Kleene star case follows the
same principles.

\section{Conclusion}


\bibliographystyle{jfp}
\bibliography{paper}

\end{document}
