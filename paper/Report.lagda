\RequirePackage{amsmath}
\documentclass{jfp1}
\bibliographystyle{jfp}

\def\textmu{}

%include agda.fmt
\usepackage{textgreek} % not reproducible without textgreek
\usepackage{bussproofs}
\usepackage{color}
\usepackage{proof}

% Editorial commands
\newcommand{\Red}[1]{{\color{red} #1}}
\newcommand{\ToDo}[1]{{\color{blue} ToDo: #1}}
\newcommand{\tocite}[0]{{\color{red} [cite]}\xspace}

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

\title{Functional Pearl: Intrinsic Verification \break of a Regular Expression Matcher}
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

Regular expression matching is a venerable problem, studied in many
programming and theory of computation courses.  Harper~\cite{harper}
presents a higher-order algorithm for regular expression matching, using
continuation-passing to store the remainder of a matching problem when a
concatenation is encountered, while using the host-language's control
stack to represent the branching when an alternation or Kleene star is
encoutered.  The code for the matcher is quite short, but also quite
subtle; the emphasis of Harper's paper is on how the correctness proof
for the matcher informs the reader's understanding of the code.  For
example, the first matcher presented has a termination bug, which is
revealed when the induction in the correctness proof breaks down.  The
problem can be fixed by restricting the domain of the function to
\emph{standard} regular expressions, which have no Kleene-stared
subexpressions that accept the empty string, and using a preprocessor
translation to cover all regular expressions and hence solve the
original problem.  Harper's algorithm has been used in first- and
second-year functional programming courses at Carnegie Mellon for more
than 20 years, as a high-water example of integrating programming and
program verification.  A later paper by Yi~\cite{Yi06regexp} revisits
the example, motivated by the author's sense that the higher-order
matcher is too difficult for students in their introductory programming
course, and gives a first-order matcher based on compilation to a state
machine.

Because of this algorithm's strong interplay between program and proof
and its pedagogical usefulness, we set out to formalize the algorithm
using the Agda proof assistant~\cite{norell07thesis}, believing that it
could be a pedagogically useful example of dependently typed
programming.  The process of mechanizing the algorithm led us to a few
new observations that streamline the presentation of the
algorithm---which was quite surprising to the third author, who has
previously taught this material several times and thought hard about how
to present it.  Our goal in this pearl paper is to document these
variations on the matching algorithm, and how the process of programming
it in Agda led us to them.

In partciular, we make three new observations.  First, because Agda is a
total language, we must make the termination of the matcher evident in
the code itself.  Harper's original algorithm can be shown to terminate
using lexicographic induction on first the regular expression and second
well-founded induction on the string being matched, but in Agda the
latter requires passing an explicit termination measure.  In an attempt
to avoid this, we discovered that
\emph{defunctionalizing}~\cite{danvyetc} the matcher avoids the explicit
termination argument, because the problematic recursive call is moved
from the Kleene star case to the character literal base case, where it
is clear that the string is getting smaller.  The defunctionalized
matcher is of interest not only because programming it in Agda is
simpler: it also achieves Yi's goal of a first-order matcher in a simple
way, which has a clear relationship to the higher-order matcher.
Pedagogically, it could be used at a point in a course before
higher-order functions have been introduced, and it could be used as a
stepping stone to the more sophisticated higher-order matcher.

Second, the matcher discussed in Harper's paper, whose Agda type is
\begin{code}
_accepts_ : RegExp → String → Bool
\end{code}
determines whether or not a string is accepted by a regular expression.
However, for most applications of regexp matching (and for making
compelling homework assignments), it is useful to allow a ``brakcet'' or
``grouping'' construct that allows the user to specify
sub-regular-expressions whose matching strings should be reported---
e.g. |ACG[.*]TAC[(G⊕C)*]GA| for extracting the parts of a DNA string
surrounded by certain signal codes.  When coding a program/proof in a
dependently typed language, there is a choice between ``extrinsic''
verification (write the simply-typed code, and then prove it correct)
and ``intrinsic verification'' (fuse the program and proof into one
function, with a dependent type).  We have formalized both a
straightforward extrinsic verification, and an intrinsically
\emph{sound} verification, which has the dependent type
\begin{code}
_FIXMEWHATISTHISCALLEDINTHECODE?_ : (r : RegExp) (s : String) → Maybe (s ∈L r)
\end{code}
All formalizations are availabe online~\footnote{FIXME URL for repo}.  That is, when
the matcher succeeds, it returns the derivation that the string is in
the language of the regexp (completeness, which says that the matcher
does not improperly reject strings, is still proved separately).  The
reason for this choice is that the \emph{computational content} of the
soundness proof is relevant to the above problem: the derivation gives a
parse tree, which allows reporting the matching strings for each
specified sub-expression.  Indeed, we first realized this for the
extrinsic matcher, running the separate soundness proof to produce the
matching strings.  However, running the matcher and then its soundness
proof (which has success of the matcher as a precondition) duplicates
work, so we present the intrinsic version in the paper.  

A third observation, is that, while Harper uses a negative semantic
definition of standard regular expressions (``no subexpression of the
form $r^*$ accepts the empty string''), it is often more convenient in
Agda to use positive/inductive criteria.  While formalizing the notion
of stadard, we realized that it is possible to instead use a syntactic
criterion, generating standard regular expressions by literals,
concatenation, alternation, and Kleene \emph{plus} (one or more
occurences) instead of Kleene \emph{star} (zero or more occurences), and
omitting the empty string regexp |ε|.  While the syntactic criterion
omits some semantically valid expression (e.g. |(ε · r)*|, where |r|
does not accept the empty string), it still suffices to define a matcher
for all regular expression by translation.  In addition to simplifying
the Agda formalization, this observation has the pedagogical benefit of
allowing a self-contained treatment of these syntactically standard
regular expressions.

Though dependently typed programming led us to these new insights into a
problem that has been very throughly studied from a very similar point
of view, they can all be ported back to simply-typed languages.  Thus,
in addition to being a strong pedagogical example of dependently typed
programming, these variations on regular expression matching could be
used in introductory programming courses to offer a streamlined
unit---e.g. using the defunctionalized matcher for only standard regular
expressions, which still captures the basic interplay between
programming and proof---which scales to higher-order matching and more
interesting homework assignments---e.g. by computing matching strings.
Therefore, even though there is existing work on parsing in a total
programming language~\cite{danielsson}, which includes regular
expression matching as a special cases, we believe these variations on
Harper's algorithm will be of interest to the dependent types and
broader functional programming communities.  

The remainder of this paper is organized as follows.  <TODO>

\subsection{Agda Definitions}

We assume the reader is familiar with
Agda~\cite{norell07thesis,dybjertutorial} and the notation from the Agda
standard library~\cite{danielson}.  Though the Agda library
differentiates between strings (|String|) and lists of characters (|List
Char|), we will ignore this distinction in the paper.  Because the
intrinsically verified matcher returns a |Maybe|/option type, it will be
useful to use monadic notation for |Maybe| (in Haskell terminology,
|_∣_| is |mplus| and |map| is |fmap|):

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

\section{Syntactically standard regular expressions}

Rather than Harper's negative semantic criterion (no starred
subexpression accepts the empty string), we use an inductive definition
of standard regular expressions.  Compared with the standard grammar of
the regexp matching the empty string (|ε|), the regexp matching the
empty language (|∅|), character literals, concatenation (|r₁ · r₂|),
alternation |(r₁ ⊕ˢ r₂)|, and Kleene star/repitition (|r⁺|), we omit ε,
and replace Kleene star with Kleene plus, which represents repitition
one or more times.  As an operator on regular languages, Kleene plus
($\Sigma^+$) is equivalent to $\Sigma · \Sigma^* $, where $\Sigma^*$ is
the Kleene star.

In Agda, we define a type of |StdRegExp| as follows:

\begin{code}
data StdRegExp : Set where
  ∅ˢ : StdRegExp
  Litˢ : Char → StdRegExp
  _·ˢ_ : StdRegExp → StdRegExp → StdRegExp
  _⊕ˢ_ : StdRegExp → StdRegExp → StdRegExp
  _⁺ˢ : StdRegExp → StdRegExp
\end{code}
|∅ˢ| is the empty set, |Litˢ| is the character literal, |_·ˢ_| is
concatenation, |_⊕ˢ_| is alternation, and |_⁺ˢ| is Kleene plus.  We use
the |ˢ| superscript to differentiate standard regular expressions from
the the full language, which is defined in
Section~\ref{sec:standardization}.

Informally, Kleene plus is defined as the least language closed under
the following rules:

\[
\infer{s \in L(|r ⁺ˢ|)}
      {s \in L(|r|)}
\qquad
\infer{s \in L(|r ⁺ˢ|)}
      {s_1 s_2 = s &
        s_1 \in L(|r|) &
        s_2 \in L(|r ⁺ˢ|)}
\]

In Agda, we represent sets of strings by something analogous to their
membership predicates.  For standard regular expressions, we define a
binary relation |s ∈Lˢ r|, which means |s| is in the language of |r|, by
recursion on |r|, illustrating how it is possible to compute types based
on values in a dependently typed language.  This uses an auxilary,
inductively definition relation |s ∈L⁺ r|, represented by an Agda
inductively defined datatype family, which corresponds to the inference
rules above.

\begin{code}
mutual
  _∈Lˢ_ : List Char → StdRegExp → Set
  _ ∈Lˢ ∅ˢ = ⊥
  s ∈Lˢ (Litˢ c) = s ≡ [ c ]
  s ∈Lˢ (r₁ ⊕ˢ r₂) = (s ∈Lˢ r₁) ⊎ (s ∈Lˢ r₂)
  s ∈Lˢ (r₁ ·ˢ r₂) =
    Σ (List Char × List Char) (λ { (p , q)  → (p ++ q ≡ s) × (p ∈Lˢ r₁) × (q ∈Lˢ r₂) })
  s ∈Lˢ (r ⁺ˢ) = s ∈L⁺ r

  data _∈L⁺_ : List Char → StdRegExp → Set where
      S+ : ∀ {s r} → s ∈Lˢ r → s ∈L⁺ r
      C+ : ∀ {s s₁ s₂ r} → s₁ ++ s₂ ≡ s → s₁ ∈Lˢ r → s₂ ∈L⁺ r → s ∈L⁺ r
\end{code}

Here, |⊥| is the empty Agda type and |⊎| is disjoint union (|Either|),
and × is the pair type.  |Σ A (λ x → B)| is an existential/dependent
pair, where the type of the second component depends on the value of the
first---because this is not built in in Agda, it takes a type |A| and a
function from |A| to |Set| as arguments.  The notation |λ {p → e}|
allows a pattern-matching anonymous function.  
The function |++| appends lists, and |≡ is| Agda's
propositional equality.  Thus, in full, the clause for alternation means
``there exist strings |p| and |q| such that appending |p| and |q| gives
|s|, where |p| is in the language of |r₁| and |q| is in the language of
|r₂|.

However, is is important to note that these membership ``predicates''
land in |Set|, the Agda type of types, and thus may have computational
content.  For example, a witness that |s ∈Lˢ (r₁ ⊕ r₂)| includes a bit
(|Inl|) or (|Inr|) that tells which possibility was taken, and 
a witness |s ∈L⁺ r| is a non-empty list of strings matching |r|, which
concatentate to |s|.  Thus, there can be different witnesses that the
a string matches a regular expression, such as 

\begin{prooftree}
    \AxiomC{$``a" \in L(|Litˢ 'a'|)$}
\LeftLabel{Derivation A $:=$}
  \UnaryInfC{$``a" \in L(|Litˢ 'a' ⁺ˢ|)$}
\end{prooftree}

\begin{prooftree}
    \AxiomC{$``a" \plus ``a" = ``aaa"$}
    \AxiomC{$``a" \in L(|Litˢ 'a'|)$}
    \AxiomC{Derivation A}
\LeftLabel{Derivation B $:=$}
  \TrinaryInfC{$``aa" \in L(|Litˢ 'a' ⁺ˢ|)$}
\end{prooftree}

\begin{prooftree}
  \AxiomC{$``a" \plus ``aa" = ``aaa"$}
  \AxiomC{Derivation A}
  \AxiomC{Derivation B}
\LeftLabel{Derivation C $:=$}
  \TrinaryInfC{$``aaa" \in L(|(Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ)|)$}
\end{prooftree}

\begin{prooftree}
  \AxiomC{$``aa" \plus ``a" = ``aaa"$}
  \AxiomC{Derivation B}
  \AxiomC{Derivation A}
\LeftLabel{Derivation D $:=$}
  \TrinaryInfC{$``aaa" \in L(|(Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ)|)$}
\end{prooftree}

We will exploit this in Section~\ref{sec:groups} to extract the strings
matching subexpressions.

% two different values in the same type written in Agda

% \begin{code}
% ex₁ : ('a' ∷ 'a' ∷ 'a' ∷ []) ∈Lˢ ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))
% ex₂ : ('a' ∷ 'a' ∷ 'a' ∷ []) ∈Lˢ ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))
% ex₁ = ('a' ∷ [] , 'a' ∷ 'a' ∷ []) , refl , S+ refl , C+ refl refl (S+ refl)
% ex₂ = ('a' ∷ 'a' ∷ [] , 'a' ∷ []) , refl , C+ refl refl (S+ refl) , S+ refl
% \end{code}

\section{Defunctionalized intrinsic matcher}

In this section, we define a first-order matcher for standard regular
expressions.  This is a defunctionalization of Harper's algorithm,
though we will describe it from first principles.  The idea is to
generalize from matching a string |s| against a regular expression |r|
by adding an additional stack of regular expressions |k| that need to be
matched against the suffix |s| if some prefix matches |r|.  We represent
the stack by a list, and say that a string is in the language of a stack
if it splits into strings in the language of each stack element:
\begin{code}
_∈Lᵏ_ : List Char → List StdRegExp → Set
s ∈Lᵏ [] = s ≡ []
s ∈Lᵏ (r ∷ rs) =
  Σ (List Char × List Char) (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × (s' ∈Lᵏ rs) })
\end{code}
If the stack is empty, the string also has to be empty.  If the stack
has a head, then a prefix of the string should match the head of the
list and the rest of the string should match with the rest of the list.  

\subsection{Definition}

The soundness part of informal description of the matcher given above
translates into the following dependent type/specification:
\begin{code}
match : (r : StdRegExp)
      → (s : List Char)
      → (k : List StdRegExp)
      → Maybe (Σ (List Char × List Char)
              (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
\end{code}
This says that the matcher takes a regular expression |r|, a string |s|
and a stack |k|, and creates a splitting of the original list |s| into
lists |p| and |s'| and, if matching succeeds, returns a splitting |(p ++
s' ≡ s)|, a derivation that |p| is in the language of |r| and a
derivation that |s'| is in the language of the stack |k|.  This
specifies the soundness of successful matching, and has computational
content that will let us extract matching strings, but leaves open the
possiblity that the matcher fails incorrectly (for example, the
constantly |nothing| function has this type)---this will be addressed in
the completeness proof below.

The complete code is in
Figure~\ref{fig:intrinsic-defunctionalized-matcher}.  Agda can verify
that this function terminates by induction on first the string |s|, and
then the regular expression |r|.  \ToDo{FIXME is this what we said?}.
We now discuss the code case by case.

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

The |isEqual x c| call has type |Maybe (x ≡ c)|---i.e. it optionally
shows that |x| is equal to |c|.  Thus, by the monad bind, if we are
trying to match an empty list with a regular expression that requires a
character, the matcher fails.  If not, we try to match the first
character of the string to |c| and then match the stack |k| against the
suffix using |match-helper|.  

The function |match-helper| is mutually recursive with our matcher and
is defined as follows:
\begin{code}
match-helper : (k : List StdRegExp) → (s : List Char) → Maybe (s ∈Lᵏ k)
match-helper [] [] = return refl
match-helper [] (x ∷ s) = fail
match-helper (r ∷ rs) s = match r s rs
\end{code}
It succeeds when matching the emptry string against the empty stack,
fails when matching a non-empty string against the empty stack, and
otherwise refers back to |match|.  Relative to Harper's algorithm, this
is the application function for the defunctionalized continuation.  

Returning to the character literal case, if the first character in our
list matches the character literal |c|, then we call |match-helper| on
the continuation and the rest of the list, which will produce a
derivation of |s ∈Lᵏ k| if the rest of the list indeed matches the rest
of the |StdRegExp|s in |k|.  The remainder of the code packages this as
a pair showing that therefore the list |x :: s| splits as |[ x ] ∈Lˢ
(Lit c)| and |s ∈Lᵏ k|.

Agda's termination checker is able to verify that, for the call from
|match| to |match-helper| and back to |match|, the string |x ∷ xs|
becomes |xs|, and is therefore smaller, which justifies termination in
this case.  

\subsubsection{Concatenation}

\begin{code}
match (r₁ ·ˢ r₂) s k =
  map (reassociate-left {R = _·ˢ_} (λ inL inL' → _ , refl , inL , inL'))
    (match r₁ s (r₂ ∷ k))
\end{code}

In the case for concatenation |r₁ ·ˢ r₂|, match against |r₁| first, and
add |r₂| to the stack |k|.  Calling |match r₁ s (r₂ ∷ k)| will give us a
split |xs ++ ys ≡ s| and derivations of |xs ∈Lˢ r₁| and |ys ∈Lᵏ (r₂ ∷
k)|. If we unpack the second derivation (using the definition of |∈Lᵏ|
and the fact that our continuation list contains at least one element,
|r₂|), we will have another split |as ++ bs ≡ ys| and derivations |as
∈Lˢ r₂| and |bs ∈Lᵏ k|.  The helper function |reassociate-left| states
that if we have such a situation, we can reassociate it to show that |xs
++ as| matching the entire regular expression |r₁ ·ˢ r₂|.

FIXME show type of |reassociate-left|

\subsubsection{Alternation}

\begin{code}
match (r₁ ⊕ˢ r₂) s k =
  (map (change-∈L inj₁) (match r₁ s k)) ∣
  (map (change-∈L inj₂) (match r₂ s k))
\end{code}

In the alternation case, we match the string with the first part of the
alternation, and if that fails we try to match with the second part.  If
the call |match r₁ s k| succeeds, it will contain a triple splitting |s|
as |p ++ s'|, with a derivation of |p ∈Lˢ r₁| and |s' ∈Lᵏ s'|.  However
the return type for the alternation case should contain a derivation of
type |p ∈Lˢ (r₁ ⊕ˢ r₂)|, so we use the helper function |change-∈L|,
which applies a function to this position of the result triple, to make
the appropriate modification:
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

In the Kleene plus case, we first try to match |s| with just |r|, and if that
succeeds we apply |change-∈L S+| to the derivation since we matched from the
single |r| case. If this fails, then similar to the |·ˢ| case, we try to match
a prefix of the string to |r| and then the suffix that follows with the
continuation which now includes |r ⁺ˢ|. Just like in the |·ˢ| case, we use
|reassociate-left| in order to get that our splitting of |s| matches the entire
starting |r|.

\begin{figure}
\figrule
\begin{code}
match : (r : StdRegExp)
      → (s : List Char)
      → (k : List StdRegExp)
      → Maybe (Σ (List Char × List Char)
              (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
match ∅ˢ s k = fail
match (Litˢ c) (x ∷ xs) k =
  (isEqual x c) >>=
    (λ p → map (λ pf → ((([ c ] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf)))
               (match-helper k xs))
match (r₁ ·ˢ r₂) s k =
  map (reassociate-left {R = _·ˢ_} (λ inL inL' → _ , refl , inL , inL'))
    (match r₁ s (r₂ ∷ k))
match (r₁ ⊕ˢ r₂) s k =
  (map (change-∈L inj₁) (match r₁ s k)) ∣
  (map (change-∈L inj₂) (match r₂ s k))
match (r ⁺ˢ) s k =
  (map (change-∈L S+) (match r s k)) ∣
  (map (reassociate-left {R = λ r _ → r ⁺ˢ} (λ inL inL' → C+ refl inL inL'))
    (match r s ((r ⁺ˢ) ∷ k)))
\end{code}
\caption{Complete definition of the |match| function for
  the defunctionalized intrinsic matcher.}
\label{fig:intrinsic-defunctionalized-matcher}
\figrule
\end{figure}

\subsubsection{Acceptance by StdRegExp}

\begin{code}
_acceptsˢ_ : StdRegExp → List Char → Bool
r acceptsˢ s = is-just (match r s [])
\end{code}

We use the function |_acceptsˢ_| to see if a given standard regular expression
accepts a list of characters by calling our matcher with a continuation base
case. If our |match| function returns a derivation, then we know that the
string is accepted by the standard form regular expression.

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
version except for the continuations.  The matcher first tries to match |r| with
|s| and tries to match the concatenation of |r| and |r ⁺ˢ| only if the first
try fails. Observe that the second try is similar to the |·ˢ| case.

\begin{figure}
\figrule
\begin{code}
match : (C : Set)
      → (r : StdRegExp)
      → (s : List Char)
      → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
      → RecursionPermission s
      → Maybe C
match C ∅ˢ s k perm = fail
match C (Litˢ x) [] k perm = fail
match C (Litˢ x) (y ∷ ys) k perm with y Data.Char.≟ x
... | no _ = fail
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
\caption{Complete definition of the |match| function for
  the higher-order intrinsic matcher.}
\figrule
\end{figure}

\subsubsection{Acceptance by StdRegExp}
\begin{code}
_acceptsˢ_ : StdRegExp → List Char → Bool
r acceptsˢ s = is-just (match _ r s empty-continuation (well-founded s))
\end{code}

We use the function |_acceptsˢ_| to see if a given standard regular expression
accepts a list of characters by calling our matcher with a continuation base
case as well as a |RecursionPermission| for the list of characters. We define
the |empty-continuation| as a continuation base case and |well-founded| to
obtain a |RecursionPermission| for the initial list of characters.

\begin{code}
empty-continuation : ∀ {p' s' s'' r} → (p' ++ s'' ≡ s') → (p' ∈Lˢ r) → Maybe (s' ∈Lˢ r)
\end{code}
|empty-continuation| is our higher order function substitute of the empty list |[]| we used as an empty continuation in our defunctionalized version. This function takes a splitting of a string |s'| as well as a proof that its first part |p'|, is in the language of |r| and then returns either |nothing| if the second part of the string |s'|, |s''| is not empty, or |Just (s' ∈Lˢ r)| if |s''| is empty.

\begin{code}
well-founded : {A : Set} (ys : List A) → RecursionPermission ys
\end{code}
|well-founded| just gives us a |RecursionPermission| for any given list.


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
arguments does not return |nothing|. Then we have to show that the |match| function
does not fail.

Notice that we cannot make a stronger claim and say that the calls to the
continuation and the |match| function return the same derivations, because as
we showed before, derivations of the same type are not necessarily the same.

The proof follows the same pattern as the proof of |match-completeness| for the
defunctionalized version by basically using the inductive hypotheses in the same
way. Refer to the supplement code.

\section{Overall matcher}

\subsection{Conversion from RegExp to StdRegExp}

\subsubsection{Definitions}

Notice that we defined our |match| functions in terms of standard form regular
expressions, in order to guarantee termination. What we want at the end is
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
often want to use with regular expressions and it is trivial to implement with
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

The definition of |_∈L_| is the same as |_∈Lˢ_| except for three cases. We now have
a case for |ε| that requires an empty string. The Kleene star case is very
similar to the Kleene plus case. |Cx| and |C+| are very similarly defined, but
|Ex| is requires an empty string, while |S+| does not.

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
process. In fact, if a given part is equal to |∅|, we do not have to include it
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
The simple version does type check, and it is how we define the
concatenation case of |standardize|, where |δ r₁| is |true| but |δ r₂| is
|false|. The other cases are defined using the same observation.

Now that we have a complete |standardize| function, we can define |_accepts_| as follows:

\begin{code}
_accepts_ : RegExp → String → Bool
r accepts s with δ r | standardize r | String.toList s
... | true  | r' | xs = (null xs) ∨ (r' acceptsˢ xs)
... | false | r' | xs = r' acceptsˢ xs
\end{code}

If |r| accepts the empty string, we return |true| if |xs| is empty or the
standardization of |r| accepts |xs|. If |r| does not accept the empty string,
then we only have the latter option.

Note that we use |_acceptsˢ_| in this definition. Our definitions of it in
the defunctionalized and higher-order matchers are different, but they have
the same type, therefore the definition of |_accepts_| is independent of
which matcher we choose to use.

\subsubsection{Verification}

Now we want to prove the relationship between |RegExp|s and |StdRegExp|s. We want to prove that a string |s| is in the language of a regular
expression |r| if and only if, either the string is empty, or |s| is in the language of the standardized version of |r|.

$$(\forall s) \; \big[ s \in L(r) \Longleftrightarrow \left[ (\delta(r) = true \land s = []) \lor s \in L( \standardize (r))\right] \big]$$

We are going to prove the above theorem in Agda.

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

Once we prove this theorem, we can present the overall theorem:

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
\label{sec:groups}

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

% TODO

\bibliography{paper}

\end{document}
