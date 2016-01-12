\RequirePackage{amsmath}
\documentclass{jfp1}
\bibliographystyle{jfp}

\def\textmu{}

%include agda.fmt
\usepackage{textgreek} % not reproducible without textgreek
\usepackage{bussproofs}
\usepackage{color}
\usepackage{proof}
\usepackage{url}

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

\title{Intrinsic Verification \break of a Regular Expression Matcher}
\author[Joomy Korkut, Maksim Trifunovski, Daniel R. Licata]
       {JOOMY KORKUT, MAKSIM TRIFUNOVSKI, DANIEL R. LICATA\\
        Wesleyan University}


\begin{document}

\maketitle[f]

\begin{abstract}
Harper's 1999 Functional Pearl on regular expression matching is a
strong example of the interplay between programming and proof, and has
been used for many years in introductory functional programming classes.
In this paper, we revisit this algorithm from the point of view of
dependently typed programming.  In the process of formalizing the
algorithm and its correctness using the Agda proof assistant, we found
three interesting variations.  First, defunctionalizing the matcher
allows Agda to see termination without an explicit metric, and provides
a simple first-order matcher with a clear relationship to the original,
giving an alternative to a later Educational Pearl by Yi.  Second,
intrinsically verifying the soundness of the algorithm has useful
computational content, allowing the extraction of matching strings from
the parse tree.  Third, while Harper uses a negative definition of
\emph{standard} regular expressions (no starred subexpression accepts
the empty string), using a syntactic definition of standardness
simplifies the staging of the development.  These variations provide a
nice illustration of the benefits of thinking in a dependently typed
language, and have some pedagogical value for streamlining and extending
the presentation of this material.
\end{abstract}

\tableofcontents

\section{Introduction}

Regular expression matching is a venerable problem, studied in many
programming and theory of computation courses.  Harper~\cite{harper}
presents a higher-order algorithm for regular expression matching, using
continuation-passing to store the remainder of a matching problem when a
concatenation is encountered, while using the ordinary control stack to
represent the branching when an alternation is encountered.  The code for
the matcher is quite short, but also quite subtle; the emphasis of
Harper's paper is on how the correctness proof for the matcher informs
the reader's understanding of the code.  For example, the first matcher
presented has a termination bug, which is revealed when the induction in
the correctness proof breaks down.  The problem can be fixed by
restricting the domain of the function to \emph{standard} regular
expressions, which have no Kleene-stared subexpressions that accept the
empty string, and then using a preprocessor translation to solve the
original problem.  Harper's algorithm has been used in first- and
second-year functional programming courses at Carnegie Mellon for around
20 years, as a high-water example of integrating programming and program
verification.  A later paper by Yi~\cite{Yi06regexp} revisits the
example, motivated by the author's sense that the higher-order matcher
is too difficult for students in their introductory programming course,
and gives a first-order matcher based on compilation to a state machine.

Motivated by its strong interplay between programming and proof and its
pedagogical usefulness, we set out to formalize Harper's algorithm using
the Agda proof assistant~\cite{norell07thesis}, believing that it could
be a pedagogically useful example of dependently typed programming.  The
process of mechanizing the algorithm led us to a few new observations
that streamline and extend its presentation---which was quite surprising
to the third author, who has previously taught this material several
times.  Our goal in this paper is to document these variations on the
matching algorithm, and how the process of programming it in Agda led us
to them.

The three variations are as follows.  First, because Agda is a total
language, we must make the termination of the matcher evident in the
code itself.  Harper's original algorithm can be shown to terminate
using lexicographic induction on first the regular expression and second
well-founded induction on the string being matched, but in Agda the
latter requires passing an explicit termination measure.  We discovered
that \emph{defunctionalizing}~\cite{reynolds72definitional} the matcher
avoids the explicit termination measure, because the problematic
recursive call is moved from the Kleene star case to the character
literal base case, where it is clear that the string is getting smaller.
The defunctionalized matcher is of interest not only because programming
it in Agda is simpler: it also achieves Yi's goal of a first-order
matcher in a simple way, which has a clear relationship to the
higher-order matcher.  Pedagogically, it could be used at a point in a
course before higher-order functions have been introduced, and it could
be used as a stepping stone to the more sophisticated higher-order
matcher.

Second, the matcher discussed in Harper's paper, whose Agda type is
\begin{code}
_accepts_ : RegExp → String → Bool
\end{code}
determines whether or not a string is accepted by a regular expression.
However, for most applications of regexp matching (and for making
compelling homework assignments), it is useful to allow a ``bracket'' or
``grouping'' construct that allows the user to specify
sub-regular-expressions whose matching strings should be reported--- for
example, |AG[.*]TC[(G⊕C)*]GA| for extracting the parts of a DNA string
surrounded by certain signal codes.  When coding a program/proof in a
dependently typed language, there is a choice between ``extrinsic''
verification (write the simply-typed code, and then prove it correct)
and ``intrinsic verification'' (fuse the program and proof into one
function, with a dependent type).  We have formalized both a
straightforward extrinsic verification, and an intrinsically
\emph{sound} verification\footnote{All formalizations are available from
  \url{http://github.com/joom/regexp-agda}. Use Agda version 2.4.2.2
  with standard library version 0.11}, which has the dependent type
\begin{code}
accepts-intrinsic : (r : RegExp) → (s : List Char) → Maybe (s ∈L r)
\end{code}
When this matcher succeeds, it returns the derivation that the string is
in the language of the regexp; completeness, which says that the matcher
does not improperly reject strings, is still proved separately.  The
reason for this choice is that the \emph{computational content} of the
soundness proof is relevant to the above problem: the derivation gives a
parse tree, which allows reporting the matching strings for each
specified sub-expression.  Indeed, even for the extrinsic matcher, one
can run the separate soundness proof to produce the matching
strings---but running the matcher and then its soundness proof (which
has success of the matcher as a precondition) duplicates work, so we
present the intrinsic version in the paper.  Though we were led to this
variation by coding the soundness proof of the matcher using dependent
types, analogous code could be used in a simply typed language, with the
less informative result type |Maybe Derivation| which does not say what
string and regexp it is a derivation for.

A third variation is that, while Harper uses a negative semantic
definition of standard regular expressions (``no subexpression of the
form $r^*$ accepts the empty string''), it is often more convenient in
Agda to use positive/inductive criteria.  While formalizing the notion
of standard, we realized that it is possible to instead use a syntactic
criterion, generating standard regular expressions by literals,
concatenation, alternation, and Kleene \emph{plus} (one or more
occurrences) instead of Kleene \emph{star} (zero or more occurrences), and
omitting the empty string regexp |ε|.  While the syntactic criterion
omits some semantically standard expression (such as |(ε · r)*|, where |r|
does not accept the empty string), it still suffices to define a matcher
for all regular expression.  In addition to simplifying the Agda
formalization, this observation has the pedagogical benefit of allowing
a self-contained treatment of these syntactically standard regular
expressions.

Though dependently typed programming led us to these new insights into a
problem that has been very thoroughly studied from a very similar point
of view, they can all be ported back to simply-typed languages.  Thus,
in addition to being a strong pedagogical example of dependently typed
programming, these variations on regular expression matching could be
used in introductory programming courses to offer a streamlined
treatment---e.g. using the defunctionalized matcher for only
syntactically standard regular expressions, which still captures the
basic interplay between programming and proof---which scales to
higher-order matching and more interesting homework
assignments---e.g. by computing matching strings.  Therefore, even
though there is existing work on verified parsing of regular expressions
and context-free grammars in a dependently typed programming language
(such as \cite{danielsson10totalparser,ridge11cfg,firsov+13parsing}), we
believe these new variations on Harper's algorithm will be of interest
to the dependent types and broader functional programming communities.

The remainder of this paper is organized as follows.  In
Section~\ref{sec:standard}, we define syntactically standard regular
expressions.  In Section~\ref{sec:defunc}, we give an intrinsically
sound defunctionalized matcher, with no explicit termination measure.
In Section~\ref{sec:hof}, we give an intrinsically sound higher-order
matcher, which uses an explicit termination measure, and explain the
correspondence with the defunctionalized matcher.  In
Section~\ref{sec:nonstandard}, we show that these matchers suffice to
match all regular expressions by translation.  In
Section~\ref{sec:groups} we discuss how to extract matching strings.

\subsection{Agda Definitions}

We assume the reader is familiar with Agda~\cite{norell07thesis} and the
notation from the Agda standard library.  Though the Agda library
differentiates between strings (|String|) and lists of characters (|List
Char|), we will ignore this distinction in the paper.  Because the
intrinsically verified matcher returns a |Maybe|/option type, it will be
useful to use monadic notation for |Maybe| (in Haskell terminology,
|_∣∣_| is |mplus| and |map| is |fmap|):

\begin{code}
return : ∀ {A} → A → Maybe A
return = just

fail : ∀ {A} → Maybe A
fail = nothing

_>>=_ : ∀ {A B} → Maybe A → (A → Maybe B) → Maybe B
just x >>= f = f x
nothing >>= f = nothing

_∣∣_ : ∀ {A} → Maybe A → Maybe A → Maybe A
just x | _ = just x
nothing | y = y

map : ∀ {A B} → (A → B) → Maybe A → Maybe B
map f (just x) = just (f x)
map _ nothing  = nothing
\end{code}

\section{Syntactically standard regular expressions}
\label{sec:standard}

Rather than Harper's negative semantic criterion (no starred
subexpression accepts the empty string), we use an inductive definition
of standard regular expressions.  Compared with the standard grammar of
regular expressions, which includes the regexp matching the empty string
(|ε|), the regexp matching the empty language (|∅|), character literals,
concatenation (|r₁ · r₂|), alternation |(r₁ ⊕ˢ r₂)|, and Kleene
star/repetition (|r*|), we omit ε, and replace Kleene star with Kleene
plus, which represents repetition one or more times.  As an operator on
regular languages, Kleene plus ($\Sigma^+$) is equivalent to $\Sigma
\cdot \Sigma^* $, where $\Sigma^*$ is the Kleene star.

In Agda, we define a type of |StdRegExp| as follows:

\begin{code}
data StdRegExp : Set where
  ∅ˢ : StdRegExp
  Litˢ : Char → StdRegExp
  _·ˢ_ : StdRegExp → StdRegExp → StdRegExp
  _⊕ˢ_ : StdRegExp → StdRegExp → StdRegExp
  _⁺ˢ : StdRegExp → StdRegExp
\end{code}
|∅ˢ| is the regular expression matching no strings, |Litˢ| is the
character literal, |_·ˢ_| is concatenation, |_⊕ˢ_| is alternation, and
|_⁺ˢ| is Kleene plus.  We use the |ˢ| superscript to differentiate
standard regular expressions from the the full language, which is
defined in Section~\ref{sec:nonstandard}.

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
\noindent In Agda, we represent sets of strings by something analogous to their
membership predicates.  For standard regular expressions, we define a
binary relation |s ∈Lˢ r|, which means |s| is in the language of |r|, by
recursion on |r|, illustrating how it is possible to compute types based
on values in a dependently typed language.  This uses an auxiliary,
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
\noindent Here, |⊥| is the empty Agda type, |⊎| is disjoint union (|Either|),
and |×| is the pair type.  |Σ A (λ x → B)| is an existential/dependent
pair, where the type of the second component depends on the value of the
first---because this is not built in in Agda, it takes a type |A| and a
function from |A| to |Set| as arguments.  The notation |λ {p → e}|
allows a pattern-matching anonymous function.
The function |++| appends lists, and |≡| is Agda's
propositional equality.  Thus, in full, the clause for alternation means
``there exist strings |p| and |q| such that appending |p| and |q| gives
|s|, where |p| is in the language of |r₁| and |q| is in the language of
|r₂|".

However, is is important to note that these membership ``predicates''
land in |Set|, the Agda type of types, and thus may have computational
content.  For example, a witness that |s ∈Lˢ (r₁ ⊕ r₂)| includes a bit
(|inj₁| or |inj₂|) that tells which possibility was taken, and
a witness |s ∈L⁺ r| is a non-empty list of strings matching |r|, which
concatenate to |s|.  Thus, there can be different witnesses that 
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

\noindent We will exploit this in Section~\ref{sec:groups} to extract matching
strings from such derivations.

% two different values in the same type written in Agda

% \begin{code}
% ex₁ : ('a' ∷ 'a' ∷ 'a' ∷ []) ∈Lˢ ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))
% ex₂ : ('a' ∷ 'a' ∷ 'a' ∷ []) ∈Lˢ ((Litˢ 'a' ⁺ˢ) ·ˢ (Litˢ 'a' ⁺ˢ))
% ex₁ = ('a' ∷ [] , 'a' ∷ 'a' ∷ []) , refl , S+ refl , C+ refl refl (S+ refl)
% ex₂ = ('a' ∷ 'a' ∷ [] , 'a' ∷ []) , refl , C+ refl refl (S+ refl) , S+ refl
% \end{code}

\section{Defunctionalized intrinsic matcher}
\label{sec:defunc}

In this section, we define a first-order matcher for standard regular
expressions.  This is a defunctionalization of Harper's algorithm,
though we will describe it from first principles.  The idea is to
generalize from matching a string |s| against a regular expression |r|
by adding an additional stack of regular expressions |k| that need to be
matched against the suffix of |s| if some prefix of |s| matches |r|.  We represent
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
match :  (r : StdRegExp) (s : List Char) (k : List StdRegExp)
         → Maybe  (Σ  (List Char × List Char)
                       (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
\end{code}
This says that the matcher takes a regular expression |r|, a string |s|
and a stack |k|, and, if matching succeeds, returns a splitting |(p ++
s' ≡ s)|, a derivation that |p| is in the language of |r| and a
derivation that |s'| is in the language of the stack |k|.  This
specifies the soundness of successful matching, and has computational
content that will let us extract matching strings, but leaves open the
possibility that the matcher fails incorrectly (for example, the
constantly |nothing| function has this type)---this will be addressed in
the completeness proof below.

The complete code is in
Figure~\ref{fig:intrinsic-defunctionalized-matcher}.  Agda can verify
that this function terminates by induction on first the string |s|, and
then the regular expression |r|.  We now discuss the code case by case.

\subsubsection{Base cases}

First, the empty language does not accept any string:
\begin{code}
match ∅ˢ s k = fail
\end{code}

For character literals
\begin{code}
match (Litˢ c) [] k = fail
match (Litˢ c) (x ∷ xs) k =
  (isEqual x c) >>=
    (λ p → map (λ pf → ((([ c ] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf)))
               (match-helper k xs))
\end{code}
in the first case, if we are trying to match an empty list with a
regular expression that requires a character, the matcher fails.  In the
next case, the |isEqual x c| call has type |Maybe (x ≡ c)|---i.e. it
optionally shows that |x| is equal to |c|.  Thus, by the monad bind,
when |x| is not |c|, the matcher fails, and when |x| is |c|, we try to
match the stack |k| against the suffix |xs| using |match-helper|.

The function |match-helper| is mutually recursive with our matcher and
is defined as follows:
\begin{code}
match-helper : (k : List StdRegExp) → (s : List Char) → Maybe (s ∈Lᵏ k)
match-helper [] [] = return refl
match-helper [] (x ∷ s) = fail
match-helper (r ∷ k') s = match r s k'
\end{code}
It succeeds when matching the empty string against the empty stack,
fails when matching a non-empty string against the empty stack, and
otherwise refers back to |match|.  Relative to Harper's algorithm, this
is the application function for the defunctionalized continuation.

Returning to the character literal case, if the first character in our
list matches the character literal |c|, then we call |match-helper| on
the continuation and the rest of the list, which will produce a
derivation of |s ∈Lᵏ k| if the rest of the list indeed matches the rest
of the |StdRegExp|s in |k|.  The remainder of the code packages this as
a pair showing that therefore the list |x ∷ xs| splits as |[ x ] ∈Lˢ
(Lit c)| and |xs ∈Lᵏ k|.

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

In the case for concatenation |r₁ ·ˢ r₂|, we match against |r₁| first,
and add |r₂| to the stack |k|.  Calling |match r₁ s (r₂ ∷ k)| will give
us a split |xs ++ ys ≡ s| and derivations of |xs ∈Lˢ r₁| and |ys ∈Lᵏ (r₂
∷ k)|. If we unpack the second derivation (using the definition of |∈Lᵏ|
and the fact that our continuation list contains at least one element,
|r₂|), we will have another split |as ++ bs ≡ ys| and derivations |as
∈Lˢ r₂| and |bs ∈Lᵏ k|.  The helper function |reassociate-left| states
that if we have such a situation, we can reassociate it to show that |xs
++ as| matching the entire regular expression |r₁ ·ˢ r₂|.  Because we
will want to do similar reasoning in the Kleene plus case below, we use
a higher-order function that says that if |R| is a binary operation on
regular expressions that respects splitting, then given the first kind
of splitting, we can produce the second:

\begin{code}
reassociate-left : ∀ {r₁ r₂ s k} {R : StdRegExp → StdRegExp → StdRegExp}
              → (f : ∀ {xs as} → xs ∈Lˢ r₁ → as ∈Lˢ r₂ → ((xs ++ as) ∈Lˢ R r₁ r₂))
              → Σ _ (λ { (xs , ys) → (xs ++ ys ≡ s) × xs ∈Lˢ r₁
                     × Σ _ (λ {(as , bs) → (as ++ bs ≡ ys) × as ∈Lˢ r₂ × bs ∈Lᵏ k})})
              → (Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ R r₁ r₂) × s' ∈Lᵏ k}))
\end{code}

\subsubsection{Alternation}

\begin{code}
match (r₁ ⊕ˢ r₂) s k =
  (map (change-∈L inj₁) (match r₁ s k)) ∣∣
  (map (change-∈L inj₂) (match r₂ s k))
\end{code}

In the alternation case, we match the string with |r₁|, and if that
fails match with |r₂| (recall that |∣∣| handles failure of its first
disjunct by trying the second).  If the call |match r₁ s k| succeeds, it
will produce a triple splitting |s| as |p ++ s'|, with a derivation of
|p ∈Lˢ r₁| and |s' ∈Lᵏ k|.  However the return type for the alternation
case should contain a derivation of type |p ∈Lˢ (r₁ ⊕ˢ r₂)|, so we use
the helper function |change-∈L|, which applies a function to this
position of the result triple, to make the appropriate modification:
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
  (map (change-∈L S+) (match r s k)) ∣∣
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
mutual
  match : (r : StdRegExp) (s : List Char) (k : List StdRegExp)
        → Maybe (Σ (List Char × List Char) (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
  match ∅ˢ s k = fail
  match (Litˢ c) [] k = fail
  match (Litˢ c) (x ∷ xs) k =
    (isEqual x c) >>=
      (λ p → map (λ pf → ((([ c ] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf)))
                 (match-helper k xs)
  match (r₁ ·ˢ r₂) s k =
    map (reassociate-left {R = _·ˢ_} (λ inL inL' → _ , refl , inL , inL'))
      (match r₁ s (r₂ ∷ k))
  match (r₁ ⊕ˢ r₂) s k =
    (map (change-∈L inj₁) (match r₁ s k)) ∣∣
    (map (change-∈L inj₂) (match r₂ s k))
  match (r ⁺ˢ) s k =
    (map (change-∈L S+) (match r s k)) ∣∣
    (map (reassociate-left {R = λ r _ → r ⁺ˢ} (λ inL inL' → C+ refl inL inL'))
      (match r s ((r ⁺ˢ) ∷ k)))

  match-helper : (k : List StdRegExp) → (s : List Char) → Maybe (s ∈Lᵏ k)
  match-helper [] [] = return refl
  match-helper [] (x ∷ s) = fail
  match-helper (r ∷ k') s = match r s k'
\end{code}
\caption{Defunctionalized intrinsic matcher}
\label{fig:intrinsic-defunctionalized-matcher}
\figrule
\end{figure}

\subsubsection{Acceptance}

From the outside, we can call the generalized matcher with the empty
stack to check membership:

\begin{code}
acceptsˢ-intrinsic : (r : StdRegExp) → (s : List Char) → Maybe (s ∈Lˢ r)
acceptsˢ-intrinsic r s = map ∈L-empty-stack (match r s [])
\end{code}
%
When the |match| function succeeds on an empty stack, the suffix is in
the language of an empty stack and is therefore an empty string, so we
use the following lemma to change the result of the function call
|match r s []| into a derivation over the entire string |s|.
\begin{code}
∈L-empty-stack : {r : StdRegExp} {s : List Char}
                → Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × (s' ≡ []) })
                → s ∈Lˢ r
\end{code}


\subsection{Completeness}

Though the above matcher is intrinsically sound, it is not intrinsically
complete---for example, the function that always fails has the above
type.  One way to resolve this would be to write a matcher that is
intrinsically both sound and complete --- ignoring the stack,
given |s| and |r|, we would like to know |(s ∈Lˢ r) ⊎ ¬ (s ∈Lˢ r)|, a
type that expresses decidability of matching.  However, while there is
an efficiency reason to intrinsically compute the the derivation of |s
∈Lˢ r|---we will use it to extract matching strings in Section~\ref{sec:groups}---there is no
computational content to |¬ (s ∈Lˢ r)|.  Because of this, and because it
keeps the matcher code itself simpler, we choose to make completeness
extrinsic.  In full, completeness says that if we have |r|, |s|, |k| and
a split of |p ++ s' ≡ s| such that there are derivations of type |p ∈Lˢ
r| and |s' ∈Lᵏ k|, then we know that our |match| function does not fail:

\begin{code}
match-completeness :  (r : StdRegExp) (s : List Char) (k : List StdRegExp)
                      → Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × (s' ∈Lᵏ k)})
                      → isJust (match r s k)
\end{code}
That is, when there is a way for the matcher to succeed, it does.  We
cannot make a stronger claim and say that it returns the same derivation
that is given as input, because as we showed before, there can be
different derivations for the same |s| and |r|, and the given one may
not be the one the matcher finds.

The full proof is in the companion code.  The base cases |∅ˢ| and |Litˢ|
are easy.  Since the Kleene plus case captures the essence of both
concatenation and alternation cases, we will explain only this case.
The proof proceeds by cases, depending on how the given derivation of |p
∈L (r ⁺)| was constructed.  For the first,
\begin{code}
match-completeness (r ⁺ˢ) s k ((xs , ys) , eq , S+ inL , rest)
  with match r s k | match-completeness r s k ((xs , ys) , eq , inL , rest)
... | nothing | ()
... | just _  | _ = tt
\end{code}
if the given derivation of |xs ∈L (r ⁺)| was by the constructor |S+|,
then sitting under the constructor is a derivation of |inL : xs ∈Lˢ r|,
and the result follows from the inductive hypothesis on |D|.

For the second, where the derivation was constructed by |C+|,
\begin{code}
match-completeness (r ⁺ˢ) .((s₁ ++ s₂) ++ ys) k
    ((._ , ys) , refl , C+ {._}{s₁}{s₂} refl inL1 inL2 , rest)
  with match r ((s₁ ++ s₂) ++ ys) k
... | just _ = tt
... | nothing
  with match r ((s₁ ++ s₂) ++ ys) ((r ⁺ˢ) ∷ k)
     | match-completeness r ((s₁ ++ s₂) ++ ys) ((r ⁺ˢ) ∷ k)
        (_ , append-assoc s₁ s₂ ys , inL1 , (_ , ys) , refl , inL2 , rest)
... | nothing | ()
... | just _  | _ = tt
\end{code}
we already had a split |xs ++ ys ≡ s|, so we can replace |s| with |xs ++
ys| by pattern matching on the equality proof.  The constructor |C+|
gives us another split |s₁ ++ s₂ ≡ xs|, so we can also replace |xs| with
|s₁ ++ s₂|.  This means now we have to show the goal for |(s₁ ++ s₂) ++
ys| instead of |s|.  The definition of the Kleene plus case uses |_∣∣_|,
which has to try and fail the first case to return the second case.  To
verify completeness, we first check whether |match r ((s₁ ++ s₂) ++ ys)
k| succeeds or fails.  If the call succeeds, then we satisfy the first
case of |_∣∣_|, so the matcher succeeds.  If the call fails, then we
checker whether the second disjunct fails or succeeds.  If it fails,
then we obtain a contradiction by the inductive hypothesis, which shows
that the recursive call should have succeeded because |s₁| matches |r|
and |s₂ ++ ys| matches the continuation (using the associative property
of appending lists to show that it is the same string).  If it succeeds,
then the matcher succeeds, so we have the result.

As a corollary, we get completeness of |acceptsˢ-intrinsic|:
\begin{code}
acceptsˢ-intrinsic-completeness :  (r : StdRegExp) (s : List Char)
                                   → s ∈Lˢ r
                                   → isJust (acceptsˢ-intrinsic r s)
\end{code}

\section{Higher-order intrinsic matcher}
\label{sec:hof}

In this section, we show that the above intrinsic verification of the
first-order matcher scales to a higher-order matcher, written using
continuation-passing, which is more similar to Harper's original code.
We will use this to explain why the above matcher is a
defunctionalization, and why the termination reasoning is more difficult
in the higher-order case.  To make termination evident to Agda, we will
need to use an explicit termination metric that corresponds to
well-founded induction on strings/lists.  This is represented in Agda by
an iterated inductive definition |RecursionPermission xs|.  Visually,
you can think of |RecursionPermission ys| as a tree, where a node for
|ys| has subtrees for each strict suffix of |ys|.  Each of these
subtrees is judged smaller by the termination checker, and therefore we
will be allowed to recur on any suffix of |ys|.  Such a tree type is
defined by the following datatype, which has a higher-order constructor
argument:

\begin{code}
data RecursionPermission {A : Set} : List A → Set where
  CanRec : {ys : List A}
         → ((xs : List A) → Suffix xs ys → RecursionPermission xs)
         → RecursionPermission ys
\end{code}

\subsection{Definition}

The higher-order intrinsic matcher has the following specification:

\begin{code}
match :  (C : Set) (r : StdRegExp) (s : List Char)
         → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
         → RecursionPermission s
         → Maybe C
\end{code}

The type variable |C| stands for the output derivation computed by the
matcher on success.  Just as Harper's algorithm returns a |bool| and
uses both the continuation and the language's control stack
(i.e. it is not fully in CPS), here both the continuation and the
matcher return an option, but the success data can been chosen
arbitrarily.  In Harper's algorithm, the continuation takes a string
that corresponds to |s'| in the above type.  The additional arguments
provided here, which are important for justifying termination, say that
in a call to |match r s k|, the domain of the continuation is suffixes
|s'| of |s| by a prefix that is in the language of |r|.  The final
argument is of type |RecursionPermission s|, and allows recursive calls
on strict suffixes of |s|.  The termination measure for this function is
lexicographic in first the regular expression |r| and then the recursion
permission tree.  The complete code is in
Figure~\ref{fig:intrinsic-hof-matcher}.

\subsubsection{Base cases}

The case for the empty regexp fails:
\begin{code}
match C ∅ˢ s k perm = fail
\end{code}

The cases for character literals
\begin{code}
match C (Litˢ c) [] k perm = fail
match C (Litˢ c) (x ∷ xs) k perm =
  (isEqual x c) >>= (λ p → k {[ x ]} {xs} refl (cong (λ q → [ q ]) p))
\end{code}
are as above, except that where we called |match-helper| to activate the
stack |k|, here we call |k| itself.  The packaging of the result of
|match-helper| (the |map| in the above code) now happens as \emph{input}
to |k|, because to call |k| we must show that |x ∷ xs| splits as
something in the language of |Litˢ c| and some suffix.

\subsubsection{Concatenation}

\begin{code}
match C (r₁ ·ˢ r₂) s k (CanRec f) =
  match C r₁ s
        (λ {p}{s'} eq inL →
          match C r₂ s' (λ {p'}{s''} eq' inL' →
                          k {p ++ p'}{s''} (replace-right p s' p' s'' s eq' eq) ((p , p') , refl , inL , inL'))
                        (f s' (suffix-after-∈Lˢ eq inL))) (CanRec f)
\end{code}

In the concatenation case of the defunctionalized version, we added |r₂|
to the stack of continuations to be matched later.  In the higher-order
version, extending the stack with |r₂| corresponds to constructing a new
continuation function which matches |r₂| against the suffix that results
from matching |r₁| against a prefix---which is exactly what ``applying''
the stack in |match-helper| did in the defunctionalized version.  The
massaging that happens after the recursive call above (the
|reassociate-left|) here happens in the new continuation, which
repackages the given derivations |inL : p ∈Lˢ r₁| and |inL' : p' ∈Lˢ r₂|
and the given splittings |eq : p ++ s' ≡ s| and |eq' : p' ++ s'' ≡ s'|
as a splitting |(p ++ p') ++ s'' ≡ s| and a derivation that |p ++ p' ∈
∈Lˢ (r₁ ·ˢ r₂)|.  The two recursive calls pass the termination checker
because the regular expressions |r₁| and |r₂| get smaller in each case.
To make the inner recursive call, it is necessary to supply a recursion
permission for |s'|, i.e. to allow recursive calls on |s'|, and to do
this it suffices to show that |s'| is a suffix of |s|.  The
|suffix-after-∈Lˢ| lemma
\begin{code}
  suffix-after-∈Lˢ : ∀ {p s' s r} → (p ++ s' ≡ s) → (p ∈Lˢ r) → Suffix s' s
\end{code}
does this: |s'| is a non-strict suffix of |s| by the equality, and
because the prefix |p| is in the language of a \emph{standard} regular
expression |r| and therefore is not empty, it is a strict suffix.  (In
this case, it would also be sufficient to observe that |s'| is a
non-strict suffix of |s|, because we do not need the string and
recursion permission to get smaller to justify termination, but the
argument we just gave will also be used in the Kleene plus case.)

\subsubsection{Alternation}

\begin{code}
match C (r₁ ⊕ˢ r₂) s k perm =
  match C r₁ s (λ eq inL → k eq (inj₁ inL)) perm ∣∣
  match C r₂ s (λ eq inL → k eq (inj₂ inL)) perm
\end{code}

The alternation case is similar to the defunctionalized version, except
instead of massaging the derivations after the fact with |map
change-∈L|, we modify them before passing them to the continuation.

\subsubsection{Kleene plus}

\begin{code}
match C (r ⁺ˢ) s k (CanRec f) =
  match C r s (λ eq inL → k eq (S+ inL)) (CanRec f) ∣∣
  match C r s (λ {p}{s'} eq inL →
                match C (r ⁺ˢ) s' (λ {p'}{s''} eq' inL' →
                                    k (replace-right p s' p' s'' s eq' eq) (C+ refl inL inL') )
                      (f s' (suffix-after-∈Lˢ eq inL))) (CanRec f)
\end{code}

The structure of the Kleene plus case is similar to the defunctionalized
version, except the continuations are modified analogously to the
concatenation and alternation cases.  The first recursive call
terminates because |r| gets smaller.  For the second recursive call, |(r
⁺ˢ)| stays the same, so it is essential that |s'| is a \emph{strict}
suffix of |s|, and that the recursion permission tree gets smaller.  As
in the alternation case, |s'| is a non-strict suffix of |s| by the
equality |eq : p ++ s' ≡ s|, and because the prefix |p| is in the language
of a \emph{standard} regular expression |r| and therefore is not empty,
|s'| is a strict suffix of |s| by the |suffix-after-∈Lˢ| lemma.
Therefore, applying |f| to |s'| and this fact selects a smaller
recursion permission subtree, justifying termination.

Termination is trickier for the higher-order matcher than for the
defunctionalized matcher because, here, we make the recursive call on |r
⁺ˢ| in the continuation constructed in the |r ⁺ˢ| case, so we must argue
that \emph{whenever this continuation is applied}, it will be applied to
a smaller string.  In the defunctionalized matcher, this recursive call
is made in |match-helper| (the apply function for the defunctionalized
continuation), which is called from the character literal case, at which
point it is syntactically clear that the recursive call \emph{is being
  made} on a smaller string.

\begin{figure}
\figrule
\begin{code}
match :  (C : Set) (r : StdRegExp) (s : List Char)
         (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
         → RecursionPermission s
         → Maybe C
match C ∅ˢ s k perm = fail
match C (Litˢ c) [] k perm = fail
match C (Litˢ c) (x ∷ xs) k perm =
  (isEqual x c) >>= (λ p → k {[ x ]} {xs} refl (cong (λ q → [ q ]) p))
match C (r₁ ·ˢ r₂) s k (CanRec f) =
  match C r₁ s
        (λ {p}{s'} eq inL →
          match C r₂ s' (λ {p'}{s''} eq' inL' →
                          k {p ++ p'}{s''} (replace-right p s' p' s'' s eq' eq) ((p , p') , refl , inL , inL'))
                        (f _ (suffix-after-∈Lˢ eq inL))) (CanRec f)
match C (r₁ ⊕ˢ r₂) s k perm =
  match C r₁ s (λ eq inL → k eq (inj₁ inL)) perm ∣∣
  match C r₂ s (λ eq inL → k eq (inj₂ inL)) perm
match C (r ⁺ˢ) s k (CanRec f) =
  match C r s (λ eq inL → k eq (S+ inL)) (CanRec f) ∣∣
  match C r s (λ {p}{s'} eq inL →
                match C (r ⁺ˢ) s' (λ {p'}{s''} eq' inL' →
                                    k (replace-right p s' p' s'' s eq' eq) (C+ refl inL inL') )
                      (f _ (suffix-after-∈Lˢ eq inL))) (CanRec f)
\end{code}
\caption{Complete definition of the |match| function for
  the higher-order intrinsic matcher.}
\figrule
\label{fig:intrinsic-hof-matcher}
\end{figure}

\subsubsection{Acceptance}

Overall, we can define
\begin{code}
acceptsˢ-intrinsic : (r : StdRegExp) → (s : List Char) → Maybe (s ∈Lˢ r)
acceptsˢ-intrinsic r s = match _ r s empty-continuation (well-founded s)
\end{code}
by choosing an appropriate initial continuation, and by constructing a
recursion permission for |s| (which exists because string suffix is a
well-founded relation).  The initial continuation
\begin{code}
empty-continuation : ∀ {p s' s r} → (p ++ s' ≡ s) → (p ∈Lˢ r) → Maybe (s ∈Lˢ r)
\end{code}
corresponds to the logic for the empty stack |[]| in |match-helper| in
the defunctionalized version.  This function takes a splitting of a
string |s| as |p ++ s'|, as well as a proof that its first part |p| is
in the language of |r|.  It returns either |nothing| if |s'| is not
empty, or |just| a witness that |(s ∈Lˢ r)| if |s'| is empty, and
therefore |s ≡ p'|.

%% \begin{code}
%% well-founded : {A : Set} (ys : List A) → RecursionPermission ys
%% \end{code}
%% |well-founded| just gives us a |RecursionPermission| for any given list.

\subsection{Completeness}

Completeness is similar to above, and says that the matcher succeeds
whenever it should:
\begin{code}
match-completeness : (C : Set) (r : StdRegExp) (s : List Char)
                   → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
                   → (perm : RecursionPermission s)
                   → Σ _ (λ { (p , s') → Σ _ (λ eq → Σ _ (λ inL → isJust (k {p}{s'} eq inL))) })
                   → isJust (match C r s k perm)
\end{code}
The type can be read as follows: Suppose we have |C|, |r|, |s|, |k| and
|perm|. Suppose there exists a split of |p ++ s' ≡ s| such that there
exists a derivation of type |p ∈Lˢ r| such that the continuation called
with those arguments does not return |nothing|. Then we have to show
that the |match| function does not fail.  Like above, we cannot make a
stronger claim and say that the calls to the continuation and the
|match| function return the same derivations, because there can be more
than one derivation of a string matching a regexp.  The proof is in the
companion code, and follows the same pattern as the proof of
|match-completeness| for the defunctionalized version.

\section{Matching non-standard regular expressions}
\label{sec:nonstandard}

Both of the above matchers work on syntactically standard regular
expressions, which is used to show termination.  We now show that this
suffices to define a matcher for non-standard regular expressions, which
we represent by a type |RegExp|:

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
|∅| matches the empty language, |ε| matches the empty string, |Lit| is
character literals, |_·_| is concatenation, |_⊕_| is alternation,
|_*_| is Kleene star, and |G| is for reporting matching strings.
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
The definition of the language of these regular expressions is similar
to above, but with an |ε| case that requires an empty string, and a base
case for |s ∈Lˣ r| that allows the empty string; note that |G| does not
change the language.

Next, we define a translation from regexps to syntactically standard
regexps.  The translation uses a helper function that checks if a
regular expression accepts the empty string.  Instead of giving this
function the type |RegExp → Bool|, we give it a more informative type
stating that it decides whether the empty string is in the language of
its input:
\begin{code}
δ' : (r : RegExp) → ([] ∈L r) ⊎ (¬ ([] ∈L r))
\end{code}
Using |δ'|, we can easily define |δ : RegExp → Bool| by forgetting the
extra information.

The specification for standardization, which we prove below, is that
\[
(\forall s) \; \big[ s \in L(r) \Longleftrightarrow \left[ (\delta(r)
    = true \land s = []) \lor s \in L( \standardize (r))\right] \big]
\]
That is, |s| is in the language of |r| if and only if either and $r$
accepts the empty string and the string is empty , or |s| is in the
language of the standardized version of |r|.

We $\standardize$ as follows:
\begin{code}
standardize : RegExp → StdRegExp
standardize ∅ = ∅ˢ
standardize ε = ∅ˢ
standardize (Lit x) = Litˢ x
standardize (r₁ · r₂) with standardize r₁ | standardize r₂ | δ r₁ | δ r₂
... | r₁' | r₂' | false | false = r₁' ·ˢ r₂'
... | r₁' | r₂' | false | true = r₁' ⊕ˢ (r₁' ·ˢ r₂')
... | r₁' | r₂' | true | false = r₂' ⊕ˢ (r₁' ·ˢ r₂')
... | r₁' | r₂' | true | true = r₁' ⊕ˢ r₂' ⊕ˢ (r₁' ·ˢ r₂')
standardize (r₁ ⊕ r₂) = standardize r₁ ⊕ˢ standardize r₂
standardize (r *) = (standardize r) ⁺ˢ
standardize (G r) = standardize r
\end{code}

The empty string language |ε| becomes the empty set |∅ˢ| and Kleene star
becomes Kleene plus, because the emptiness checking is performed outside
matching the standardized regexp.  For the concatenation case, we write
|r₁'| and |r₂'| for the standardizations of |r₁| and |r₂|.  Because
|standardize r| will not accept the empty string even when |r| does, it
is necessary to check |r₁'| and |r₂'| by themselves in the case where
the other one accepts the empty string, because otherwise we would miss
strings that rely on one component but not the other being empty.

Our definition of the concatenation
case is a bit different than Harper's, where |δ| returns not a boolean,
but a regexp |∅| (if |r| does not accept the empty string) or |ε| (if it
does), and the clause is as follows:
\begin{code}
standardize (r₁ · r₂) =  ((δ r₁) ·ˢ (standardize r₂)) ⊕ˢ
                         ((standardize r₁) ·ˢ (δ r₂)) ⊕ˢ
                         ((standardize r₁) ·ˢ (standardize r₂))
\end{code}
This definition is equivalent to above, using the equivalences that for any |r|,
|∅ ·ˢ r = ∅ = r ·ˢ ∅| and |ε ·ˢ r = r = r ·ˢ ε|.  For example, when
|δ r₁| is true, Harper's translation gives a |ε ·ˢ (standardize r₂)|
summand, which is standard but \emph{not} syntactically standard, but we
can simplify it to |standardize r₂|.  When |δ r₁| is false, Harper's
translation gives an |∅ ·ˢ (standardize r₂)| summand, which drops out.

This definition of standardization satisfies the above correctness
theorem; we have proved
\begin{code}
∈L-soundness  : (s : List Char) (r : RegExp)
              → ((δ r ≡ true) × (s ≡ [])) ⊎ (s ∈Lˢ (standardize r))
              → s ∈L r

∈L-completeness  : (s : List Char) (r : RegExp)
                 → s ∈L r
                 → ((δ r ≡ true) × (s ≡ [])) ⊎ (s ∈Lˢ (standardize r))
\end{code}
Now that we have a verified |standardize| function, we can define
|_accepts_| as follows, where |acceptsˢ-intrinsic| can be either of the
above matchers:

\begin{code}
accepts-intrinsic : (r : RegExp) → (s : List Char) → Maybe (s ∈L r)
accepts-intrinsic r s with δ' r
accepts-intrinsic r [] | inj₁ x = just x
accepts-intrinsic r s | _ = map (∈L-soundness s r ∘ inj₂) (acceptsˢ-intrinsic (standardize r) s)
\end{code}

If |r| accepts the empty string, we return |true| if |xs| is empty or the
standardization of |r| accepts |xs|. If |r| does not accept the empty string,
then we only have the latter option. In that case, we call |acceptsˢ-intrinsic|
to get an optional derivation of the type |s ∈Lˢ (standardize r)| and use that
on |∈L-soundness| to get an optional derivation of the type |s ∈L r|.

As usual, we have proved completeness extrinsically:
\begin{code}
correct-completeness  : (r : RegExp) (s : List Char)
                      → s ∈L r
                      → isJust (r accepts s)
\end{code}

Finally, we have proved decidability of matching as a corollary of
soundness and completeness:
\begin{code}
decidability : (r : RegExp) (s : List Char) → (s ∈L r) ⊎ (¬ (s ∈L r))
\end{code}

\subsection{Capturing groups}
\label{sec:groups}

The ``capturing group'' constructor |G| is intended to allow the user to
specify parts of a regular expression whose matching strings should be
extracted and reported.  For example, if our regular expression checks
if a string is a valid e-mail address, we might use this to parse the
username and domains.  If we have a regular expression |alphanumeric :
RegExp| that accepts a single alphanumeric character (this can be
defined in the above language as a big |⊕| of character literals), we
can define a (na\"ive) regular expression for e-mail addresses such as
\begin{code}
e-mail : RegExp
e-mail = G (alphanumeric *) · Lit '@' · G (alphanumeric *) · Lit '.' · G (alphanumeric *)
\end{code}
Now, if we match the string ``jdoe|@|wesleyan.edu" with |e-mail|, we
should extract and report ``jdoe", ``wesleyan" and ``edu", because each
of those substrings matched a sub-regexp that was marked with |G|.

This extraction can be computed from the derivation of |s ∈L r|, which
provides a parse tree that says which substring of |xs| is matched by
which part of |r|.  Thus, to report the groups, we do an in-order
traversal of the regexp and derivation tree, and collect the strings
matching a capturing group to a list.  The function to do this can be
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

Base cases |∅|, |ε|, |Lit| will return an empty list because if they are
captured by a group, the substring is already added to the list in the
previous calls to |extract|.  In concatenation, we make two recursive
calls and append the results because |r₁| and |r₂| match different
substrings and they may have different capturing groups inside them.  In
alternation, the entire string matches either |r₁| or |r₂|, so we make
one recursive call to the one it matches.  The Kleene star case follows
the same principles.

Combining this with our intrinsic matcher, we can define an overall function
\begin{code}
groups : (r : RegExp) (s : List Char) → Maybe (List (List Char))
groups r s = map extract (accepts-intrinsic r s)
\end{code}

\section{Conclusion}

We have studied three variations on Harper's algorithm for regular
expression matching, which were inspired by programming and verifying
this algorithm using dependent types: defunctionalizing the matcher
allows Agda to see termination without an explicit metric, and provides
an alternative to Yi's first-order matcher based on state machines;
intrinsically verifying soundness allows extracting matching strings;
and a syntactic definition of standard regular expressions simplifies
the staging of the development.  We believe that these variations
provide a nice illustration of the benefits of thinking in a dependently
typed language, and that they have some pedagogical value for teaching
this material in courses on dependently typed programming---or, by
porting the observations back to simply-typed languages, on introductory
programming.

\bibliography{paper}

\end{document}
