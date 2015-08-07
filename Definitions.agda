open import lib.Preliminaries

module Definitions where

  open List

  -- Definitions of types and functions used in the matchers.

  data RegExp : Set where
    ∅ : RegExp  -- empty set (type \emptyset)
    ε : RegExp   -- empty string (type \epsilon)
    Lit : Char → RegExp -- literal character
    _·_ : RegExp → RegExp → RegExp -- concatenation (type \cdot)
    _⊕_ : RegExp → RegExp → RegExp -- alternation/set union (type \oplus)
    _* : RegExp → RegExp -- Kleene star
    G : RegExp → RegExp

  {- The regular expressions that do not accept empty string. -}
  data StdRegExp : Set where
    ∅ˢ : StdRegExp
    Litˢ : Char → StdRegExp
    _·ˢ_ : StdRegExp → StdRegExp → StdRegExp
    _⊕ˢ_ : StdRegExp → StdRegExp → StdRegExp
    _⁺ˢ : StdRegExp → StdRegExp -- accepts one or more of the given StdRegExp
    Gˢ : StdRegExp → StdRegExp

  infix 1 _* _⁺ˢ
  infixr 2 _·_ _·ˢ_
  infixr 3 _⊕_ _⊕ˢ_

  {-
    Example regexp:
      ((Lit 'a' ⊕ Lit 'b') · (Lit 'c')) accepts "ac"
      (∅ *) accepts ""
      ((Lit 'd') *) accepts "ddd"
      ((Lit 'd') *) accepts ""
      (Lit '<' · (Lit '0' *) · Lit '>') accepts "<>"
      (Lit '<' · (Lit '0' *) · Lit '>') accepts "<00>"
  -}

  -- Shows a string accepted by the language of a regexp. Type "\in L".
  _∈L_ : List Char → RegExp → Set
  data _∈Lˣ_ : List Char → RegExp → Set

  _ ∈L ∅ = Void
  s ∈L ε = s == []
  s ∈L (Lit c) = s == c :: []
  s ∈L (r₁ ⊕ r₂) = Either (s ∈L r₁) (s ∈L r₂)
  s ∈L (r₁ · r₂) = Σ (λ { (p , q) → (p ++ q == s) × (p ∈L r₁) × (q ∈L r₂) })
  s ∈L (r *) = s ∈Lˣ r
  s ∈L (G r) = s ∈L r

  data _∈Lˣ_ where
    Ex : ∀ {s r} → s == [] → s ∈Lˣ r
    Cx : ∀ {s s₁ s₂ r} → s₁ ++ s₂ == s → s₁ ∈L r → s₂ ∈Lˣ r → s ∈Lˣ r

  _∈Lˢ_ : List Char → StdRegExp → Set
  data _∈L⁺_ : List Char → StdRegExp → Set

  _ ∈Lˢ ∅ˢ = Void
  s ∈Lˢ (Litˢ c) = s == c :: []
  s ∈Lˢ (r₁ ⊕ˢ r₂) = Either (s ∈Lˢ r₁) (s ∈Lˢ r₂)
  s ∈Lˢ (r₁ ·ˢ r₂) = Σ (λ { (p , q)  → (p ++ q == s) × (p ∈Lˢ r₁) × (q ∈Lˢ r₂) })
  s ∈Lˢ (r ⁺ˢ) = s ∈L⁺ r
  s ∈Lˢ (Gˢ r) = s ∈Lˢ r

  data _∈L⁺_ where
    S+ : ∀ {s r} → s ∈Lˢ r → s ∈L⁺ r
    C+ : ∀ {s s₁ s₂ r} → s₁ ++ s₂ == s → s₁ ∈Lˢ r → s₂ ∈L⁺ r → s ∈L⁺ r

  {- Suffix xs ys means that xs is a suffix of ys -}
  data Suffix {A : Set} : List A → List A → Set where
    Stop : ∀ {x xs} → Suffix xs (x :: xs)
    Drop : ∀ {y xs ys} → Suffix xs ys → Suffix xs (y :: ys)

  {- A type to make it obvious to Agda that our function will terminate. -}
  data RecursionPermission {A : Set} : List A → Set where
    CanRec : {ys : List A} → ((xs : List A) → Suffix xs ys → RecursionPermission xs) → RecursionPermission ys

  -- Two lemmas needed for definitions.

  empty-append : {xs ys : List Char} → xs ++ ys == [] → (xs == []) × (ys == [])
  empty-append {[]} {[]} Refl = Refl , Refl
  empty-append {[]} {_ :: _} ()
  empty-append {_ :: _} {[]} ()
  empty-append {_ :: _} {_ :: _} ()

  empty-append-δ : ∀ {x y r} → x ++ y == [] → Either (x ∈L r) (y ∈L r) → ([] ∈L r → Void) → Void
  empty-append-δ {x}{y}{r} eq inL f with empty-append {x}{y} eq
  empty-append-δ eq (Inl inL) f | Refl , Refl = f inL
  empty-append-δ eq (Inr inL) f | Refl , Refl = f inL

  -- Checks if a given regexp accepts empty string.
  δ' : (r : RegExp) → Either ([] ∈L r) ([] ∈L r → Void)
  δ' ∅ = Inr (λ ())
  δ' ε = Inl Refl
  δ' (Lit x) = Inr (λ ())
  δ' (r₁ · r₂) with δ' r₁ | δ' r₂
  ... | Inr p | _ = Inr (λ {((x , y) , (a , (b , _))) → empty-append-δ {x}{y}{r₁} a (Inl b) p})
  ... | _ | Inr q = Inr (λ {((x , y) , (a , (_ , c))) → empty-append-δ {x}{y}{r₂} a (Inr c) q})
  ... | Inl p | Inl q = Inl (([] , []) , Refl , p , q)
  δ' (r₁ ⊕ r₂) with δ' r₁ | δ' r₂
  ... | (Inl p) | _ = Inl (Inl p)
  ... | _ | (Inl q) = Inl (Inr q)
  ... | (Inr p) | (Inr q) = Inr (sub-lemma p q)
    where sub-lemma : ∀ {a b} → (a → Void) → (b → Void) → Either a b → Void
          sub-lemma f _ (Inl a) = f a
          sub-lemma _ g (Inr b) = g b
  δ' (r *) = Inl (Ex Refl)
  δ' (G r) = δ' r

  -- Checks if a given regexp accepts empty string. True, if it accepts ε, False otherwise.
  δ : RegExp → Bool
  δ r with δ' r
  ... | Inl _ = True
  ... | Inr _ = False

  standardize : RegExp → StdRegExp
  standardize ∅ = ∅ˢ
  standardize ε = ∅ˢ
  standardize (Lit x) = Litˢ x
  standardize (r₁ · r₂) with standardize r₁ | standardize r₂ | δ r₁ | δ r₂
  ... | x₁ | x₂ | False | False = x₁ ·ˢ x₂
  ... | x₁ | x₂ | False | True = x₁ ⊕ˢ (x₁ ·ˢ x₂)
  ... | x₁ | x₂ | True | False = x₂ ⊕ˢ (x₁ ·ˢ x₂)
  ... | x₁ | x₂ | True | True = x₁ ⊕ˢ x₂ ⊕ˢ (x₁ ·ˢ x₂)
  standardize (r₁ ⊕ r₂) = standardize r₁ ⊕ˢ standardize r₂
  standardize (r *) = x ⁺ˢ
    where x = standardize r
  standardize (G r) = Gˢ (standardize r)

  isSome : {A : Set} → Maybe A → Set
  isSome (Some _) = Unit
  isSome _ = Void

  _∈Lᵏ_ : List Char → List StdRegExp → Set
  s ∈Lᵏ [] = s == []
  s ∈Lᵏ (r :: rs) = Σ (λ { (p , s') → (p ++ s' == s) × (p ∈Lˢ r) × (s' ∈Lᵏ rs) })
