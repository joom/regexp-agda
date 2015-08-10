module Definitions where

  open import Data.Char
  open import Data.Bool
  open import Data.Empty
  open import Data.List
  open import Data.Maybe
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

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

  _ ∈L ∅ = ⊥
  s ∈L ε = s ≡ []
  s ∈L (Lit c) = s ≡ c ∷ []
  s ∈L (r₁ ⊕ r₂) = (s ∈L r₁) ⊎ (s ∈L r₂)
  s ∈L (r₁ · r₂) = Σ (List Char × List Char) (λ { (p , q) → (p ++ q ≡ s) × (p ∈L r₁) × (q ∈L r₂) })
  s ∈L (r *) = s ∈Lˣ r
  s ∈L (G r) = s ∈L r

  data _∈Lˣ_ where
    Ex : ∀ {s r} → s ≡ [] → s ∈Lˣ r
    Cx : ∀ {s s₁ s₂ r} → s₁ ++ s₂ ≡ s → s₁ ∈L r → s₂ ∈Lˣ r → s ∈Lˣ r

  _∈Lˢ_ : List Char → StdRegExp → Set
  data _∈L⁺_ : List Char → StdRegExp → Set

  _ ∈Lˢ ∅ˢ = ⊥
  s ∈Lˢ (Litˢ c) = s ≡ c ∷ []
  s ∈Lˢ (r₁ ⊕ˢ r₂) = (s ∈Lˢ r₁) ⊎ (s ∈Lˢ r₂)
  s ∈Lˢ (r₁ ·ˢ r₂) = Σ (List Char × List Char) (λ { (p , q)  → (p ++ q ≡ s) × (p ∈Lˢ r₁) × (q ∈Lˢ r₂) })
  s ∈Lˢ (r ⁺ˢ) = s ∈L⁺ r
  s ∈Lˢ (Gˢ r) = s ∈Lˢ r

  data _∈L⁺_ where
    S+ : ∀ {s r} → s ∈Lˢ r → s ∈L⁺ r
    C+ : ∀ {s s₁ s₂ r} → s₁ ++ s₂ ≡ s → s₁ ∈Lˢ r → s₂ ∈L⁺ r → s ∈L⁺ r

  {- Suffix xs ys means that xs is a suffix of ys -}
  data Suffix {A : Set} : List A → List A → Set where
    Stop : ∀ {x xs} → Suffix xs (x ∷ xs)
    Drop : ∀ {y xs ys} → Suffix xs ys → Suffix xs (y ∷ ys)

  {- A type to make it obvious to Agda that our function will terminate. -}
  data RecursionPermission {A : Set} : List A → Set where
    CanRec : {ys : List A} → ((xs : List A) → Suffix xs ys → RecursionPermission xs) → RecursionPermission ys

  -- Two lemmas needed for definitions.

  empty-append : {xs ys : List Char} → xs ++ ys ≡ [] → (xs ≡ []) × (ys ≡ [])
  empty-append {[]} {[]} refl = refl , refl
  empty-append {[]} {_ ∷ _} ()
  empty-append {_ ∷ _} {[]} ()
  empty-append {_ ∷ _} {_ ∷ _} ()

  empty-append-δ : ∀ {x y r} → x ++ y ≡ [] → (x ∈L r) ⊎ (y ∈L r) → ([] ∈L r → ⊥) → ⊥
  empty-append-δ {x}{y}{r} eq inL f with empty-append {x}{y} eq
  empty-append-δ eq (inj₁ inL) f | refl , refl = f inL
  empty-append-δ eq (inj₂ inL) f | refl , refl = f inL

  -- Checks if a given regexp accepts empty string.
  δ' : (r : RegExp) → ([] ∈L r) ⊎ (¬ ([] ∈L r))
  δ' ∅ = inj₂ (λ ())
  δ' ε = inj₁ refl
  δ' (Lit x) = inj₂ (λ ())
  δ' (r₁ · r₂) with δ' r₁ | δ' r₂
  ... | inj₂ p | _ = inj₂ (λ {((x , y) , (a , (b , _))) → empty-append-δ {x}{y}{r₁} a (inj₁ b) p})
  ... | _ | inj₂ q = inj₂ (λ {((x , y) , (a , (_ , c))) → empty-append-δ {x}{y}{r₂} a (inj₂ c) q})
  ... | inj₁ p | inj₁ q = inj₁ (([] , []) , refl , p , q)
  δ' (r₁ ⊕ r₂) with δ' r₁ | δ' r₂
  ... | (inj₁ p) | _ = inj₁ (inj₁ p)
  ... | _ | (inj₁ q) = inj₁ (inj₂ q)
  ... | (inj₂ p) | (inj₂ q) = inj₂ (sub-lemma p q)
    where sub-lemma : ∀ {l1 l2} {a : Set l1} {b : Set l2} → (¬ a) → (¬ b) → ¬ (a ⊎ b)
          sub-lemma f _ (inj₁ a) = f a
          sub-lemma _ g (inj₂ b) = g b
  δ' (r *) = inj₁ (Ex refl)
  δ' (G r) = δ' r

  -- Checks if a given regexp accepts empty string. true, if it accepts ε, false otherwise.
  δ : RegExp → Bool
  δ r with δ' r
  ... | inj₁ _ = true
  ... | inj₂ _ = false

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
  standardize (r *) = x ⁺ˢ
    where x = standardize r
  standardize (G r) = Gˢ (standardize r)

  isJust : {A : Set} → Maybe A → Set
  isJust (just _) = ⊤
  isJust _ = ⊥

  _∈Lᵏ_ : List Char → List StdRegExp → Set
  s ∈Lᵏ [] = s ≡ []
  s ∈Lᵏ (r ∷ rs) = Σ (List Char × List Char) (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × (s' ∈Lᵏ rs) })
