module Definitions where

  open import Function
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

  {- The regular expressions that do not accept empty string. -}
  data StdRegExp : Set where
    ∅ˢ : StdRegExp
    Litˢ : Char → StdRegExp
    _·ˢ_ : StdRegExp → StdRegExp → StdRegExp
    _⊕ˢ_ : StdRegExp → StdRegExp → StdRegExp
    _⁺ˢ : StdRegExp → StdRegExp -- accepts one or more of the given StdRegExp

  infix 1 _⁺ˢ
  infixr 2 _·ˢ_
  infixr 3 _⊕ˢ_

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

  {- Suffix xs ys means that xs is a suffix of ys -}
  data Suffix {A : Set} : List A → List A → Set where
    Stop : ∀ {x xs} → Suffix xs (x ∷ xs)
    Drop : ∀ {y xs ys} → Suffix xs ys → Suffix xs (y ∷ ys)

  {- A type to make it obvious to Agda that our function will terminate. -}
  data RecursionPermission {A : Set} : List A → Set where
    CanRec : {ys : List A} → ((xs : List A) → Suffix xs ys → RecursionPermission xs) → RecursionPermission ys

  isJust : {A : Set} → Maybe A → Set
  isJust (just _) = ⊤
  isJust _ = ⊥

  data _∈Lᵏ_ : (List Char) → List StdRegExp → Set where
    emp : [] ∈Lᵏ []
    cons : ∀ {s r rs} → (p s' : List Char) → (p ++ s' ≡ s) → (p ∈Lˢ r) → (s' ∈Lᵏ rs) → s ∈Lᵏ (r ∷ rs)

  is-equal : (x y : Char) → Maybe (x ≡ y)
  is-equal x y = decToMaybe (x Data.Char.≟ y)
