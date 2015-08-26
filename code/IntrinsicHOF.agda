open import Definitions
open import Lemmas

module IntrinsicHOF where

  open import Category.Monad
  open import Data.Char
  open import Data.Bool
  open import Data.Empty
  open import Data.List
  open import Data.Maybe
  open import Data.Product
  import Data.String as String
  open import Data.Sum
  open import Function
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Binary.PropositionalEquality
  import Agda.Primitive

  open RawMonadPlus {Agda.Primitive.lzero} Data.Maybe.monadPlus renaming (∅ to fail)

  match : (c : StdRegExp → StdRegExp)
        → (r : StdRegExp)
        → (s : List Char)
        → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe (s ∈Lˢ (c r)))
        → Maybe (s ∈Lˢ (c r))
  match c ∅ˢ s k = nothing
  match c (Litˢ x) [] k = nothing
  match c (Litˢ x) (y ∷ ys) k with y Data.Char.≟ x
  ... | no _ = nothing
  ... | yes p = k {y ∷ []} {ys} refl (cong (λ q → q ∷ []) p)
  match c (r₁ ·ˢ r₂) s k = match {!!} r₁ s (λ {p}{s'} eq inL → match {!!} r₂ s' (λ {p'}{s''} eq' inL' → {!!}))
  match c (r₁ ⊕ˢ r₂) s k =
    match (c ∘ (λ r → r ⊕ˢ r₂)) r₁ s (λ {p}{s'} eq inL → k {p}{s'} eq (inj₁ inL))  ∣
    match (c ∘ (λ r → r₁ ⊕ˢ r)) r₂ s (λ {p}{s'} eq inL → k {p}{s'} eq (inj₂ inL))
  match c (r ⁺ˢ) s k =
    match (c ∘ _⁺ˢ) r s (λ {p}{s'} eq inL → {!S+ {s}{r} ?!})  ∣
    match {!!} r s (λ {p}{s'} eq inL → match {!!} (r ⁺ˢ) s' (λ {p'}{s''} eq' inL' → {!!}))
