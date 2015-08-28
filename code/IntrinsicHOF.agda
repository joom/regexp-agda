open import Definitions
open import Lemmas
import OverallMatcher

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
        → (cs : List Char → List Char)
        → (r : StdRegExp)
        → (s : List Char)
        → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe ((cs s) ∈Lˢ (c r)))
        → RecursionPermission s
        → Maybe ((cs s) ∈Lˢ (c r))
  match _ _ ∅ˢ s k perm = nothing
  match _ _ (Litˢ x) [] k perm = nothing
  match _ _ (Litˢ x) (y ∷ ys) k perm with y Data.Char.≟ x
  ... | no _ = nothing
  ... | yes p = k {y ∷ []} {ys} refl (cong (λ q → q ∷ []) p)
  match c cs (r₁ ·ˢ r₂) s k (CanRec f) =
    match (λ r → c (r ·ˢ r₂)) cs r₁ s
          (λ {p}{s'} eq inL → match (λ r → c (r₁ ·ˢ r)) (λ x → cs s) r₂ s'
                                     (λ {p'}{s''} eq' inL' → k {p ++ p'}{s''} (replace-right p s' p' s'' s eq' eq) ((p , p') , refl , inL , inL'))
                                     (f _ (suffix-continuation eq inL)) ) (CanRec f)
  match c cs (r₁ ⊕ˢ r₂) s k perm =
    match (c ∘ (λ r → r ⊕ˢ r₂)) cs r₁ s (λ {p}{s'} eq inL → k {p}{s'} eq (inj₁ inL)) perm ∣
    match (c ∘ (λ r → r₁ ⊕ˢ r)) cs r₂ s (λ {p}{s'} eq inL → k {p}{s'} eq (inj₂ inL)) perm
  match c cs (r ⁺ˢ) s k (CanRec f) =
    match (c ∘ _⁺ˢ) cs r s (λ {p}{s'} eq inL → k {p}{s'} eq (S+ inL)) (CanRec f) ∣
    match (c ∘ _⁺ˢ) cs r s
          (λ {p}{s'} eq inL → match c (λ _ → cs s) (r ⁺ˢ) s'
                                    (λ {p'}{s''} eq' inL' → k {p ++ p'}{s''} (replace-right p s' p' s'' s eq' eq) (C+ {p ++ p'}{p}{p'} refl inL inL'))
                                    (f _ (suffix-continuation eq inL))) (CanRec f)

  match-completeness : (c : StdRegExp → StdRegExp)
                     → (cs : List Char → List Char)
                     → (r : StdRegExp)
                     → (s : List Char)
                     → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe ((cs s) ∈Lˢ (c r)))
                     → (perm : RecursionPermission s)
                     → (cs s) ∈Lˢ (c r)
                     → isJust (match c cs r s k perm)
  match-completeness c _ ∅ˢ s k perm inL = {!!}
  match-completeness c _ (Litˢ x) s k perm inL = {!!}
  match-completeness c _ (r₁ ·ˢ r₂) s k perm inL = {!!}
  match-completeness c _ (r₁ ⊕ˢ r₂) s k perm inL = {!!}
  match-completeness c _ (r ⁺ˢ) s k perm inL = {!!}

  -- Standard "accepts"

  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = is-just (match id id r s empty-continuation (well-founded s))

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with match id id r s empty-continuation (well-founded s)
  ... | just pf = pf
  acceptsˢ-soundness r s () | nothing

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r s inL = is-just-lemma (match-completeness id id r s empty-continuation (well-founded s) inL)

  open OverallMatcher.Matcher {_acceptsˢ_}{acceptsˢ-soundness}{acceptsˢ-completeness}
