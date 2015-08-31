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
  ... | yes p = k {y ∷ []} {ys} refl (cong (λ q → q ∷ []) p)
  match C (r₁ ·ˢ r₂) s k (CanRec f) =
    match C r₁ s (λ {p}{s'} eq inL → match C r₂ s' (λ {p'}{s''} eq' inL' → k {p ++ p'}{s''} (replace-right p s' p' s'' s eq' eq) ((p , p') , refl , inL , inL')) (f _ (suffix-continuation eq inL))) (CanRec f)
  match C (r₁ ⊕ˢ r₂) s k perm =
    match C r₁ s (λ eq inL → k eq (inj₁ inL)) perm ∣
    match C r₂ s (λ eq inL → k eq (inj₂ inL)) perm
  match C (r ⁺ˢ) s k (CanRec f) =
    match C r s (λ eq inL → k eq (S+ inL)) (CanRec f) ∣
    match C r s (λ {p}{s'} eq inL → match C (r ⁺ˢ) s' (λ {p'}{s''} eq' inL' → k (replace-right p s' p' s'' s eq' eq) (C+ refl inL inL') ) (f _ (suffix-continuation eq inL))) (CanRec f)


  match-completeness : (C : Set)
                     → (r : StdRegExp)
                     → (s : List Char)
                     → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
                     → (perm : RecursionPermission s)
                     → C
                     → isJust (match C r s k perm)
  match-completeness C ∅ˢ s k perm pf = ?
  match-completeness C (Litˢ x) s k perm pf = {!!}
  match-completeness C (r₁ ·ˢ r₂) s k perm pf = {!!}
  match-completeness C (r₁ ⊕ˢ r₂) s k perm pf = {!!}
  match-completeness C (r ⁺ˢ) s k perm pf = {!!}

  -- Standard "accepts"

  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = is-just (match _ r s empty-continuation (well-founded s))

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with match _ r s empty-continuation (well-founded s)
  ... | just pf = pf
  acceptsˢ-soundness r s () | nothing

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r s inL = is-just-lemma (match-completeness _ r s empty-continuation (well-founded s) inL)

  open OverallMatcher.Matcher {_acceptsˢ_}{acceptsˢ-soundness}{acceptsˢ-completeness}
