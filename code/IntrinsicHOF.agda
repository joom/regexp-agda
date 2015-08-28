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

  empty-continuation : ∀ {p' s' s'' r} → (p' ++ s'' ≡ s') → (p' ∈Lˢ r) → Maybe (s' ∈Lˢ r)
  empty-continuation {p'}{s'}{s'' = []}{r} eq inL =  just (eq-replace (cong₂ _∈Lˢ_ {_}{_}{r}{r} (trans (sym (append-rh-[] p')) eq) refl ) inL)
  empty-continuation {s'' = x ∷ s''} eq inL = nothing

  suffix-continuation : ∀ {p s' s r} → (p ++ s' ≡ s) → (p ∈Lˢ r) → Suffix s' s
  suffix-continuation {p}{s'}{s}{r} eq inL = eq-replace (cong₂ Suffix refl eq) (append-suffix2 {p}{s'}{r} inL)

  match : (c : StdRegExp → StdRegExp)
        → (r : StdRegExp)
        → (s : List Char)
        → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe (s ∈Lˢ (c r)))
        → RecursionPermission s
        → Maybe (s ∈Lˢ (c r))
  match c ∅ˢ s k perm = nothing
  match c (Litˢ x) [] k perm = nothing
  match c (Litˢ x) (y ∷ ys) k perm with y Data.Char.≟ x
  ... | no _ = nothing
  ... | yes p = k {y ∷ []} {ys} refl (cong (λ q → q ∷ []) p)
  match c (r₁ ·ˢ r₂) s k (CanRec f) =
    match (λ r → c (r ·ˢ r₂)) r₁ s
          (λ {p}{s'} eq inL → (match (λ x → x) r₂ s' (λ {p'}{s''} eq' inL' → empty-continuation eq' inL') (f _ (suffix-continuation eq inL)))
                               >>= (λ inL' → k {s}{[]} (append-rh-[] s) ((p , s') , eq , inL , inL')) ) (CanRec f)
  match c (r₁ ⊕ˢ r₂) s k perm =
    match (c ∘ (λ r → r ⊕ˢ r₂)) r₁ s (λ {p}{s'} eq inL → k {p}{s'} eq (inj₁ inL)) perm ∣
    match (c ∘ (λ r → r₁ ⊕ˢ r)) r₂ s (λ {p}{s'} eq inL → k {p}{s'} eq (inj₂ inL)) perm
  match c (r ⁺ˢ) s k (CanRec f) =
    match (c ∘ _⁺ˢ) r s (λ {p}{s'} eq inL → k {p}{s'} eq (S+ inL)) (CanRec f) ∣
    match (c ∘ _⁺ˢ) r s
          (λ {p}{s'} eq inL → (match (λ x → x) (r ⁺ˢ) s' (λ {p'}{s''} eq' inL' → empty-continuation eq' inL') (f _ (suffix-continuation eq inL)))
                               >>= (λ inL' → k {s}{[]} (append-rh-[] s) (C+ {s}{p}{s'} eq inL inL'))) (CanRec f)

  match-completeness : (c : StdRegExp → StdRegExp)
                     → (r : StdRegExp)
                     → (s : List Char)
                     → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe (s ∈Lˢ (c r)))
                     → (perm : RecursionPermission s)
                     → s ∈Lˢ (c r)
                     → isJust (match c r s k perm)
  match-completeness c ∅ˢ s k inL = {!!}
  match-completeness c (Litˢ x) s k inL = {!!}
  match-completeness c (r₁ ·ˢ r₂) s k inL = {!!}
  match-completeness c (r₁ ⊕ˢ r₂) s k inL = {!!}
  match-completeness c (r ⁺ˢ) s k inL = {!!}

  -- Standard "accepts"

  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = is-just (match id r s (λ {p}{s'} eq inL → empty-continuation eq inL) (well-founded s))

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with match id r s (λ {p}{s'} eq inL → empty-continuation eq inL) (well-founded s)
  ... | just pf = pf
  acceptsˢ-soundness r s () | nothing

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r s inL = {!!}

  open OverallMatcher.Matcher {_acceptsˢ_}{acceptsˢ-soundness}{acceptsˢ-completeness}

  ex4 = exec (G (Lit 'a' · Lit 'b' · Lit 'c') ) "abc"
    where open OverallMatcher
