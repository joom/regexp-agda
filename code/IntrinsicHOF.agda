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
  open import Data.Unit
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

  or-just : ∀ {A} {a b : Maybe A} → (isJust a) ⊎ (isJust b) → isJust (a ∣ b)
  or-just {a = just x} m = tt
  or-just {a = nothing} (inj₁ x) = ⊥-elim x
  or-just {a = nothing} (inj₂ y) = y

  match-completeness : (C : Set)
                     → (r : StdRegExp)
                     → (s : List Char)
                     → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
                     → (perm : RecursionPermission s)
                     → Σ _ (λ { (p , s') → Σ _ (λ eq → Σ _ (λ inL → isJust (k {p}{s'} eq inL))) })
                     → isJust (match C r s k perm)
  match-completeness _ ∅ˢ _ _ _ (_ , _ , () , _)
  match-completeness C (Litˢ x) .(x ∷ ys) k perm ((.(x ∷ []) , ys) , refl , refl , m) with x Data.Char.≟ x
  ... | no ¬p = ⊥-elim (¬p refl)
  ... | yes refl = m
  match-completeness C (r₁ ·ˢ r₂) .((as ++ bs) ++ ys) k (CanRec f) ((.(as ++ bs) , ys) , refl , ((as , bs) , refl , inL , rest) , m)
    with match-completeness C r₂ (bs ++ ys) {!!} {!!} ?
  ... | pf = match-completeness C r₁ _ {!!} (CanRec f) {!!}
  match-completeness C (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , eq , inj₁ inL , m)
    with match-completeness C r₁ s (λ {p}{s'} eq' inL' → k eq' (inj₁ inL') ) perm (_ , eq , inL , m)
  ... | pf = or-just (inj₁ pf)
  match-completeness C (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , eq , inj₂ inL , m)
    with match-completeness C r₂ s (λ {p}{s'} eq' inL' → k eq' (inj₂ inL')) perm ((_ , eq , inL , m))
  ... | pf =  or-just {_}{match C r₁ s (λ {p} {s'} eq' inL' → k eq' (inj₁ inL')) perm} (inj₂ pf)
  match-completeness C (r ⁺ˢ) s k perm ((xs , ys) , eq , S+ x , m)
    with match-completeness C r s (λ {p}{s'} eq' inL' → k eq' (S+ inL')) perm (_ , eq , x , m)
  ... | pf = {!!}
  match-completeness C (r ⁺ˢ) s k perm ((xs , ys) , eq , C+ x x₁ inL , m)
    with match-completeness C r s {!!} perm {!!}
  ... | pf = {!!}


  -- Standard "accepts"

  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = is-just (match _ r s empty-continuation (well-founded s))

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with match _ r s empty-continuation (well-founded s)
  ... | just pf = pf
  acceptsˢ-soundness r s () | nothing

  -- acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  -- acceptsˢ-completeness r s inL = is-just-lemma (match-completeness _ r s empty-continuation (well-founded s) inL)

  -- open OverallMatcher.Matcher {_acceptsˢ_}{acceptsˢ-soundness}{acceptsˢ-completeness}
