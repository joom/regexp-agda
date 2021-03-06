open import Definitions
open import Lemmas

module IntrinsicHOF where

  open import Category.Monad
  open import Function
  open import Data.Char
  open import Data.Bool
  open import Data.Empty
  open import Data.List
  open import Data.Maybe
  import Data.Maybe.Categorical
  open import Data.Product
  import Data.String as String
  open import Data.Sum
  open import Data.Unit
  open import Induction.WellFounded
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  import Agda.Primitive

  open RawMonadPlus {Agda.Primitive.lzero} Data.Maybe.Categorical.monadPlus renaming (∅ to fail)

  match : (C : Set)
        → (r : StdRegExp)
        → (s : List Char)
        → (k : (p s' : List Char) → (p ++ s' ≡ s) → (p ∈Lˢ r) → Maybe C)
        → Acc Suffix s
        → Maybe C
  match C ∅ˢ s k perm = nothing
  match C (Litˢ c) [] k perm = nothing
  match C (Litˢ c) (x ∷ xs) k perm =
      do refl ← is-equal x c
         k [ x ] xs refl ∈ˢLit
  match C (r₁ ·ˢ r₂) s k (acc f) =
    match C r₁ s (λ p s' eq inL → match C r₂ s' (λ p' s'' eq' inL' → k (p ++ p') s'' (replace-right eq' eq) (∈ˢ· refl inL inL')) (f _ (suffix-after-∈Lˢ eq inL))) (acc f)
  match C (r₁ ⊕ˢ r₂) s k perm =
    match C r₁ s (λ p s' eq inL → k p s' eq (∈ˢ⊕₁ inL)) perm ∣
    match C r₂ s (λ p s' eq inL → k p s' eq (∈ˢ⊕₂ inL)) perm
  match C (r ⁺ˢ) s k (acc f) =
    match C r s (λ p s' eq inL → k p s' eq (∈ˢS+ inL)) (acc f) ∣
    match C r s (λ p s' eq inL → match C (r ⁺ˢ) s' (λ p' s'' eq' inL' → k (p ++ p') s'' (replace-right eq' eq) (∈ˢC+ refl inL inL') ) (f _ (suffix-after-∈Lˢ eq inL))) (acc f)

  match-completeness : (C : Set)
                     → (r : StdRegExp)
                     → (s : List Char)
                     → (k : (p s' : List Char) → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
                     → (perm : Acc Suffix s)
                     → Σ (List Char × List Char) (λ { (p , s') → Σ _ (λ eq → Σ _ (λ inL → isJust (k p s' eq inL))) })
                     → isJust (match C r s k perm)
  match-completeness _ ∅ˢ _ _ _ (_ , _ , () , _)
  match-completeness C (Litˢ x) .(x ∷ ys) k perm ((.(x ∷ []) , ys) , refl , ∈ˢLit , m) with x Data.Char.≟ x
  ... | no ¬p = ⊥-elim (¬p refl)
  ... | yes refl = m
  match-completeness C (r₁ ·ˢ r₂) .((as ++ bs) ++ ys) k (acc f) ((.(as ++ bs) , ys) , refl , (∈ˢ· {_}{as}{bs} refl inL inL2) , m)
    with match-completeness C r₂ (bs ++ ys) _ (f _ (suffix-after-∈Lˢ (replace-left {as}{bs}{_}{ys} refl refl) inL))
                            (_ , refl , inL2 , subst (λ H → isJust (k (as ++ bs) ys H (∈ˢ· refl inL inL2))) (sym (uip _)) m)
  ... | pf = match-completeness C r₁ _ _ (acc f) (_ , replace-left {as}{bs}{_}{ys} refl refl , inL , pf)
  match-completeness C (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , eq , ∈ˢ⊕₁ inL , m)
    with match-completeness C r₁ s (λ p s' eq' inL' → k p s' eq' (∈ˢ⊕₁ inL') ) perm (_ , eq , inL , m)
  ... | pf = or-just (inj₁ pf)
  match-completeness C (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , eq , ∈ˢ⊕₂ inL , m)
    with match-completeness C r₂ s (λ p s' eq' inL' → k p s' eq' (∈ˢ⊕₂ inL')) perm ((_ , eq , inL , m))
  ... | pf =  or-just {_}{match C r₁ s (λ p s' eq' inL' → k p s' eq' (∈ˢ⊕₁ inL')) perm} (inj₂ pf)
  match-completeness C (r ⁺ˢ) s k (acc f) ((xs , ys) , eq , ∈ˢS+ x , m) =
    or-just (inj₁ (match-completeness C r s (λ p s' eq' inL' → k p s' eq' (∈ˢS+ inL')) (acc f) (_ , eq , x , m)))
  match-completeness C (r ⁺ˢ) ._ k (acc f) ((._ , ys) , refl , ∈ˢC+ {._}{s₁}{s₂} refl inL inL2 , m)
    with match-completeness C (r ⁺ˢ) (s₂ ++ ys) _ (f _ (suffix-after-∈Lˢ (append-assoc s₁ s₂ ys) inL))
                            (_ , refl , inL2 , subst (λ H → isJust (k (s₁ ++ s₂) ys H (∈ˢC+ refl inL inL2))) (sym (uip _)) m)
  ... | pf = or-just {_}{match C r _ (λ p s' eq inL → k p s' eq (∈ˢS+ inL)) (acc f)}
                     (inj₂ (match-completeness C r ((s₁ ++ s₂) ++ ys) _ _ (_ , append-assoc s₁ s₂ ys , inL , pf)))

  -- Standard "accepts"

  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = is-just (match _ r s (λ p s' → empty-continuation) (well-founded s))

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with match _ r s (λ p s' → empty-continuation) (well-founded s)
  ... | just pf = pf
  acceptsˢ-soundness r s () | nothing

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r s inL = is-just-lemma (match-completeness _ r s (λ p s' → empty-continuation) (well-founded s) ((s , []) , append-rh-[] s , inL , tt))

  acceptsˢ-intrinsic : (r : StdRegExp) → (s : List Char) → Maybe (s ∈Lˢ r)
  acceptsˢ-intrinsic r s = match _ r s (λ p s' → empty-continuation) (well-founded s)

  open import Matcher {_acceptsˢ_}{acceptsˢ-soundness}{acceptsˢ-completeness}
