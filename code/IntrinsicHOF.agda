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
  open import Data.Unit
  open import Function
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Binary.PropositionalEquality hiding ([_])
  import Agda.Primitive

  open RawMonadPlus {Agda.Primitive.lzero} Data.Maybe.monadPlus renaming (∅ to fail)

  match : (C : Set)
        → (r : StdRegExp)
        → (s : List Char)
        → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
        → RecursionPermission s
        → Maybe C
  match C ∅ˢ s k perm = fail
  match C (Litˢ c) [] k perm = fail
  match C (Litˢ c) (x ∷ xs) k perm =
    (isEqual x c) >>= (λ p → k {[ x ]} {xs} refl (cong (λ q → [ q ]) p))
  match C (r₁ ·ˢ r₂) s k (CanRec f) =
    match C r₁ s (λ {p}{s'} eq inL → match C r₂ s' (λ {p'}{s''} eq' inL' → k {p ++ p'}{s''} (replace-right p s' p' s'' s eq' eq) ((p , p') , refl , inL , inL')) (f _ (suffix-after-∈Lˢ eq inL))) (CanRec f)
  match C (r₁ ⊕ˢ r₂) s k perm =
    match C r₁ s (λ eq inL → k eq (inj₁ inL)) perm ∣
    match C r₂ s (λ eq inL → k eq (inj₂ inL)) perm
  match C (r ⁺ˢ) s k (CanRec f) =
    match C r s (λ eq inL → k eq (S+ inL)) (CanRec f) ∣
    match C r s (λ {p}{s'} eq inL → match C (r ⁺ˢ) s' (λ {p'}{s''} eq' inL' → k (replace-right p s' p' s'' s eq' eq) (C+ refl inL inL') ) (f _ (suffix-after-∈Lˢ eq inL))) (CanRec f)

  match-completeness : (C : Set)
                     → (r : StdRegExp)
                     → (s : List Char)
                     → (k : ∀ {p s'} → p ++ s' ≡ s  → p ∈Lˢ r → Maybe C)
                     → (perm : RecursionPermission s)
                     → Σ (List Char × List Char) (λ { (p , s') → Σ _ (λ eq → Σ _ (λ inL → isJust (k {p}{s'} eq inL))) })
                     → isJust (match C r s k perm)
  match-completeness _ ∅ˢ _ _ _ (_ , _ , () , _)
  match-completeness C (Litˢ x) .(x ∷ ys) k perm ((.(x ∷ []) , ys) , refl , refl , m) with x Data.Char.≟ x
  ... | no ¬p = ⊥-elim (¬p refl)
  ... | yes refl = m
  match-completeness C (r₁ ·ˢ r₂) .((as ++ bs) ++ ys) k (CanRec f) ((.(as ++ bs) , ys) , refl , ((as , bs) , refl , inL , inL2) , m)
    with match-completeness C r₂ (bs ++ ys) _ (f _ (suffix-after-∈Lˢ (replace-left as bs _ ys _ refl refl) inL))
                            (_ , refl , inL2 , subst (λ H → isJust (k H (_ , refl , inL , inL2))) (sym (uip _)) m)
  ... | pf = match-completeness C r₁ _ _ (CanRec f) (_ , replace-left as bs _ ys _ refl refl , inL , pf)
  match-completeness C (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , eq , inj₁ inL , m)
    with match-completeness C r₁ s (λ {p}{s'} eq' inL' → k eq' (inj₁ inL') ) perm (_ , eq , inL , m)
  ... | pf = or-just (inj₁ pf)
  match-completeness C (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , eq , inj₂ inL , m)
    with match-completeness C r₂ s (λ {p}{s'} eq' inL' → k eq' (inj₂ inL')) perm ((_ , eq , inL , m))
  ... | pf =  or-just {_}{match C r₁ s (λ {p} {s'} eq' inL' → k eq' (inj₁ inL')) perm} (inj₂ pf)
  match-completeness C (r ⁺ˢ) s k (CanRec f) ((xs , ys) , eq , S+ x , m) =
    or-just (inj₁ (match-completeness C r s (λ {p}{s'} eq' inL' → k eq' (S+ inL')) (CanRec f) (_ , eq , x , m)))
  match-completeness C (r ⁺ˢ) ._ k (CanRec f) ((._ , ys) , refl , C+ {._}{s₁}{s₂} refl inL inL2 , m)
    with match-completeness C (r ⁺ˢ) (s₂ ++ ys) _ (f _ (suffix-after-∈Lˢ (append-assoc s₁ s₂ ys) inL))
                            (_ , refl , inL2 , subst (λ H → isJust (k H (C+ refl inL inL2))) (sym (uip _)) m)
  ... | pf = or-just {_}{match C r _ (λ eq inL → k eq (S+ inL)) (CanRec f)}
                     (inj₂ (match-completeness C r ((s₁ ++ s₂) ++ ys) _ _ (_ , append-assoc s₁ s₂ ys , inL , pf)))

  -- Standard "accepts"

  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = is-just (match _ r s empty-continuation (well-founded s))

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with match _ r s empty-continuation (well-founded s)
  ... | just pf = pf
  acceptsˢ-soundness r s () | nothing

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r s inL = is-just-lemma (match-completeness _ r s empty-continuation (well-founded s) ((s , []) , append-rh-[] s , inL , tt))

  acceptsˢ-intrinsic : (r : StdRegExp) → (s : List Char) → Maybe (s ∈Lˢ r)
  acceptsˢ-intrinsic r s with match _ r s empty-continuation (well-founded s)
  ... | just pf = just pf
  acceptsˢ-intrinsic r s | nothing = nothing

  open import Matcher {_acceptsˢ_}{acceptsˢ-soundness}{acceptsˢ-completeness}
