open import Definitions
open import Lemmas

module ExtrinsicDefun where

  open import Data.Char
  open import Data.Bool
  open import Data.Empty
  open import Data.List
  open import Data.Maybe
  open import Data.Product
  import Data.String as String
  open import Data.Sum
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Binary.PropositionalEquality

  match : StdRegExp → (s : List Char) → (k : List StdRegExp) → Bool
  match ∅ˢ s k = false
  match (Litˢ x) [] k = false
  match (Litˢ x) (y ∷ ys) k with x Data.Char.≟ y
  ... | no ¬p = false
  match (Litˢ x) (y ∷ ys) [] | yes p = null ys
  match (Litˢ x) (y ∷ ys) (r ∷ rs) | yes p = match r ys rs
  match (r₁ ·ˢ r₂) s k = match r₁ s (r₂ ∷ k)
  match (r₁ ⊕ˢ r₂) s k = (match r₁ s k) ∨ (match r₂ s k)
  match (r ⁺ˢ) s k = (match r s k) ∨ (match r s ((r ⁺ˢ) ∷ k))

  -- Proofs
  match-soundness : (r : StdRegExp) → (s : List Char) → (k : List StdRegExp) → match r s k ≡ true → (Σ (List Char × List Char) (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
  match-soundness ∅ˢ s k ()
  match-soundness (Litˢ x) [] k ()
  match-soundness (Litˢ x) (y ∷ ys) k m with x Data.Char.≟ y
  match-soundness (Litˢ x) (.x ∷ []) [] refl | yes refl = (x ∷ [] , []) , refl , refl , refl
  match-soundness (Litˢ _) (._ ∷ _ ∷ _) [] () | yes refl
  match-soundness (Litˢ x) (.x ∷ ys) (r ∷ rs) m | yes refl = (x ∷ [] , ys) , refl , refl , match-soundness r ys rs m
  match-soundness (Litˢ x) (y ∷ ys) k () | no ¬p
  match-soundness (r₁ ·ˢ r₂) s k m with match-soundness r₁ s (r₂ ∷ k) m
  match-soundness (r₁ ·ˢ r₂) s k m | (xs , ys) , eq , inL , ((as , bs) , eq' , inL' , rest) = (xs ++ as , bs) , (replace-right xs ys as bs s eq' eq , (((xs , as) , refl , inL , inL') , rest))
  match-soundness (r₁ ⊕ˢ r₂) s k m with or-eq {match r₁ s k} {match r₂ s k } m
  match-soundness (r₁ ⊕ˢ r₂) s k m | inj₁ x with match-soundness r₁ s k x
  match-soundness (r₁ ⊕ˢ r₂) s k m | inj₁ x | (p , q) , a , b , c = (p , q) , (a , (inj₁ b , c))
  match-soundness (r₁ ⊕ˢ r₂) s k m | inj₂ y with match-soundness r₂ s k y
  match-soundness (r₁ ⊕ˢ r₂) s k m | inj₂ x | (p , q) , a , b , c = (p , q) , (a , (inj₂ b , c))
  match-soundness (r ⁺ˢ) s k m with or-eq {match r s k} { match r s ((r ⁺ˢ) ∷ k)} m
  match-soundness (r ⁺ˢ) s k m | inj₁ x with match-soundness r s k x
  match-soundness (r ⁺ˢ) s k m | inj₁ x | (xs , ys) , eq , inL , rest = (xs , ys) , (eq , (S+ {xs} {r} inL , rest))
  match-soundness (r ⁺ˢ) s k m | inj₂ y with match-soundness r s ((r ⁺ˢ) ∷ k) y
  match-soundness (r ⁺ˢ) s k m | inj₂ y | (xs , ys) , eq , inL , ((as , bs) , eq' , inL' , rest) = (xs ++ as , bs) , (replace-right xs ys as bs s eq' eq , (C+ {xs ++ as} {xs} {as} refl inL inL' , rest))

  match-completeness : (r : StdRegExp) → (s : List Char) → (k : List StdRegExp) → (Σ (List Char × List Char) (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k})) → match r s k ≡ true
  match-completeness ∅ˢ _ _ (_ , _ , c , _) = ⊥-elim c
  match-completeness (Litˢ _) [] _ ((.(_ ∷ []) , _) , () , refl , _)
  match-completeness (Litˢ x) .(x ∷ xs) k ((.(x ∷ []) , xs) , refl , refl , rest) with x Data.Char.≟ x
  ... | no p = ⊥-elim (p refl)
  match-completeness (Litˢ x) .((x ∷ []) ++ []) [] ((.(x ∷ []) , .[]) , refl , refl , refl) | yes refl = refl
  match-completeness (Litˢ x) .((x ∷ []) ++ xs) (r ∷ k) ((.(x ∷ []) , xs) , refl , refl , rest) | yes refl = match-completeness r xs k rest
  match-completeness (r₁ ·ˢ r₂) s k ((xs , ys) , b , ((ms , ns) , tot , ms∈r₁ , ns∈r₂) , d) = match-completeness r₁ s (r₂ ∷ k) ((ms , ns ++ ys) , replace-left ms ns xs ys s tot b , ms∈r₁ , (ns , ys) , refl , ns∈r₂ , d)
  match-completeness (r₁ ⊕ˢ r₂) s k ((xs , ys) , eq , inj₁ p , rest) = either-if (inj₁ (match-completeness r₁ s k ((xs , ys) , eq , p , rest) ))
  match-completeness (r₁ ⊕ˢ r₂) s k ((xs , ys) , eq , inj₂ p , rest) = either-if {match r₁ s k} {match r₂ s k} (inj₂ (match-completeness r₂ s k ((xs , ys) , eq , (p , rest))))
  match-completeness (r ⁺ˢ) s k ((xs , ys) , b , S+ x , d) = either-if (inj₁ (match-completeness r s k ((xs , ys) , b , x , d)))
  match-completeness (r ⁺ˢ) s k ((._ , ys) , b , C+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c , d) with match r s k
  match-completeness (r ⁺ˢ) s k ((._ , ys) , b , C+ refl q c , d) | true = refl
  match-completeness (r ⁺ˢ) s k ((._ , ys) , b , C+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c , d) | false = match-completeness r s ((r ⁺ˢ) ∷ k) ((s₁ , s₂ ++ ys) , trans (append-assoc s₁ s₂ ys) b , q , (s₂ , ys) , refl , c , d)

  -- Standard "accepts"
  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = match r s []

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with bool-eq (match r s [])
  ... | inj₁ p with match-soundness r s [] p
  acceptsˢ-soundness r .(xs ++ []) m | inj₁ p | (xs , .[]) , refl , inL , refl = eq-replace (sym (cong₂ _∈Lˢ_ {_}{_}{r}{r} (append-rh-[] xs) refl)) inL
  acceptsˢ-soundness r s m | inj₂ q with trans (sym m) q
  ... | ()

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r s inL = match-completeness r s [] ((s , []) , append-rh-[] s , inL , refl)

  open import Matcher {_acceptsˢ_}{acceptsˢ-soundness}{acceptsˢ-completeness}
