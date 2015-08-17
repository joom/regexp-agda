open import Definitions
open import Lemmas

module ExtrinsicMatcher where

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
  {- Show that if match r s k perm is true, then there is a split of s, namely s₁ s₂, such that s₁ ∈L r and k s₂ is true. -}
  match-soundness : (r : StdRegExp) → (s : List Char) → (k : List StdRegExp) → match r s k ≡ true → (Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
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

  -- {- Show that if there is a split of s, namely s₁ s₂, such that s₁ ∈L r and k s₂ is true, then match r s k perm is true. -}
  match-completeness : (r : StdRegExp) → (s : List Char) → (k : List StdRegExp) → (Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k})) → match r s k ≡ true
  match-completeness ∅ˢ _ _ (_ , _ , c , _) = ⊥-elim c
  match-completeness (Litˢ _) [] _ ((.(_ ∷ []) , _) , () , refl , _)
  match-completeness (Litˢ x) .(x ∷ xs) k ((.(x ∷ []) , xs) , refl , refl , rest) with x Data.Char.≟ x
  ... | no p = ⊥-elim (p refl)
  match-completeness (Litˢ x) .((x ∷ []) ++ []) [] ((.(x ∷ []) , .[]) , refl , refl , refl) | yes p = refl
  match-completeness (Litˢ x) .((x ∷ []) ++ xs) (k ∷ ks) ((.(x ∷ []) , xs) , refl , refl , rest) | yes p = {!match-completeness k xs ks rest!}
  match-completeness (r₁ ·ˢ r₂) s k ((xs , ys) , b , ((ms , ns) , tot , ms∈r₁ , ns∈r₂) , d) with tot | b | append-assoc ms ns ys
  match-completeness (r₁ ·ˢ r₂) .((ms ++ ns) ++ ys) k ((.(ms ++ ns) , ys) , b , ((ms , ns) , tot , ms∈r₁ , ns∈r₂) , d) | refl | refl | p3 with match-completeness r₂ (ns ++ ys) k ((ns , ys) , refl , ns∈r₂ , d)
  ... | x = match-completeness r₁ ((ms ++ ns) ++ ys) _ ((ms , ns ++ ys) , (p3 , (ms∈r₁ , (ns , ys) , (refl , (ns∈r₂ , d)))))
  match-completeness (r₁ ⊕ˢ r₂) s k ((xs , ys) , eq , inj₁ p , rest) = either-if (inj₁ (match-completeness r₁ s k ((xs , ys) , eq , p , rest) ))
  match-completeness (r₁ ⊕ˢ r₂) s k ((xs , ys) , eq , inj₂ p , rest) = either-if {match r₁ s k} {match r₂ s k} (inj₂ (match-completeness r₂ s k ((xs , ys) , eq , (p , rest))))
  match-completeness (r ⁺ˢ) s k ((xs , ys) , b , S+ x , d) = either-if (inj₁ (match-completeness r s k ((xs , ys) , b , x , d)))
  match-completeness (r ⁺ˢ) s k ((._ , ys) , b , C+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c , d) with match r s k
  match-completeness (r ⁺ˢ) s k ((._ , ys) , b , C+ refl q c , d) | true = refl
  match-completeness (r ⁺ˢ) s k ((._ , ys) , b , C+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c , d) | false = match-completeness r s ((r ⁺ˢ) ∷ k) ((s₁ , s₂ ++ ys) , trans (append-assoc s₁ s₂ ys) b , q , (s₂ , ys) , refl , c , d)

  _accepts_ : RegExp → String.String → Bool
  r accepts s = match-plus (δ r , standardize r) l []
    where l = String.toList s
          match-plus : Bool × StdRegExp → (s : List Char) → (k : List StdRegExp) → Bool
          match-plus (false , r) s k = match r s k
          match-plus (true , r) s k = if null s then true else match r s k

  -- -- Overall correctness

  correct-soundness : (r : RegExp)
                    → (s : String.String)
                    → r accepts s ≡ true
                    → (String.toList s) ∈L r
  correct-soundness r s eq with String.toList s | δ' r
  ... | xs | inj₂ q with match-soundness (standardize r) xs _ eq
  ... | ((as , bs) , a , b , c) with ∈L-soundness as r (inj₂ b)
  correct-soundness r s eq | xs | inj₂ q | (_ , _ ∷ _ ) , _ , _ , () | as∈Lr
  correct-soundness r s eq | xs | inj₂ q | (as , [] ) , a , b , c | as∈Lr with trans (sym (append-rh-[] as)) a
  correct-soundness r s eq | as | inj₂ q | (.as , [] ) , a , b , c | as∈Lr | refl = as∈Lr
  correct-soundness r s eq | [] | inj₁ p = p
  correct-soundness r s eq | x ∷ xs | inj₁ p with match-soundness (standardize r) (x ∷ xs) _ eq
  ... | ((as , bs) , a , b , c) with ∈L-soundness as r (inj₂ b)
  correct-soundness r s eq | x ∷ xs | inj₁ p | (_ , _ ∷ _ ) , _ , _ , () | _
  correct-soundness r s eq | x ∷ xs | inj₁ p | (as , [] ) , a , b , refl | inL-sn with trans (sym (append-rh-[] as)) a
  correct-soundness r s eq | x ∷ xs | inj₁ p | (.(x ∷ xs) , []) , a , b , refl | inL-sn | refl = inL-sn

  correct-completeness : (r : RegExp)
                       → (s : String.String)
                       → (String.toList s) ∈L r
                       → r accepts s ≡ true
  correct-completeness r s inL with String.toList s | δ' r
  correct-completeness r s inL | [] | inj₁ p = refl
  correct-completeness r s inL | x ∷ xs | inj₁ p with ∈L-completeness (x ∷ xs) r inL
  correct-completeness r s inL | x ∷ xs | inj₁ p | inj₁ (d , ())
  correct-completeness r s inL | x ∷ xs | inj₁ p | inj₂ q = match-completeness (standardize r) _ _  ((x ∷ xs , []) , cong (λ l → x ∷ l) (append-rh-[] xs) , q , refl)
  correct-completeness r s inL | xs | inj₂ q with ∈L-completeness xs r inL
  correct-completeness r s inL | .[] | inj₂ q | inj₁ (d , refl) = ⊥-elim (q inL)
  correct-completeness r s inL | xs | inj₂ q | inj₂ p with non-empty {standardize r}
  correct-completeness r s inL | [] | inj₂ q | inj₂ p | f = ⊥-elim (q inL)
  correct-completeness r s inL | x ∷ xs | inj₂ q | inj₂ p | f = match-completeness (standardize r) _ _ ((x ∷ xs , []) , cong (λ l → x ∷ l) (append-rh-[] xs) , p , refl)
