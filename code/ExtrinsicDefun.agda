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
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

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
  match-soundness : (r : StdRegExp) → (s : List Char) → (k : List StdRegExp) → match r s k ≡ true → s ∈Lᵏ (r ∷ k)
  match-soundness ∅ˢ s k ()
  match-soundness (Litˢ x) [] k ()
  match-soundness (Litˢ x) (y ∷ ys) k m with x Data.Char.≟ y
  match-soundness (Litˢ x) (.x ∷ []) [] refl | yes refl = cons (x ∷ []) [] refl ∈ˢLit emp
  match-soundness (Litˢ _) (._ ∷ _ ∷ _) [] () | yes refl
  match-soundness (Litˢ x) (.x ∷ ys) (r ∷ rs) m | yes refl = cons (x ∷ []) ys refl ∈ˢLit (match-soundness r ys rs m)
  match-soundness (Litˢ x) (y ∷ ys) k () | no ¬p
  match-soundness (r₁ ·ˢ r₂) s k m with match-soundness r₁ s (r₂ ∷ k) m
  match-soundness (r₁ ·ˢ r₂) s k m | cons xs ys eq inL (cons as bs eq' inL' rest) =
    cons (xs ++ as) bs (replace-right {xs} eq' eq) (∈ˢ· refl inL inL') rest
  match-soundness (r₁ ⊕ˢ r₂) s k m with or-eq {match r₁ s k} {match r₂ s k } m
  match-soundness (r₁ ⊕ˢ r₂) s k m | inj₁ x with match-soundness r₁ s k x
  match-soundness (r₁ ⊕ˢ r₂) s k m | inj₁ x | cons p q a b c = cons p q a (∈ˢ⊕₁ b) c
  match-soundness (r₁ ⊕ˢ r₂) s k m | inj₂ y with match-soundness r₂ s k y
  match-soundness (r₁ ⊕ˢ r₂) s k m | inj₂ x | cons p q a b c = cons p q a (∈ˢ⊕₂ b) c
  match-soundness (r ⁺ˢ) s k m with or-eq {match r s k} { match r s ((r ⁺ˢ) ∷ k)} m
  match-soundness (r ⁺ˢ) s k m | inj₁ x with match-soundness r s k x
  match-soundness (r ⁺ˢ) s k m | inj₁ x | cons xs ys eq inL rest = cons xs ys eq (∈ˢS+ inL) rest
  match-soundness (r ⁺ˢ) s k m | inj₂ y with match-soundness r s ((r ⁺ˢ) ∷ k) y
  match-soundness (r ⁺ˢ) s k m | inj₂ y | cons xs ys eq inL (cons as bs eq' inL' rest) =
    cons (xs ++ as) bs (replace-right {xs} eq' eq) (∈ˢC+ refl inL inL') rest

  match-completeness : (r : StdRegExp) → (s : List Char) → (k : List StdRegExp) → s ∈Lᵏ (r ∷ k) → match r s k ≡ true
  match-completeness ∅ˢ _ _ (cons _ _ _ () _)
  match-completeness (Litˢ c) .(c ∷ []) .[] (cons .(c ∷ []) .[] refl ∈ˢLit emp) with c Data.Char.≟ c
  ... | no a = ⊥-elim (a refl)
  ... | yes a = refl
  match-completeness (Litˢ c) .(c ∷ s') (r ∷ k) (cons .(c ∷ []) s' refl ∈ˢLit (cons p s'' eq inL inK)) with c Data.Char.≟ c
  ... | no a = ⊥-elim (a refl)
  match-completeness (Litˢ c) .((c ∷ []) ++ s') (r ∷ k) (cons .(c ∷ []) s' refl ∈ˢLit (cons p s'' eq inL inK)) | yes refl =
    match-completeness r s' k (cons p s'' eq inL inK)
  match-completeness (r₁ ·ˢ r₂) s k (cons xs ys b (∈ˢ· {_}{ms}{ns} tot ms∈r₁ ns∈r₂) d) =
    match-completeness r₁ s (r₂ ∷ k) (cons ms (ns ++ ys) (replace-left {ms} tot b) ms∈r₁ (cons ns ys refl ns∈r₂ d))
  match-completeness (r₁ ⊕ˢ r₂) s k (cons xs ys eq (∈ˢ⊕₁ p) rest) = either-if (inj₁ (match-completeness r₁ s k (cons xs ys eq p rest)))
  match-completeness (r₁ ⊕ˢ r₂) s k (cons xs ys eq (∈ˢ⊕₂ p) rest) = either-if {match r₁ s k} {match r₂ s k} (inj₂ (match-completeness r₂ s k (cons xs ys eq p rest)))
  match-completeness (r ⁺ˢ) s k (cons xs ys b (∈ˢS+ x) d) = either-if (inj₁ (match-completeness r s k (cons xs ys b x d)))
  match-completeness (r ⁺ˢ) s k (cons ._ ys b (∈ˢC+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c) d) with match r s k
  match-completeness (r ⁺ˢ) s k (cons ._ ys b (∈ˢC+ refl q c) d) | true = refl
  match-completeness (r ⁺ˢ) s k (cons ._ ys b (∈ˢC+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c) d) | false =
    match-completeness r s ((r ⁺ˢ) ∷ k) (cons s₁ (s₂ ++ ys) (trans (append-assoc s₁ s₂ ys) b) q (cons s₂ ys refl c d))

  -- Standard "accepts"
  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = match r s []

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with bool-eq (match r s [])
  ... | inj₁ p with match-soundness r s [] p
  acceptsˢ-soundness r .(xs ++ []) m | inj₁ p | cons xs .[] refl inL emp = eq-replace (sym (cong₂ _∈Lˢ_ {_}{_}{r}{r} (append-rh-[] xs) refl)) inL
  acceptsˢ-soundness r s m | inj₂ q with trans (sym m) q
  ... | ()

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r s inL = match-completeness r s [] (cons s [] (append-rh-[] s) inL emp)

  open import Matcher {_acceptsˢ_}{acceptsˢ-soundness}{acceptsˢ-completeness}
