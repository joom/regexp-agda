open import Definitions
open import Lemmas
open import RegExpDefinitions

module IntrinsicDefun where

  open import Category.Monad
  open import Function
  open import Data.Bool
  open import Data.Char
  open import Data.Empty
  open import Data.List
  open import Data.Maybe
  import Data.Maybe as M
  open import Data.Product
  import Data.String as String
  open import Data.Sum
  open import Data.Unit
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Binary.PropositionalEquality hiding ([_])
  import Agda.Primitive

  -- Using groups

  -- open RawMonadZero {Agda.Primitive.lzero} Data.Maybe.monadZero renaming (∅ to fail)
  open RawMonadPlus {Agda.Primitive.lzero} Data.Maybe.monadPlus renaming (∅ to fail)

  change-∈L-S+ : ∀ {s r k} → s ∈Lᵏ (r ∷ k) → s ∈Lᵏ ((r ⁺ˢ) ∷ k)
  change-∈L-S+ (cons _ _ eq inL inK) = cons _ _ eq (∈ˢS+ inL) inK

  change-∈L-C+ : ∀ {s r k} → s ∈Lᵏ (r ∷ (r ⁺ˢ) ∷ k) → s ∈Lᵏ ((r ⁺ˢ) ∷ k)
  change-∈L-C+ (cons _ _ eq inL (cons _ _ eq' inL' inK)) = cons _ _ (replace-right eq' eq) (∈ˢC+ refl inL inL') inK

  change-∈L-⊕₁ : ∀ {s r₁ r₂ k} → s ∈Lᵏ (r₁ ∷ k) → s ∈Lᵏ ((r₁ ⊕ˢ r₂) ∷ k)
  change-∈L-⊕₁ (cons _ _ eq inL inK) = cons _ _ eq (∈ˢ⊕₁ inL) inK

  change-∈L-⊕₂ : ∀ {s r₁ r₂ k} → s ∈Lᵏ (r₂ ∷ k) → s ∈Lᵏ ((r₁ ⊕ˢ r₂) ∷ k)
  change-∈L-⊕₂ (cons _ _ eq inL inK) = cons _ _ eq (∈ˢ⊕₂ inL) inK

  change-∈L-· : ∀ {s r₁ r₂ k} → s ∈Lᵏ (r₁ ∷ r₂ ∷ k) → s ∈Lᵏ ((r₁ ·ˢ r₂) ∷ k)
  change-∈L-· (cons _ _ eq inL (cons _ _ eq' inL' inK)) = cons _ _ (replace-right eq' eq) (∈ˢ· refl inL inL') inK

  mutual
    match-helper : (k : List StdRegExp) → (s : List Char) → Maybe (s ∈Lᵏ k)
    match-helper [] [] = just emp
    match-helper [] (x ∷ s) = nothing
    match-helper (r ∷ rs) s = match r s rs

    -- Doing the matching and soundness proof at the same time.
    match : (r : StdRegExp)
          → (s : List Char)
          → (k : List StdRegExp)
          → Maybe (s ∈Lᵏ (r ∷ k))
    match ∅ˢ s k = nothing
    match (Litˢ c) [] k = nothing
    match (Litˢ c) (x ∷ xs) k =
        do refl ← is-equal x c
           pf ← match-helper k xs
           just (cons [ x ] xs refl ∈ˢLit pf)
    match (r₁ ·ˢ r₂) s k = M.map change-∈L-· (match r₁ s (r₂ ∷ k))
    match (r₁ ⊕ˢ r₂) s k = (M.map change-∈L-⊕₁ (match r₁ s k)) ∣ (M.map change-∈L-⊕₂ (match r₂ s k))
    match (r ⁺ˢ) s k = (M.map change-∈L-S+ (match r s k)) ∣ (M.map change-∈L-C+ (match r s ((r ⁺ˢ) ∷ k)))

  mutual
    match-helper-some : (k : List StdRegExp) → (s : List Char) → (s ∈Lᵏ k) → isJust (match-helper k s)
    match-helper-some [] .[] emp = tt
    match-helper-some (r ∷ rs) s pf = match-completeness r s rs pf

    match-completeness : (r : StdRegExp)
                       → (s : List Char)
                       → (k : List StdRegExp)
                       → s ∈Lᵏ (r ∷ k)
                       → isJust (match r s k)
    match-completeness ∅ˢ s k (cons _ _ eq () inK)
    match-completeness (Litˢ x) .(x ∷ _) k (cons _ s' refl ∈ˢLit inK) with x Data.Char.≟ x
    match-completeness (Litˢ x) .((x ∷ []) ++ s') k (cons .(x ∷ []) s' refl ∈ˢLit inK) | no ¬p = ⊥-elim (¬p refl)
    match-completeness (Litˢ x) .((x ∷ []) ++ s') k (cons .(x ∷ []) s' refl ∈ˢLit inK) | yes refl with match-helper k s' | match-helper-some k s' inK
    match-completeness (Litˢ x) .((x ∷ []) ++ s') k (cons .(x ∷ []) s' refl ∈ˢLit inK) | yes refl | just _ | tt = tt
    match-completeness (Litˢ x) .((x ∷ []) ++ s') k (cons .(x ∷ []) s' refl ∈ˢLit inK) | yes refl | nothing | ()
    match-completeness (r₁ ·ˢ r₂) s k (cons p s' eq (∈ˢ· {_}{as}{bs} eq' inL' inK') inK)
      with match r₁ s (r₂ ∷ k)
         | match-completeness r₁ s (r₂ ∷ k) (cons as (bs ++ s') (replace-left {as} eq' eq) inL' (cons bs s' refl inK' inK))
    ... | nothing | ()
    ... | just _  | tt = tt
    match-completeness (r₁ ⊕ˢ r₂) s k (cons p s' eq (∈ˢ⊕₁ inL) inK)
      with match r₁ s k | match-completeness r₁ s k (cons p s' eq inL inK)
    ... | nothing | ()
    ... | just _  | _ = tt
    match-completeness (r₁ ⊕ˢ r₂) s k (cons p s' eq (∈ˢ⊕₂ inL) inK) with match r₁ s k
    ... | just pf = tt
    ... | nothing with match r₂ s k | match-completeness r₂ s k (cons p s' eq inL inK)
    ...           | nothing | ()
    ...           | just _  | _ = tt
    match-completeness (r ⁺ˢ) s k (cons p s' eq (∈ˢS+ x) inK)
      with match r s k | match-completeness r s k (cons p s' eq x inK)
    ... | nothing | ()
    ... | just _  | _ = tt
    match-completeness (r ⁺ˢ) .((s₁ ++ s₂) ++ s') k (cons ._ s' refl (∈ˢC+ {._}{s₁}{s₂} refl y inL) inK)
      with match r ((s₁ ++ s₂) ++ s') k
    ... | just _ = tt
    ... | nothing
      with match r ((s₁ ++ s₂) ++ s') ((r ⁺ˢ) ∷ k)
         | match-completeness r ((s₁ ++ s₂) ++ s') ((r ⁺ˢ) ∷ k)
             (cons s₁ (s₂ ++ s') (append-assoc s₁ s₂ s') y (cons s₂ s' refl inL inK))
    ... | nothing | ()
    ... | just _  | _ = tt

  -- Standard "accepts"

  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = is-just (match r s [])

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with match r s []
  acceptsˢ-soundness r .(p ++ []) m | just (cons p .[] refl inL emp) =
    eq-replace (sym (cong₂ _∈Lˢ_ {_}{_}{r}{r} (append-rh-[] p) refl)) inL
  acceptsˢ-soundness r s () | nothing

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r s inL = is-just-lemma (match-completeness r s [] (cons _ _ (append-rh-[] s) inL emp))

  acceptsˢ-intrinsic : (r : StdRegExp) → (s : List Char) → Maybe (s ∈Lˢ r)
  acceptsˢ-intrinsic r s = M.map ∈Lᵏ-empty-continuation (match r s [])

  acceptsˢ-intrinsic-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → isJust (acceptsˢ-intrinsic r s)
  acceptsˢ-intrinsic-completeness r s inL = is-just-preserve (match-completeness r s [] (cons s [] (append-rh-[] s) inL emp))

  {- Efficient overall matcher.
   These functions can be found in the OverallMatcher module
   but efficiency is sacrificed for generalization, because
   _acceptsˢ_ and _acceptsˢ-soundness are run twice, however
   those two are the same thing for the intrinsic matcher.
   Hence, we should run it only once. The functions below are efficient.
  -}

  accepts-intrinsic : (r : RegExp) → (s : List Char) → Maybe (s ∈L r)
  accepts-intrinsic r s with δ' r
  accepts-intrinsic r [] | inj₁ x = just x
  accepts-intrinsic r s | _ = Data.Maybe.map (∈L-soundness s r ∘ inj₂) (acceptsˢ-intrinsic (standardize r) s)

  exec : RegExp → String.String → Maybe (List String.String)
  exec r s = Data.Maybe.map (λ inL → Data.List.map String.fromList (extract {r}{xs} inL)) (accepts-intrinsic r xs)
    where xs = String.toList s
