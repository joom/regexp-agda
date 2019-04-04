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

  change-∈L : {a b d : List Char → Set} {c : List Char → List Char → Set}
            → (∀ {s} → a s → b s)
            → (Σ (List Char × List Char) (λ {(p , s') → (c p s') × (a p) × (d s')}))
            → (Σ (List Char × List Char) (λ {(p , s') → (c p s') × (b p) × (d s')}))
  change-∈L f (x , eq , inL , rest) = (x , eq , f inL , rest)

  reassociate-left : ∀ {r₁ r₂ s k} {R : StdRegExp → StdRegExp → StdRegExp}
               → (f : ∀ {xs as} → xs ∈Lˢ r₁ → as ∈Lˢ r₂ → ((xs ++ as) ∈Lˢ R r₁ r₂))
               → Σ (List Char × List Char) (λ { (xs , ys) → (xs ++ ys ≡ s) × xs ∈Lˢ r₁ × Σ (List Char × List Char) (λ {(as , bs) → (as ++ bs ≡ ys) × as ∈Lˢ r₂ × bs ∈Lᵏ k})})
               → (Σ (List Char × List Char) (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ R r₁ r₂) × s' ∈Lᵏ k}))
  reassociate-left {_}{_}{s} f ((xs , ys) , eq , inL , (as , bs) , eq' , inL' , rest) =
    ((xs ++ as , bs) , replace-right xs ys as bs s eq' eq , f inL inL' , rest )

  mutual
    match-helper : (k : List StdRegExp) → (s : List Char) → Maybe (s ∈Lᵏ k)
    match-helper [] [] = return refl
    match-helper [] (x ∷ s) = fail
    match-helper (r ∷ rs) s = match r s rs

    -- Doing the matching and soundness proof at the same time.
    match : (r : StdRegExp)
          → (s : List Char)
          → (k : List StdRegExp)
          → Maybe (Σ (List Char × List Char) (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
    match ∅ˢ s k = fail
    match (Litˢ c) [] k = fail
    match (Litˢ c) (x ∷ xs) k =
        do eq ← is-equal x c
           pf ← match-helper k xs
           just ((([ c ] , xs) , cong (λ x → x ∷ xs) (sym eq) , refl , pf))
      -- case (x Data.Char.≟ c) of
      --   -- λ { (yes p) → Data.Maybe.map (λ pf → ((([ c ] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf))) (match-helper k xs)
      --   λ { (yes p) →
      --       do pf ← match-helper k xs
      --          just ((([ c ] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf))
      --     ; (no _) → fail
      --     }
    match (r₁ ·ˢ r₂) s k =
      Data.Maybe.map (reassociate-left {R = _·ˢ_} (λ inL inL' → _ , refl , inL , inL')) (match r₁ s (r₂ ∷ k))
    match (r₁ ⊕ˢ r₂) s k =
      (Data.Maybe.map (change-∈L inj₁) (match r₁ s k)) ∣
      (Data.Maybe.map (change-∈L inj₂) (match r₂ s k))
    match (r ⁺ˢ) s k =
      (Data.Maybe.map (change-∈L S+) (match r s k)) ∣
      (Data.Maybe.map (reassociate-left {R = λ r _ → r ⁺ˢ} (λ inL inL' → C+ refl inL inL')) (match r s ((r ⁺ˢ) ∷ k)))

  mutual
    match-helper-some : (k : List StdRegExp) → (s : List Char) → (s ∈Lᵏ k) → isJust (match-helper k s)
    match-helper-some [] .[] refl = tt
    match-helper-some (r ∷ rs) s pf = match-completeness r s rs pf

    match-completeness : (r : StdRegExp)
                       → (s : List Char)
                       → (k : List StdRegExp)
                       → Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k})
                       → isJust (match r s k)
    match-completeness ∅ˢ _ _ (_ , _ , () , _)
    match-completeness (Litˢ x) .(x ∷ xs) k ((.(x ∷ []) , xs) , refl , refl , rest) with x Data.Char.≟ x
    ... | no q = ⊥-elim (q refl)
    ... | yes p with match-helper k xs | match-helper-some k xs rest
    ...            | just _  | tt = tt
    ...            | nothing | ()
    match-completeness (r₁ ·ˢ r₂) s' k ((xs , ys) , eq , ((as , bs) , eq' , inL' , rest') , rest)
      with match r₁ s' (r₂ ∷ k) | match-completeness r₁ s' (r₂ ∷ k) ((as , bs ++ ys) , replace-left as bs xs ys s' eq' eq , inL' , (bs , ys) , refl , rest' , rest)
    ... | nothing | ()
    ... | just _  | tt = tt
    match-completeness (r₁ ⊕ˢ r₂) s k ((xs , ys) , eq , inj₁ p , rest)
      with match r₁ s k | match-completeness r₁ s k (((xs , ys) , eq , p , rest))
    ... | nothing | ()
    ... | just _  | _ = tt
    match-completeness (r₁ ⊕ˢ r₂) s k ((xs , ys) , eq , inj₂ q , rest) with match r₁ s k
    ... | just pf = tt
    ... | nothing with match r₂ s k | match-completeness r₂ s k (((xs , ys) , eq , q , rest))
    ...           | nothing | ()
    ...           | just _  | _ = tt
    match-completeness (r ⁺ˢ) s k ((xs , ys) , eq , S+ x , rest)
      with match r s k | match-completeness r s k ((xs , ys) , eq , x , rest)
    ... | nothing | ()
    ... | just _  | _ = tt
    match-completeness (r ⁺ˢ) .((s₁ ++ s₂) ++ ys) k ((._ , ys) , refl , C+ {._}{s₁}{s₂} refl y inL , rest)
      with match r ((s₁ ++ s₂) ++ ys) k
    ... | just _ = tt
    ... | nothing
      with match r ((s₁ ++ s₂) ++ ys) ((r ⁺ˢ) ∷ k)
         | match-completeness r ((s₁ ++ s₂) ++ ys) ((r ⁺ˢ) ∷ k) (_ , append-assoc s₁ s₂ ys , y , (_ , ys) , refl , inL , rest)
    ... | nothing | ()
    ... | just _  | _ = tt

  -- Standard "accepts"

  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = is-just (match r s [])

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with match r s []
  acceptsˢ-soundness r .(xs ++ []) m | just ((xs , .[]) , refl , inL , refl) = eq-replace (sym (cong₂ _∈Lˢ_ {_}{_}{r}{r} (append-rh-[] xs) refl)) inL
  acceptsˢ-soundness r s () | nothing

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r s inL = is-just-lemma (match-completeness r s [] ((s , []) , append-rh-[] s , inL , refl))

  acceptsˢ-intrinsic : (r : StdRegExp) → (s : List Char) → Maybe (s ∈Lˢ r)
  acceptsˢ-intrinsic r s = Data.Maybe.map ∈Lˢ-empty-continuation (match r s [])

  acceptsˢ-intrinsic-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → isJust (acceptsˢ-intrinsic r s)
  acceptsˢ-intrinsic-completeness r s inL = is-just-preserve (match-completeness r s [] ((s , []) , append-rh-[] s , inL , refl))

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
