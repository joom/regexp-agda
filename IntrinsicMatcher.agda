open import Definitions
open import Lemmas

module IntrinsicMatcher where

  open import Category.Monad
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
  open import Relation.Binary.PropositionalEquality
  import Agda.Primitive

  -- Using groups

  open RawMonadZero {Agda.Primitive.lzero} Data.Maybe.monadZero renaming (∅ to fail)

  try_within_handle_ : ∀ {l1 l2} {a : Set l1} {b : Set l2} → Maybe a → (a → Maybe b) → Maybe b → Maybe b
  try x within y handle z = maybe′ y z x

  mutual
    intrinsic-helper : (k : List StdRegExp) → (s : List Char) → Maybe (s ∈Lᵏ k)
    intrinsic-helper [] [] = return refl
    intrinsic-helper [] (x ∷ s) = fail
    intrinsic-helper (r ∷ rs) s = intrinsic r s rs

    -- Doing the matching and soundness proof at the same time.
    intrinsic : (r : StdRegExp)
              → (s : List Char)
              → (k : List StdRegExp)
              → Maybe (Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
    intrinsic ∅ˢ s k = fail
    intrinsic (Litˢ c) [] k = fail
    intrinsic (Litˢ c) (x ∷ xs) k = (decToMaybe (x Data.Char.≟ c)) >>=
                                    (λ p → (intrinsic-helper k xs) >>= (λ pf → return (((c ∷ [] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf))))
    intrinsic (r₁ ·ˢ r₂) s k = (intrinsic r₁ s (r₂ ∷ k)) >>= (λ { ((xs , ys) , eq , inL , ((as , bs) , eq' , inL' , rest)) → return ((xs ++ as , bs) , replace-right xs ys as bs s eq' eq , ((xs , as) , refl , inL , inL') , rest) })
    intrinsic (r₁ ⊕ˢ r₂) s k = try (intrinsic r₁ s k)
        within (λ {((p , s' ) , eq , inL , rest) → return ((p , s') , eq , inj₁ inL , rest)})
        handle ((intrinsic r₂ s k) >>= (λ { (_ , eq , inL , rest) → return (_ , eq , inj₂ inL , rest) }))
    intrinsic (r ⁺ˢ) s k = try (intrinsic r s k)
        within (λ {((p , s') , eq , inL , rest) → return ((p , s') , eq , S+ {p}{r} inL , rest) })
        handle ((intrinsic r s ((r ⁺ˢ) ∷ k)) >>= (λ { ((xs , ys) , eq , inL , ((as , bs) , eq' , inL' , rest)) → return ((xs ++ as , bs) , replace-right xs ys as bs s eq' eq , C+ {xs ++ as}{xs}{as} refl inL inL' , rest) }))

  mutual
    intrinsic-helper-some : (k : List StdRegExp) → (s : List Char) → (s ∈Lᵏ k) → isJust (intrinsic-helper k s)
    intrinsic-helper-some [] .[] refl = tt
    intrinsic-helper-some (r ∷ rs) s pf = intrinsic-completeness r s rs pf

    intrinsic-completeness : (r : StdRegExp)
                            → (s : List Char)
                            → (k : List StdRegExp)
                            → Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k})
                            → isJust (intrinsic r s k )
    intrinsic-completeness ∅ˢ _ _ (_ , _ , () , _)
    intrinsic-completeness (Litˢ x) .(x ∷ xs) k ((.(x ∷ []) , xs) , refl , refl , rest) with x Data.Char.≟ x
    ... | no q = ⊥-elim (q refl)
    ... | yes p with intrinsic-helper k xs | intrinsic-helper-some k xs rest
    ...            | just _  | tt = tt
    ...            | nothing | ()
    intrinsic-completeness (r₁ ·ˢ r₂) s' k ((xs , ys) , eq , ((as , bs) , eq' , inL' , rest') , rest)
      with intrinsic r₁ s' (r₂ ∷ k) | intrinsic-completeness r₁ s' (r₂ ∷ k) ((as , bs ++ ys) , replace-left as bs xs ys s' eq' eq , inL' , (bs , ys) , refl , rest' , rest)
    ... | nothing | ()
    ... | just _  | tt = tt
    intrinsic-completeness (r₁ ⊕ˢ r₂) s k ((xs , ys) , eq , inj₁ p , rest)
      with intrinsic r₁ s k | intrinsic-completeness r₁ s k (((xs , ys) , eq , p , rest))
    ... | nothing | ()
    ... | just _  | _ = tt
    intrinsic-completeness (r₁ ⊕ˢ r₂) s k ((xs , ys) , eq , inj₂ q , rest) with intrinsic r₁ s k
    ... | just pf = tt
    ... | nothing with intrinsic r₂ s k | intrinsic-completeness r₂ s k (((xs , ys) , eq , q , rest))
    ...           | nothing | ()
    ...           | just _  | _ = tt
    intrinsic-completeness (r ⁺ˢ) s k ((xs , ys) , eq , S+ x , rest)
      with intrinsic r s k | intrinsic-completeness r s k ((xs , ys) , eq , x , rest)
    ... | nothing | ()
    ... | just _  | _ = tt
    intrinsic-completeness (r ⁺ˢ) s k ((xs , ys) , eq , C+ x y inL , rest) with intrinsic r s k
    ... | just _ = tt
    intrinsic-completeness (r ⁺ˢ) .((s₁ ++ s₂) ++ ys) k ((._ , ys) , refl , C+ {._}{s₁}{s₂} refl y inL , rest) | nothing
      with intrinsic r ((s₁ ++ s₂) ++ ys) ((r ⁺ˢ) ∷ k) | intrinsic-completeness r ((s₁ ++ s₂) ++ ys) ((r ⁺ˢ) ∷ k) (_ , append-assoc s₁ s₂ ys , y , (_ , ys) , refl , inL , rest)
    ... | nothing | ()
    ... | just _  | _ = tt

  -- Standard "accepts"

  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = is-just (intrinsic r s [])

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with intrinsic r s []
  acceptsˢ-soundness r .(xs ++ []) m | just ((xs , .[]) , refl , inL , refl) = eq-replace (sym (cong₂ _∈Lˢ_ {_}{_}{r}{r} (append-rh-[] xs) refl)) inL
  acceptsˢ-soundness r s () | nothing

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r s inL = lemma (intrinsic-completeness r s [] ((s , []) , append-rh-[] s , inL , refl))
    where lemma : ∀ {l} → {x : Maybe l} → isJust x → is-just x ≡ true
          lemma {x = just x} m = refl
          lemma {x = nothing} ()