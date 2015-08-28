open import Definitions
open import Lemmas
open import OverallMatcher

module IntrinsicDefun where

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

  -- open RawMonadZero {Agda.Primitive.lzero} Data.Maybe.monadZero renaming (∅ to fail)
  open RawMonadPlus {Agda.Primitive.lzero} Data.Maybe.monadPlus renaming (∅ to fail)

  change-∈L : {a b d : List Char → Set} {c : List Char → List Char → Set}
            → (∀ {s} → a s → b s)
            → (Σ (List Char × List Char) (λ {(p , s') → (c p s') × (a p) × (d s')}))
            → Maybe (Σ (List Char × List Char) (λ {(p , s') → (c p s') × (b p) × (d s')}))
  change-∈L f = λ {(x , eq , inL , rest) → return (x , eq , f inL , rest)}

  collect-left : ∀ {r₁ r₂ s k} {C : List Char → List Char → Set}
               → (f : ∀ {xs as bs} → xs ∈Lˢ r₁ → as ∈Lˢ r₂ → C (xs ++ as) bs)
               → Σ _ (λ { (xs , ys) → (xs ++ ys ≡ s) × xs ∈Lˢ r₁ × Σ (List Char × List Char) (λ {(as , bs) → (as ++ bs ≡ ys) × as ∈Lˢ r₂ × bs ∈Lᵏ k})})
               → Maybe (Σ _ (λ { (p , s') → (p ++ s' ≡ s) × C p s' × s' ∈Lᵏ k}))
  collect-left {_}{_}{s} f = λ {((xs , ys) , eq , inL , (as , bs) , eq' , inL' , rest) → return ((xs ++ as , bs) , replace-right xs ys as bs s eq' eq , f inL inL' , rest )}

  mutual
    intrinsic-helper : (k : List StdRegExp) → (s : List Char) → Maybe (s ∈Lᵏ k)
    intrinsic-helper [] [] = return refl
    intrinsic-helper [] (x ∷ s) = fail
    intrinsic-helper (r ∷ rs) s = intrinsic r s rs

    -- Doing the matching and soundness proof at the same time.
    intrinsic : (r : StdRegExp)
              → (s : List Char)
              → (k : List StdRegExp)
              → Maybe (Σ (List Char × List Char) (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
    intrinsic ∅ˢ s k = fail
    intrinsic (Litˢ c) [] k = fail
    intrinsic (Litˢ c) (x ∷ xs) k =
        (isEqual x c) >>= (λ p → (intrinsic-helper k xs) >>= (λ pf → return (((c ∷ [] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf))))
    intrinsic (r₁ ·ˢ r₂) s k =
        (intrinsic r₁ s (r₂ ∷ k)) >>= collect-left (λ inL inL' → _ , refl , inL , inL')
    intrinsic (r₁ ⊕ˢ r₂) s k =
      ((intrinsic r₁ s k) >>= change-∈L inj₁) ∣ ((intrinsic r₂ s k) >>= change-∈L inj₂)
    intrinsic (r ⁺ˢ) s k =
      ((intrinsic r s k) >>= change-∈L S+) ∣ ((intrinsic r s ((r ⁺ˢ) ∷ k)) >>= collect-left (λ inL inL' → C+ refl inL inL'))

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

  {- Efficient overall matcher.
   These functions can be found in the OverallMatcher module
   but efficiency is sacrificed for generalization, because
   _acceptsˢ_ and _acceptsˢ-soundness are run twice, however
   those two are the same thing for the intrinsic matcher.
   Hence, we should run it only once. The functions below are efficient.
  -}

  inL-intrinsic : (r : RegExp)
                → (s : String.String)
                → Maybe ((String.toList s) ∈L r)
  inL-intrinsic r s with String.toList s | δ' r
  ... | [] | inj₁ x = just x
  ... | l | d with intrinsic (standardize r) l []
  ...            | nothing = nothing
  inL-intrinsic r s | .(xs ++ []) | d | just ((xs , .[]) , refl , inL , refl) =
    just ( eq-replace (sym (cong₂ _∈L_ {_}{_}{r}{r} (append-rh-[] xs) refl)) (∈L-soundness xs r (inj₂ inL)))

  exec : RegExp → String.String → Maybe (List String.String)
  exec r s = Data.Maybe.map (λ inL → Data.List.map String.fromList (extract {r}{String.toList s} inL)) (inL-intrinsic r s)
