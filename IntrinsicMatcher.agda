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

  -- Using groups

  mutual
    intrinsic-helper : (k : List StdRegExp) → (s : List Char) → Maybe (s ∈Lᵏ k)
    intrinsic-helper [] [] = just refl
    intrinsic-helper [] (x ∷ s) = nothing
    intrinsic-helper (r ∷ rs) s = intrinsic r s rs

    -- Doing the matching and soundness proof at the same time.
    intrinsic : (r : StdRegExp)
              → (s : List Char)
              → (k : List StdRegExp)
              → Maybe (Σ _ (λ { (p , s') → (p ++ s' ≡ s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
    intrinsic ∅ˢ s k = nothing
    intrinsic (Litˢ c) [] k = nothing
    intrinsic (Litˢ c) (x ∷ xs) k = (decToMaybe (x Data.Char.≟ c)) >>= (λ p → Data.Maybe.map (λ pf → (((c ∷ [] , xs) , cong (λ x → x ∷ xs) (sym p) , refl , pf))) (intrinsic-helper k xs)) where open RawMonad Data.Maybe.monad
    intrinsic (r₁ ·ˢ r₂) s k = Data.Maybe.map (λ { ((xs , ys) , eq , inL , ((as , bs) , eq' , inL' , rest)) → ((xs ++ as , bs) , replace-right xs ys as bs s eq' eq , ((xs , as) , refl , inL , inL') , rest) }) (intrinsic r₁ s (r₂ ∷ k))
    intrinsic (r₁ ⊕ˢ r₂) s k = maybe′ (λ {((p , s' ) , eq , inL , rest) → just ((p , s') , eq , inj₁ inL , rest)}) (Data.Maybe.map (λ { ((p , s') , eq , inL , rest) →  ((p , s') , eq , inj₂ inL , rest) }) (intrinsic r₂ s k)) (intrinsic r₁ s k)
    intrinsic (r ⁺ˢ) s k = maybe′ (λ {((p , s') , eq , inL , rest) → just ((p , s') , eq , S+ {p}{r} inL , rest)  }) (Data.Maybe.map (λ { ((xs , ys) , eq , inL , ((as , bs) , eq' , inL' , rest)) → ((xs ++ as , bs) , replace-right xs ys as bs s eq' eq , C+ {xs ++ as}{xs}{as} refl inL inL' , rest) }) (intrinsic r s ((r ⁺ˢ) ∷ k))) (intrinsic r s k)

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

  acceptsˢ-correct : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-correct r s m with intrinsic r s []
  acceptsˢ-correct r .(xs ++ []) m | just ((xs , .[]) , refl , inL , refl) = eq-replace (sym (cong₂ _∈Lˢ_ {_}{_}{r}{r} (append-rh-[] xs) refl)) inL
  acceptsˢ-correct r s () | nothing

  -- Non standard stuff

  extract : {r : RegExp} → {xs : List Char} → xs ∈L r → List (List Char)
  extract {∅} ()
  extract {ε} refl = []
  extract {Lit x} refl = []
  extract {r₁ · r₂}{xs} ((as , bs) , a , b , c) = extract {r₁}{as} b ++ extract {r₂}{bs} c
  extract {r₁ ⊕ r₂}{xs} (inj₁ x) = extract {r₁}{xs} x
  extract {r₁ ⊕ r₂}{xs} (inj₂ x) = extract {r₂}{xs} x
  extract {r *} (Ex refl) = []
  extract {r *} (Cx {s}{s₁}{s₂} x x₁ inL) = extract {r}{s₁} x₁ ++ extract {r *}{s₂} inL
  extract {G r}{xs} inL = xs ∷ extract {r}{xs} inL

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

  -- Example

  alphanumeric : RegExp
  alphanumeric = foldl _⊕_ ∅ (Data.List.map Lit (String.toList "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"))

  e-mail : RegExp
  e-mail = G (alphanumeric *) · Lit '@' · G (alphanumeric *) · Lit '.' · G (alphanumeric *)

  ex1 : Maybe (List String.String)
  ex1 = exec (G ((Lit 'a') *) · G ((Lit 'b') *)) "aaaabbb"

  ex2 : Maybe (List String.String)
  ex2 = exec e-mail "jdoe@wesleyan.edu"

  ex3 : Maybe (List String.String)
  ex3 = exec (G (Lit 'a' *) · G (Lit 'a' *)) "aaaa"
