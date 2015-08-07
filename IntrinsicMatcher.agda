open import lib.Preliminaries
open import Definitions
open import Lemmas

module IntrinsicMatcher where

  open List
  open Maybe

  -- Using groups

  mutual
    intrinsic-helper : (k : List StdRegExp) → (s : List Char) → Maybe (s ∈Lᵏ k)
    intrinsic-helper [] [] = Some Refl
    intrinsic-helper [] (x :: s) = None
    intrinsic-helper (r :: rs) s = intrinsic r s rs

    -- Doing the matching and soundness proof at the same time.
    intrinsic : (r : StdRegExp)
              → (s : List Char)
              → (k : List StdRegExp)
              → Maybe (Σ (λ { (p , s') → (p ++ s' == s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
    intrinsic ∅ˢ s k = None
    intrinsic (Litˢ c) [] k = None
    intrinsic (Litˢ c) (x :: xs) k with Char.equal x c
    ... | Inr q = None
    intrinsic (Litˢ c) (x :: xs) k | Inl p with intrinsic-helper k xs
    ... | None = None
    ... | Some pf = Some (((c :: [] , xs) , ap (λ x → x :: xs) (! p) , Refl , pf))
    intrinsic (r₁ ·ˢ r₂) s k with intrinsic r₁ s (r₂ :: k)
    ... | None = None
    intrinsic (r₁ ·ˢ r₂) .(p ++ as ++ bs) k | Some ((p , .(as ++ bs)) , Refl , inL , (as , bs) , Refl , inL' , inLK) =
          Some ((p ++ as , bs) , ! (append-assoc p as bs) , ((p , as) , Refl , inL , inL') , inLK)
    intrinsic (r₁ ⊕ˢ r₂) s k with intrinsic r₁ s k
    intrinsic (r₁ ⊕ˢ r₂) s k | Some ((p , s' ) , eq , inL , oth) = Some ((p , s') , (eq , ((Inl inL) , oth)))
    intrinsic (r₁ ⊕ˢ r₂) s k | None with intrinsic r₂ s k
    intrinsic (r₁ ⊕ˢ r₂) s k | None | Some ((p , s') , eq , inL , oth) = Some ((p , s') , (eq , ((Inr inL) , oth)))
    intrinsic (r₁ ⊕ˢ r₂) s k | None | None = None
    intrinsic (r ⁺ˢ) s k with intrinsic r s k
    ... | Some ((p , s') , eq , inL , rest) = Some (((p , s') , eq , S+ {p}{r} inL , rest))
    ... | None with intrinsic r s ((r ⁺ˢ) :: k)
    ...           | None = None
    intrinsic (r ⁺ˢ) .(p ++ as ++ bs) k | None | Some ((p , .(as ++ bs)) , Refl , inL , (as , bs) , Refl , inL' , inLK) =
          Some (((p ++ as , bs) , ! (append-assoc p as bs) , C+ {p ++ as}{p}{as}{r} Refl inL inL' , inLK))
    intrinsic (Gˢ r) s k = intrinsic r s k

  intrinsic-completeness : (r : StdRegExp)
                         → (s : List Char)
                         → (k : List StdRegExp)
                         → Σ (λ { (p , s') → (p ++ s' == s) × (p ∈Lˢ r) × s' ∈Lᵏ k})
                         → isSome (intrinsic r s k )
  intrinsic-completeness ∅ˢ _ _ (_ , _ , () , _)
  intrinsic-completeness (Litˢ x) .(x :: xs) k ((.(x :: []) , xs) , Refl , Refl , rest) with Char.equal x x
  ... | Inr q = abort (q Refl)
  ... | Inl p = {!!}
  intrinsic-completeness (r₁ ·ˢ r₂) s k ((p , s') , eq , inL , rest) with intrinsic r₁ s (r₂ :: k)
  intrinsic-completeness (r₁ ·ˢ r₂) .(p ++ s') k ((p , s') , Refl , ((as , bs) , a , b , c) , rest) | None = {!!}
  ... | Some pf = {!!}
  intrinsic-completeness (r₁ ⊕ˢ r₂) s k pf = {!!}
  intrinsic-completeness (r ⁺ˢ) s k pf = {!!}
  intrinsic-completeness (Gˢ r) s k pf = intrinsic-completeness r s k pf

  extract : {r : RegExp} → {xs : List Char} → xs ∈L r → List (List Char)
  extract {∅} ()
  extract {ε} Refl = []
  extract {Lit x} Refl = []
  extract {r₁ · r₂}{xs} ((as , bs) , a , b , c) = extract {r₁}{as} b ++ extract {r₂}{bs} c
  extract {r₁ ⊕ r₂}{xs} (Inl x) = extract {r₁}{xs} x
  extract {r₁ ⊕ r₂}{xs} (Inr x) = extract {r₂}{xs} x
  extract {r *} (Ex Refl) = []
  extract {r *} (Cx {s}{s₁}{s₂} x x₁ inL) = extract {r}{s₁} x₁ ++ extract {r *}{s₂} inL
  extract {G r}{xs} inL = xs :: extract {r}{xs} inL

  inL-intrinsic : (r : RegExp)
                → (s : String.String)
                → Maybe ((String.toList s) ∈L r)
  inL-intrinsic r s with String.toList s | δ' r
  ... | [] | Inl x = Some x
  ... | l | d with intrinsic (standardize r) l []
  ...            | None = None
  inL-intrinsic r s | .(xs ++ []) | d | Some ((xs , .[]) , Refl , inL , Refl) =
          Some (eq-replace (! (ap2 {_}{_}{_}{_}{_}{_}{_}{_}{r}{r} _∈L_ (append-rh-[] xs) Refl)) (∈L-soundness xs r (Inr inL)))
    where eq-replace : {a b : Set} → a == b → a → b
          eq-replace Refl x = x

  exec : RegExp → String.String → Maybe (List String.String)
  exec r s with inL-intrinsic r s
  ... | None = None
  ... | Some inL = Some (map String.fromList (extract {r}{String.toList s} inL))

  -- Example

  alphanumeric : RegExp
  alphanumeric = foldl _⊕_ ∅ (map Lit (String.toList "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"))

  e-mail : RegExp
  e-mail = G (alphanumeric *) · Lit '@' · G (alphanumeric *) · Lit '.' · G (alphanumeric *)

  ex1 : Maybe (List String.String)
  ex1 = exec (G ((Lit 'a') *) · G ((Lit 'b') *)) "aaaabbb"

  ex2 : Maybe (List String.String)
  ex2 = exec e-mail "jdoe@wesleyan.edu"
