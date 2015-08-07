open import lib.Preliminaries
open import Definitions
open import Lemmas

module IntrinsicMatcher where

  open List
  open Maybe

  -- Using groups

  mutual
    intrinsic-helper : (k : List StdRegExp) → (s : List Char) → (perm : RecursionPermission s) → Maybe (s ∈Lᵏ k)
    intrinsic-helper [] [] perm = Some Refl
    intrinsic-helper [] (x :: s) perm = None
    intrinsic-helper (r :: rs) s perm = intrinsic r s rs perm

    -- Doing the matching and soundness proof at the same time.
    intrinsic : (r : StdRegExp)
              → (s : List Char)
              → (k : List StdRegExp)
              → (perm : RecursionPermission s)
              → Maybe (Σ {_}{_}{List Char × Σ (λ s' → Suffix s' s)} (λ { (p , s' , sf) → (p ++ s' == s) × (p ∈Lˢ r) × s' ∈Lᵏ k}))
    intrinsic ∅ˢ s k perm = None
    intrinsic (Litˢ c) [] k perm = None
    intrinsic (Litˢ c) (x :: xs) k perm with Char.equal x c
    ... | Inr q = None
    intrinsic (Litˢ c) (x :: xs) k (CanRec f) | Inl p with intrinsic-helper k xs (f xs Stop)
    ... | None = None
    ... | Some pf = Some (((c :: [] , xs , Stop) , ap (λ x → x :: xs) (! p) , Refl , pf))
    intrinsic (r₁ ·ˢ r₂) s k perm with intrinsic r₁ s (r₂ :: k) perm
    ... | None = None
    intrinsic (r₁ ·ˢ r₂) .(p ++ as ++ bs) k perm | Some ((p , .(as ++ bs) , sf) , Refl , inL , (as , bs , sf') , Refl , inL' , inLK) =
          Some ((p ++ as , bs , suffix-trans (append-suffix2 {as}{bs}{r₂} inL') (append-suffix2 {p}{as ++ bs}{r₁} inL)) , ! (append-assoc p as bs) , ((p , as) , Refl , inL , inL') , inLK)
    intrinsic (r₁ ⊕ˢ r₂) s k perm with intrinsic r₁ s k perm
    intrinsic (r₁ ⊕ˢ r₂) s k perm | Some ((p , s' , sf) , eq , inL , oth) = Some ((p , (s' , sf)) , (eq , ((Inl inL) , oth)))
    intrinsic (r₁ ⊕ˢ r₂) s k perm | None with intrinsic r₂ s k perm
    intrinsic (r₁ ⊕ˢ r₂) s k perm | None | Some ((p , s' , sf) , eq , inL , oth) = Some ((p , (s' , sf)) , (eq , ((Inr inL) , oth)))
    intrinsic (r₁ ⊕ˢ r₂) s k perm | None | None = None
    intrinsic (r ⁺ˢ) s k perm with intrinsic r s k perm
    ... | Some ((p , s' , sf) , eq , inL , rest) = Some (((p , s' , sf) , eq , S+ {p}{r} inL , rest))
    ... | None with intrinsic r s ((r ⁺ˢ) :: k) perm
    ...           | None = None
    intrinsic (r ⁺ˢ) .(p ++ as ++ bs) k perm | None | Some ((p , .(as ++ bs) , sf) , Refl , inL , (as , bs , sf') , Refl , inL' , inLK) =
          Some (((p ++ as , bs , suffix-trans (append-suffix2⁺ {as}{bs}{r} inL') (append-suffix2 {p}{as ++ bs}{r} inL)) , ! (append-assoc p as bs) , C+ {p ++ as}{p}{as}{r} Refl inL inL' , inLK))
    intrinsic (Gˢ r) s k perm = intrinsic r s k perm

  intrinsic-completeness : (r : StdRegExp)
                         → (s : List Char)
                         → (k : List StdRegExp)
                         → (perm : RecursionPermission s)
                         → Σ {_}{_}{List Char × Σ (λ s' → Suffix s' s)} (λ { (p , s' , sf) → (p ++ s' == s) × (p ∈Lˢ r) × s' ∈Lᵏ k})
                         → isSome (intrinsic r s k perm)
  intrinsic-completeness ∅ˢ _ _ _ (_ , _ , () , _)
  intrinsic-completeness (Litˢ x) .(x :: xs) k perm ((.(x :: []) , xs , sf) , Refl , Refl , rest) with Char.equal x x
  ... | Inr q = abort (q Refl)
  intrinsic-completeness (Litˢ x) .(x :: [] ++ []) [] perm ((.(x :: []) , .[] , sf) , Refl , Refl , Refl) | Inl Refl = {!!}
  intrinsic-completeness (Litˢ x) .(x :: [] ++ p ++ s') (r :: rs) (CanRec f) ((.(x :: []) , .(p ++ s') , sf) , Refl , Refl , (p , s' , sf') , Refl , inL , inLK) | Inl Refl with intrinsic r (p ++ s') rs (f (p ++ s') Stop)
  ... | Some pf = <>
  intrinsic-completeness (Litˢ x) .(x :: [] ++ p ++ s') (r :: rs) (CanRec f) ((.(x :: []) , .(p ++ s') , sf) , Refl , Refl , (p , s' , sf') , Refl , inL , inLK) | Inl Refl | None = {!!}
  intrinsic-completeness (r₁ ·ˢ r₂) s k perm ((p , s' , sf) , eq , inL , rest) with intrinsic r₁ s (r₂ :: k) perm
  intrinsic-completeness (r₁ ·ˢ r₂) .(p ++ s') k perm ((p , s' , sf) , Refl , ((as , bs) , a , b , c) , rest) | None = {!!}
  ... | Some pf = {!!}
  intrinsic-completeness (r₁ ⊕ˢ r₂) s k perm pf = {!!}
  intrinsic-completeness (r ⁺ˢ) s k perm pf = {!!}
  intrinsic-completeness (Gˢ r) s k perm pf = intrinsic-completeness r s k perm pf


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
  ... | l | d with intrinsic (standardize r) l [] (well-founded l)
  ...            | None = None
  inL-intrinsic r s | .(xs ++ []) | d | Some ((xs , .[] , sf) , Refl , inL , Refl) =
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
