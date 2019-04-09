open import Definitions
open import Lemmas

module ExtrinsicHOF where

  open import Data.Char
  open import Data.Bool
  open import Data.Empty
  open import Data.List
  open import Data.Maybe
  open import Data.Product
  open Σ
  import Data.String as String
  open import Data.Sum
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Binary.PropositionalEquality

  -- Bad matching function
  -- bad-match : StdRegExp → List Char → (List Char → Bool) → Bool
  -- bad-match ∅ˢ s k = false
  -- bad-match (Litˢ _) [] k = false
  -- bad-match (Litˢ c) (x ∷ xs) k = (x == c) ∧ (k xs)
  -- bad-match (r₁ ·ˢ r₂) s k = bad-match r₁ s (λ s' → bad-match r₂ s' (λ s'' → k s''))
  -- bad-match (r₁ ⊕ˢ r₂) s k = (bad-match r₁ s k) ∨ (bad-match r₂ s k)
  -- bad-match (r ⁺ˢ) s k = (bad-match r s k) ∨ bad-match r s (λ s' → {! bad-match (r ⁺ˢ) s' (λ s'' → k s'') !})

  -- Matching algorithm
  match : StdRegExp → (s : List Char) → ((s' : List Char) → Suffix s' s → Bool) → RecursionPermission s → Bool
  match ∅ˢ s k _ = false
  match (Litˢ _) [] _ _ = false
  match (Litˢ c) (x ∷ xs) k _ = (x == c) ∧ (k xs Stop)
  match (r₁ ·ˢ r₂) s k (CanRec f) = match r₁ s (λ s' sf → match r₂ s' (λ s'' sf' → k s'' (suffix-trans sf' sf)) (f s' sf)) (CanRec f)
  match (r₁ ⊕ˢ r₂) s k perm = (match r₁ s k perm) ∨ (match r₂ s k perm)
  match (r ⁺ˢ) s k (CanRec f) = (match r s k (CanRec f)) ∨ (match r s (λ s' sf → match (r ⁺ˢ) s' (λ s'' sf' → k s'' (suffix-trans sf' sf)) (f s' sf)) (CanRec f))

  -- Proofs

  -- data _∈L_✂_  (s : List Char) (r : StdRegExp) (k : (s' : List Char) → Suffix s' s → Bool) : Set where
  --   sound : (p s' : List Char) (sf : Suffix s' s) → (p ++ s' ≡ s) → (p ∈Lˢ r) → (k s' sf ≡ true) → s ∈L r ✂ k

  {- Show that if match r s k perm is true, then there is a split of s, namely s₁ s₂, such that s₁ ∈L r and k s₂ is true. -}
  match-soundness : (r : StdRegExp)
                  → (s : List Char)
                  → (k : (s' : List Char) → Suffix s' s → Bool)
                  → (perm : RecursionPermission s)
                  → match r s k perm ≡ true
                  → Σ (List Char × (Σ _ (λ s' → Suffix s' s))) (λ { (p , (s' , sf)) → (p ++ s' ≡ s) × (p ∈Lˢ r) × (k s' sf ≡ true)})
  match-soundness ∅ˢ s k perm ()
  match-soundness (Litˢ c) [] k perm ()
  match-soundness (Litˢ c) (y ∷ ys) k perm m with y Data.Char.≟ c
  match-soundness (Litˢ c) (.c ∷ ys) k perm m | yes refl = ((c ∷ [] , ys , Stop) , refl , ∈ˢLit , m)
  match-soundness (Litˢ c) (y ∷ ys) k perm () | no ¬p
  match-soundness (r₁ ·ˢ r₂) s k (CanRec f) m with match-soundness r₁ s (λ s' sf → match r₂ s' (λ s'' sf' → k s'' (suffix-trans sf' sf)) (f s' sf)) (CanRec f) m
  match-soundness (r₁ ·ˢ r₂) s k (CanRec f) m | (xs , ys , r) , a , b , c
    with match-soundness r₂ ys (λ s' sf → k s' (suffix-trans sf r)) (f ys r) c
  match-soundness (r₁ ·ˢ r₂) .(xs ++ as ++ bs) k (CanRec f) m | (xs , .(as ++ bs) , r) , refl , b , c | (as , bs , r1) , refl , b1 , c1 =
    ((xs ++ as) , (bs , suffix-trans r1 r)) , ((sym (append-assoc xs as bs)) , (∈ˢ· refl b b1 , c1))
  match-soundness (r₁ ⊕ˢ r₂) s k perm m with or-eq {match r₁ s k perm} {match r₂ s k perm} m
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | inj₁ x with match-soundness r₁ s k perm x
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | inj₁ x | (p , q , r) , a , b , c = (p , (q , r)) , (a , (∈ˢ⊕₁ b , c))
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | inj₂ x with match-soundness r₂ s k perm x
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | inj₂ x | (p , q , r) , a , b , c = (p , (q , r)) , (a , (∈ˢ⊕₂ b , c))
  match-soundness (r ⁺ˢ) s k (CanRec f) m
    with or-eq {match r s k (CanRec f)} { match r s (λ s' sf → match (r ⁺ˢ) s' (λ s'' sf' → k s'' (suffix-trans sf' sf)) (f s' sf)) (CanRec f)} m
  match-soundness (r ⁺ˢ) s k (CanRec f) m | inj₁ x with match-soundness r s k (CanRec f) x
  match-soundness (r ⁺ˢ) s k (CanRec f) m | inj₁ x | (xs , ys , sf) , a , fst , snd = (xs , (ys , sf)) , (a , (∈ˢS+ fst , snd))
  match-soundness (r ⁺ˢ) s k (CanRec f) m | inj₂ x with match-soundness r s (λ s' sf → match (r ⁺ˢ) s' _ (f s' sf)) (CanRec f) x
  match-soundness (r ⁺ˢ) s k (CanRec f) m | inj₂ x | (xs , (ys , sf)) , eq , xs∈rS , d with match-soundness (r ⁺ˢ) ys (λ s' sf' → k s' (suffix-trans sf' sf)) (f ys sf) d
  match-soundness (r ⁺ˢ) s k (CanRec f) m | inj₂ x | (xs , (ys , sf)) , eq , xs∈rS , d | (ys' , ys'' , sf') , eq1 , ys'∈rP , d1 with sym (append-assoc xs ys' ys'')
  match-soundness (r ⁺ˢ) .(xs ++ ys' ++ ys'') k (CanRec f) m | inj₂ x | (xs , .(ys' ++ ys'') , sf) , refl , xs∈rS , d | (ys' , ys'' , sf') , refl , ys'∈rP , d1 | app =
    (xs ++ ys' , (ys'' , suffix-trans sf' sf)) , (app , (∈ˢC+ refl xs∈rS ys'∈rP , d1))

  {- Show that if there is a split of s, namely s₁ s₂, such that s₁ ∈L r and k s₂ is true, then match r s k perm is true. -}
  match-completeness : (r : StdRegExp)
                     → (s : List Char)
                     → (k : (s' : List Char) → Suffix s' s → Bool)
                     → (perm : RecursionPermission s)
                     → Σ (List Char × (Σ _ (λ s' → Suffix s' s))) (λ { (p , (s' , sf)) → (p ++ s' ≡ s) × (p ∈Lˢ r) × (k s' sf ≡ true)})
                     → match r s k perm ≡ true
  match-completeness ∅ˢ _ _ _ (_ , _ , () , _)
  match-completeness (Litˢ x) .(x ∷ ys) k perm ((.(x ∷ []) , ys , sf) , refl , ∈ˢLit , d) with x == x | same-char x
  match-completeness (Litˢ x) .((x ∷ []) ++ ys) k perm ((.(x ∷ []) , ys , sf) , refl , ∈ˢLit , d) | false | ()
  match-completeness (Litˢ x) .((x ∷ []) ++ ys) k perm ((.(x ∷ []) , ys , sf) , refl , ∈ˢLit , d) | true | _ = subst (λ (h : Suffix ys (x ∷ ys) ) → k ys h ≡ true) (suffix-unique sf Stop) d
  match-completeness (r₁ ·ˢ r₂) .(xs ++ ys) k (CanRec f) ((xs , ys , sf) , refl , ∈ˢ· {_}{ms}{ns} eq' inL inL' , pf) with eq' | append-assoc ms ns ys
  match-completeness (r₁ ·ˢ r₂) .((ms ++ ns) ++ ys) k (CanRec f) ((.(ms ++ ns) , ys , sf) , refl , ∈ˢ· {.(ms ++ ns)} {ms} {ns} eq' inL inL' , pf) | refl | b
    with assoc-append-suffix {ns ++ ys}{ms ++ ns ++ ys}{(ms ++ ns) ++ ys} b (append-suffix2 {ms} {ns ++ ys} {r₁} inL)
  ... | t with match-completeness r₂ (ns ++ ys) (λ s' sf' → k s' (suffix-trans sf' t)) (f (ns ++ ys) t) ((ns , ys , append-suffix2 {ns} {ys} {r₂} inL') , refl , inL' , trans (cong (k ys) (suffix-unique _ _)) pf)
  ... | x = match-completeness r₁ ((ms ++ ns) ++ ys) _ (CanRec f) (((ms , ns ++ ys , t) , b  , inL , x))
  match-completeness (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , b , ∈ˢ⊕₁ c , d) = either-if (inj₁ (match-completeness r₁ s k perm ((xs , ys) , b , c , d) ))
  match-completeness (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , b , ∈ˢ⊕₂ c , d) = either-if (inj₂ (match-completeness r₂ s k perm ((xs , ys) , b , c , d)))
  match-completeness (r ⁺ˢ) s k (CanRec f) ((xs , ys , sf) , b , ∈ˢS+ x , d) = either-if (inj₁ (match-completeness r s k (CanRec f) ((xs , (ys , sf)) , b , x , d)))
  match-completeness (r ⁺ˢ) s k (CanRec f) ((._ , ys , sf) , b , ∈ˢC+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c , d) with match r s k (CanRec f)
  match-completeness (r ⁺ˢ) s k (CanRec f) ((._ , ys , sf) , b , ∈ˢC+ refl q c , d) | true = refl
  match-completeness (r ⁺ˢ) s k (CanRec f) ((._ , ys , sf) , b , ∈ˢC+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c , d) | false
    with assoc-append-suffix {s₂ ++ ys}{(s₁ ++ s₂) ++ ys}{s} b (assoc-append-suffix (append-assoc s₁ s₂ ys) (append-suffix2 {s₁}{s₂ ++ ys}{r} q))
  ... | t with match-completeness (r ⁺ˢ) (s₂ ++ ys) (λ s' sf' → k s' (suffix-trans sf' t)) (f (s₂ ++ ys) t) ((s₂ , ys , append-suffix2 c) , refl , c , trans (cong (k ys) (suffix-unique _ _)) d)
  match-completeness (r ⁺ˢ) ._ k (CanRec f) ((._ , ys , sf) , refl , ∈ˢC+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c , d) | false | t | x =
    match-completeness r ((s₁ ++ s₂) ++ ys) _ (CanRec f) ((s₁ , s₂ ++ ys , t) , append-assoc s₁ s₂ ys , q , x)

  -- Standard "accepts"
  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = match r s (λ s sf → null s) (well-founded s)

  acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-soundness r s m with bool-eq (match r s (λ s sf → null s) (well-founded s))
  ... | inj₁ p with match-soundness r s (λ s sf → null s) (well-founded s) p
  acceptsˢ-soundness r .(xs ++ []) m | inj₁ p | (xs , [] , sf) , refl , inL , refl =
    eq-replace (sym (cong₂ _∈Lˢ_ {_}{_}{r}{r} (append-rh-[] xs) refl)) inL
  acceptsˢ-soundness r s m | inj₁ p | (xs , x ∷ ys , sf) , eq , inL , ()
  acceptsˢ-soundness r s m | inj₂ q with trans (sym m) q
  ... | ()

  acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true
  acceptsˢ-completeness r [] inL = ⊥-elim (non-empty inL)
  acceptsˢ-completeness r (x ∷ s) inL = match-completeness r (x ∷ s) (λ s sf → null s) (well-founded (x ∷ s)) ((x ∷ s , [] , suffix-[]-cons) , append-rh-[] (x ∷ s) , inL , refl)

  open import Matcher {_acceptsˢ_}{acceptsˢ-soundness}{acceptsˢ-completeness}
