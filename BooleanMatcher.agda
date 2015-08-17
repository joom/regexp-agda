open import Definitions
open import Lemmas

module BooleanMatcher where

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

  -- Matching algorithm
  match : StdRegExp → (s : List Char) → (Σ _ (λ s' → Suffix s' s) → Bool) → RecursionPermission s → Bool
  match ∅ˢ s k _ = false
  match (Litˢ _) [] _ _ = false
  match (Litˢ c) (x ∷ xs) k _ = (x == c) ∧ (k (xs , Stop))
  match (r₁ ·ˢ r₂) s k (CanRec f) = match r₁ s (λ { (s' , sf) → match r₂ s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)
  match (r₁ ⊕ˢ r₂) s k perm = (match r₁ s k perm) ∨ (match r₂ s k perm)
  match (r ⁺ˢ) s k (CanRec f) = (match r s k (CanRec f)) ∨ (match r s (λ { (s' , sf) → match (r ⁺ˢ) s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f))

  -- Proofs

  {- Show that if match r s k perm is true, then there is a split of s, namely s₁ s₂, such that s₁ ∈L r and k s₂ is true. -}
  match-soundness : (r : StdRegExp)
                  → (s : List Char)
                  → (k : Σ _ (λ s' → Suffix s' s) → Bool)
                  → (perm : RecursionPermission s)
                  → match r s k perm ≡ true
                  → Σ (List Char × (Σ _ (λ s' → Suffix s' s))) (λ { (p , (s' , sf)) → (p ++ s' ≡ s) × (p ∈Lˢ r) × (k (s' , sf) ≡ true)})
  match-soundness ∅ˢ s k perm ()
  match-soundness (Litˢ c) [] k perm ()
  match-soundness (Litˢ c) (y ∷ ys) k perm m with y Data.Char.≟ c
  match-soundness (Litˢ c) (.c ∷ ys) k perm m | yes refl = ((c ∷ [] , ys , Stop) , refl , refl , m)
  match-soundness (Litˢ c) (y ∷ ys) k perm () | no ¬p
  match-soundness (r₁ ·ˢ r₂) s k (CanRec f) m with match-soundness r₁ s (λ { (s' , sf) → match r₂ s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f) m
  match-soundness (r₁ ·ˢ r₂) s k (CanRec f) m | (xs , ys , r) , a , b , c
    with match-soundness r₂ ys (λ { (s' , sf) → k (s' , (suffix-trans sf r)) }) (f ys r) c
  match-soundness (r₁ ·ˢ r₂) .(xs ++ as ++ bs) k (CanRec f) m | (xs , .(as ++ bs) , r) , refl , b , c | (as , bs , r1) , refl , b1 , c1 = ((xs ++ as) , (bs , suffix-trans r1 r)) , ((sym (append-assoc xs as bs)) , (((xs , as) , (refl , (b , b1))) , c1))
  match-soundness (r₁ ⊕ˢ r₂) s k perm m with or-eq {match r₁ s k perm} {match r₂ s k perm} m
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | inj₁ x with match-soundness r₁ s k perm x
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | inj₁ x | (p , q , r) , a , b , c = (p , (q , r)) , (a , (inj₁ b , c))
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | inj₂ x with match-soundness r₂ s k perm x
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | inj₂ x | (p , q , r) , a , b , c = (p , (q , r)) , (a , (inj₂ b , c))
  --match-soundness (r ⁺ˢ) s k (CanRec f) m = {!!}
  match-soundness (r ⁺ˢ) s k (CanRec f) m with or-eq {match r s k (CanRec f)} { match r s (λ { (s' , sf) → match (r ⁺ˢ) s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)} m
  match-soundness (r ⁺ˢ) s k (CanRec f) m | inj₁ x with match-soundness r s k (CanRec f) x
  match-soundness (r ⁺ˢ) s k (CanRec f) m | inj₁ x | (xs , ys , sf) , a , fst , snd = (xs , (ys , sf)) , (a , (S+ fst , snd))
  match-soundness (r ⁺ˢ) s k (CanRec f) m | inj₂ x with match-soundness r s (λ { (s' , sf) → match (r ⁺ˢ) s' _ (f s' sf) }) (CanRec f) x
  match-soundness (r ⁺ˢ) s k (CanRec f) m | inj₂ x | (xs , (ys , sf)) , eq , xs∈rS , d with match-soundness (r ⁺ˢ) ys (λ { (s' , sf') → k (s' , suffix-trans sf' sf) } ) (f ys sf) d
  match-soundness (r ⁺ˢ) s k (CanRec f) m | inj₂ x | (xs , (ys , sf)) , eq , xs∈rS , d | (ys' , ys'' , sf') , eq1 , ys'∈rP , d1 with sym (append-assoc xs ys' ys'')
  match-soundness (r ⁺ˢ) .(xs ++ ys' ++ ys'') k (CanRec f) m | inj₂ x | (xs , .(ys' ++ ys'') , sf) , refl , xs∈rS , d | (ys' , ys'' , sf') , refl , ys'∈rP , d1 | app = (xs ++ ys' , (ys'' , suffix-trans sf' sf)) , (app , (C+ refl xs∈rS ys'∈rP , d1))

  {- Show that if there is a split of s, namely s₁ s₂, such that s₁ ∈L r and k s₂ is true, then match r s k perm is true. -}
  match-completeness : (r : StdRegExp)
                     → (s : List Char)
                     → (k : Σ _ (λ s' → Suffix s' s) → Bool)
                     → (perm : RecursionPermission s)
                     → Σ (List Char × (Σ _ (λ s' → Suffix s' s))) (λ { (p , (s' , sf)) → (p ++ s' ≡ s) × (p ∈Lˢ r) × (k (s' , sf) ≡ true)})
                     → match r s k perm ≡ true
  match-completeness ∅ˢ _ _ _ (_ , _ , c , _) = ⊥-elim c
  match-completeness (Litˢ x) s k perm ((xs , (ys , sf)) , b , c , d) with sym (singleton-append c b)
  match-completeness (Litˢ x) .(x ∷ ys) k perm ((xs , ys , sf) , b , c , d) | refl with x == x | same-char x
  match-completeness (Litˢ x) .(x ∷ ys) k perm ((xs , ys , sf) , b , c , d) | refl | true | refl = subst (λ (h : Suffix ys (x ∷ ys) ) → k (ys , h) ≡ true) (suffix-unique sf Stop) d
  match-completeness (Litˢ x) .(x ∷ ys) k perm ((xs , ys , sf) , b , c , d) | refl | false | ()
  match-completeness (r₁ ·ˢ r₂) s k perm ((xs , (ys , sf)) , b , ((ms , ns) , tot , ms∈r₁ , ns∈r₂) , d) with tot | b | append-assoc ms ns ys
  match-completeness (r₁ ·ˢ r₂) .((ms ++ ns) ++ ys) k (CanRec f) ((.(ms ++ ns) , ys , sf) , b , ((ms , ns) , tot , ms∈r₁ , ns∈r₂) , d) | refl | refl | p3 with assoc-append-suffix {ns ++ ys}{ms ++ ns ++ ys}{(ms ++ ns) ++ ys} p3 (append-suffix2 {ms} {ns ++ ys} {r₁} ms∈r₁)
  ... | t with match-completeness r₂ (ns ++ ys) (λ { (s' , sf') → k (s' , suffix-trans sf' t) }) (f (ns ++ ys) t) ((ns , ys , append-suffix2 {ns} {ys} {r₂} ns∈r₂) , refl , ns∈r₂ , trans (cong (λ x → k (ys , x)) (suffix-unique _ _)) d)
  ... | x = match-completeness r₁ ((ms ++ ns) ++ ys) _ (CanRec f) ((ms , ns ++ ys , t) , p3 , ms∈r₁ , x)
  match-completeness (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , b , inj₁ c , d) = either-if (inj₁ (match-completeness r₁ s k perm ((xs , ys) , b , c , d) ))
  match-completeness (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , b , inj₂ c , d) = either-if {match r₁ s k perm} {match r₂ s k perm}
                                                                       (inj₂ (match-completeness r₂ s k perm ((xs , ys) , b , c , d)))
  match-completeness (r ⁺ˢ) s k (CanRec f) ((xs , ys , sf) , b , S+ x , d) = either-if (inj₁ (match-completeness r s k (CanRec f) ((xs , (ys , sf)) , b , x , d)))
  match-completeness (r ⁺ˢ) s k (CanRec f) ((._ , ys , sf) , b , C+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c , d) with match r s k (CanRec f)
  match-completeness (r ⁺ˢ) s k (CanRec f) ((._ , ys , sf) , b , C+ refl q c , d) | true = refl
  match-completeness (r ⁺ˢ) s k (CanRec f) ((._ , ys , sf) , b , C+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c , d) | false
    with assoc-append-suffix {s₂ ++ ys}{(s₁ ++ s₂) ++ ys}{s} b (assoc-append-suffix (append-assoc s₁ s₂ ys) (append-suffix2 {s₁}{s₂ ++ ys}{r} q))
  ... | t with match-completeness (r ⁺ˢ) (s₂ ++ ys) (λ { (s' , sf') → k (s' , suffix-trans sf' t) }) (f (s₂ ++ ys) t) ((s₂ , ys , append-suffix2⁺ {s₂}{ys}{r} c) , refl , c , trans (cong (λ x → k (ys , x)) (suffix-unique _ _)) d)
  match-completeness (r ⁺ˢ) ._ k (CanRec f) ((._ , ys , sf) , refl , C+ {.(s₁ ++ s₂)}{s₁}{s₂} refl q c , d) | false | t | x = match-completeness r ((s₁ ++ s₂) ++ ys) _ (CanRec f) ((s₁ , s₂ ++ ys , t) , append-assoc s₁ s₂ ys , q , x)

  _accepts_ : RegExp → String.String → Bool
  r accepts s = match-plus (δ r , standardize r) l (λ { (s , sf) → null s }) (well-founded l)
    where l = String.toList s
          match-plus : Bool × StdRegExp → (s : List Char) → (Σ _ (λ s' → Suffix s' s) → Bool) → RecursionPermission s → Bool
          match-plus (false , r) s k perm = match r s k perm
          match-plus (true , r) s k perm = if null s then true else match r s k perm

  -- Overall correctness

  correct-soundness : (r : RegExp)
                    → (s : String.String)
                    → r accepts s ≡ true
                    → (String.toList s) ∈L r
  correct-soundness r s eq with String.toList s | δ' r
  ... | xs | inj₂ q with match-soundness (standardize r) xs _ (well-founded xs) eq
  ... | ((as , (bs , sf)) , a , b , c) with ∈L-soundness as r (inj₂ b)
  correct-soundness r s eq | xs | inj₂ q | (_ , _ ∷ _ , _) , _ , _ , () | as∈Lr
  correct-soundness r s eq | xs | inj₂ q | (as , [] , sf) , a , b , c | as∈Lr with trans (sym (append-rh-[] as)) a
  correct-soundness r s eq | as | inj₂ q | (.as , [] , sf) , a , b , c | as∈Lr | refl = as∈Lr
  correct-soundness r s eq | [] | inj₁ p = p
  correct-soundness r s eq | x ∷ xs | inj₁ p with match-soundness (standardize r) (x ∷ xs) _ (well-founded (x ∷ xs)) eq
  ... | ((as , (bs , sf)) , a , b , c) with ∈L-soundness as r (inj₂ b)
  correct-soundness r s eq | x ∷ xs | inj₁ p | (_ , _ ∷ _ , _) , _ , _ , () | _
  correct-soundness r s eq | x ∷ xs | inj₁ p | (as , [] , sf) , a , b , refl | inL-sn with trans (sym (append-rh-[] as)) a
  correct-soundness r s eq | x ∷ xs | inj₁ p | (.(x ∷ xs) , [] , sf) , a , b , refl | inL-sn | refl = inL-sn

  correct-completeness : (r : RegExp)
                       → (s : String.String)
                       → (String.toList s) ∈L r
                       → r accepts s ≡ true
  correct-completeness r s inL with String.toList s | δ' r
  correct-completeness r s inL | [] | inj₁ p = refl
  correct-completeness r s inL | x ∷ xs | inj₁ p with ∈L-completeness (x ∷ xs) r inL
  correct-completeness r s inL | x ∷ xs | inj₁ p | inj₁ (d , ())
  correct-completeness r s inL | x ∷ xs | inj₁ p | inj₂ q = match-completeness (standardize r) _ _ _ ((x ∷ xs , [] , suffix-[]-cons) , cong (λ l → x ∷ l) (append-rh-[] xs) , q , refl)
  correct-completeness r s inL | xs | inj₂ q with ∈L-completeness xs r inL
  correct-completeness r s inL | .[] | inj₂ q | inj₁ (d , refl) = ⊥-elim (q inL)
  correct-completeness r s inL | xs | inj₂ q | inj₂ p with non-empty {standardize r}
  correct-completeness r s inL | [] | inj₂ q | inj₂ p | f = ⊥-elim (q inL)
  correct-completeness r s inL | x ∷ xs | inj₂ q | inj₂ p | f = match-completeness (standardize r) _ _ _ ((x ∷ xs , [] , suffix-[]-cons) , cong (λ l → x ∷ l) (append-rh-[] xs) , p , refl)

  -- Standard "accepts"
  _acceptsˢ_ : StdRegExp → List Char → Bool
  r acceptsˢ s = match r s (λ { (s , sf) → null s }) (well-founded s)

  acceptsˢ-correct : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r
  acceptsˢ-correct r s m with bool-eq (match r s (λ { (s , sf) → null s }) (well-founded s))
  ... | inj₁ p with match-soundness r s (λ { (s , sf) → null s }) (well-founded s) p
  acceptsˢ-correct r .(xs ++ []) m | inj₁ p | (xs , [] , sf) , refl , inL , refl = eq-replace (sym (cong₂ _∈Lˢ_ {_}{_}{r}{r} (append-rh-[] xs) refl)) inL
  acceptsˢ-correct r s m | inj₁ p | (xs , x ∷ ys , sf) , eq , inL , ()
  acceptsˢ-correct r s m | inj₂ q with trans (sym m) q
  ... | ()
