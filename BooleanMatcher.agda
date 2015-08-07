open import lib.Preliminaries
open import Definitions
open import Lemmas

module BooleanMatcher where

  open List

  -- Matching algorithm
  match : StdRegExp → (s : List Char) → (Σ (λ s' → Suffix s' s) → Bool) → RecursionPermission s → Bool
  match ∅ˢ s k _ = False
  match (Litˢ _) [] _ _ = False
  match (Litˢ c) (x :: xs) k _ = if (equalb x c) then (k (xs , Stop)) else False
  match (r₁ ·ˢ r₂) s k (CanRec f) = match r₁ s (λ { (s' , sf) → match r₂ s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)
  match (r₁ ⊕ˢ r₂) s k perm = if match r₁ s k perm then True else match r₂ s k perm
  match (r ⁺ˢ) s k (CanRec f) = if match r s k (CanRec f) then True else match r s (λ { (s' , sf) → match (r ⁺ˢ) s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)
  match (Gˢ r) s k perm = match r s k perm

  -- Proofs

  {- Show that if match r s k perm is true, then there is a split of s, namely s₁ s₂, such that s₁ ∈L r and k s₂ is true. -}
  match-soundness : (r : StdRegExp)
                  → (s : List Char)
                  → (k : Σ (λ s' → Suffix s' s) → Bool)
                  → (perm : RecursionPermission s)
                  → match r s k perm == True
                  → Σ {_}{_}{List Char × (Σ (λ s' → Suffix s' s))} (λ { (p , (s' , sf)) → (p ++ s' == s) × (p ∈Lˢ r) × (k (s' , sf) == True)})
  match-soundness ∅ˢ s k perm ()
  match-soundness (Litˢ c) [] k perm ()
  match-soundness (Litˢ c) (y :: ys) k perm m with Char.equal y c
  match-soundness (Litˢ c) (.c :: ys) k perm m | Inl Refl = (c :: [] , (ys , Stop)) , (Refl , (Refl , m))
  match-soundness (Litˢ c) (y :: ys) k perm () | Inr e
  match-soundness (r₁ ·ˢ r₂) s k (CanRec f) m with match-soundness r₁ s (λ { (s' , sf) → match r₂ s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f) m
  match-soundness (r₁ ·ˢ r₂) s k (CanRec f) m | (xs , ys , r) , a , b , c
    with match-soundness r₂ ys (λ { (s' , sf) → k (s' , (suffix-trans sf r)) }) (f ys r) c
  match-soundness (r₁ ·ˢ r₂) .(xs ++ as ++ bs) k (CanRec f) m | (xs , .(as ++ bs) , r) , Refl , b , c | (as , bs , r1) , Refl , b1 , c1 = ((xs ++ as) , (bs , suffix-trans r1 r)) , ((! (append-assoc xs as bs)) , (((xs , as) , (Refl , (b , b1))) , c1))
  match-soundness (r₁ ⊕ˢ r₂) s k perm m with lazy-or-eq {match r₁ s k perm} {match r₂ s k perm} m
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | Inl x with match-soundness r₁ s k perm x
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | Inl x | (p , q , r) , a , b , c = (p , (q , r)) , (a , (Inl b , c))
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | Inr x with match-soundness r₂ s k perm x
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | Inr x | (p , q , r) , a , b , c = (p , (q , r)) , (a , (Inr b , c))
  match-soundness (r ⁺ˢ) s k (CanRec f) m with lazy-or-eq {match r s k (CanRec f)} { match r s (λ { (s' , sf) → match (r ⁺ˢ) s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)} m
  match-soundness (r ⁺ˢ) s k (CanRec f) m | Inl x with match-soundness r s k (CanRec f) x
  match-soundness (r ⁺ˢ) s k (CanRec f) m | Inl x | (xs , ys , sf) , a , fst , snd = (xs , (ys , sf)) , (a , (S+ fst , snd))
  match-soundness (r ⁺ˢ) s k (CanRec f) m | Inr x with match-soundness r s (λ { (s' , sf) → match (r ⁺ˢ) s' _ (f s' sf) }) (CanRec f) x
  match-soundness (r ⁺ˢ) s k (CanRec f) m | Inr x | (xs , (ys , sf)) , eq , xs∈rS , d with match-soundness (r ⁺ˢ) ys (λ { (s' , sf') → k (s' , suffix-trans sf' sf) } ) (f ys sf) d
  match-soundness (r ⁺ˢ) s k (CanRec f) m | Inr x | (xs , (ys , sf)) , eq , xs∈rS , d | (ys' , ys'' , sf') , eq1 , ys'∈rP , d1 with ! (append-assoc xs ys' ys'')
  match-soundness (r ⁺ˢ) .(xs ++ ys' ++ ys'') k (CanRec f) m | Inr x | (xs , .(ys' ++ ys'') , sf) , Refl , xs∈rS , d | (ys' , ys'' , sf') , Refl , ys'∈rP , d1 | app = (xs ++ ys' , (ys'' , suffix-trans sf' sf)) , (app , (C+ Refl xs∈rS ys'∈rP , d1))
  match-soundness (Gˢ r) s k perm m = match-soundness r s k perm m

  {- Show that if there is a split of s, namely s₁ s₂, such that s₁ ∈L r and k s₂ is true, then match r s k perm is true. -}
  match-completeness : (r : StdRegExp)
                     → (s : List Char)
                     → (k : Σ (λ s' → Suffix s' s) → Bool)
                     → (perm : RecursionPermission s)
                     → Σ {_}{_}{List Char × (Σ (λ s' → Suffix s' s))} (λ { (p , (s' , sf)) → (p ++ s' == s) × (p ∈Lˢ r) × (k (s' , sf) == True)})
                     → match r s k perm == True
  match-completeness ∅ˢ _ _ _ (_ , _ , c , _) = abort c
  match-completeness (Litˢ x) s k perm ((xs , (ys , sf)) , b , c , d) with ! (singleton-append c b)
  match-completeness (Litˢ x) .(x :: ys) k perm ((xs , ys , sf) , b , c , d) | Refl with equalb x x | same-char x
  match-completeness (Litˢ x) .(x :: ys) k perm ((xs , ys , sf) , b , c , d) | Refl | True | Refl = transport (λ (h : Suffix ys (x :: ys) ) → k (ys , h) == True) (suffix-unique sf Stop) d
  match-completeness (Litˢ x) .(x :: ys) k perm ((xs , ys , sf) , b , c , d) | Refl | False | ()
  match-completeness (r₁ ·ˢ r₂) s k perm ((xs , (ys , sf)) , b , ((ms , ns) , tot , ms∈r₁ , ns∈r₂) , d) with tot | b | append-assoc ms ns ys
  match-completeness (r₁ ·ˢ r₂) .((ms ++ ns) ++ ys) k (CanRec f) ((.(ms ++ ns) , ys , sf) , b , ((ms , ns) , tot , ms∈r₁ , ns∈r₂) , d) | Refl | Refl | p3 with assoc-append-suffix {ns ++ ys}{ms ++ ns ++ ys}{(ms ++ ns) ++ ys} p3 (append-suffix2 {ms} {ns ++ ys} {r₁} ms∈r₁)
  ... | t with match-completeness r₂ (ns ++ ys) (λ { (s' , sf') → k (s' , suffix-trans sf' t) }) (f (ns ++ ys) t) ((ns , ys , append-suffix2 {ns} {ys} {r₂} ns∈r₂) , Refl , ns∈r₂ , d ∘ ap (λ x → k (ys , x)) (suffix-unique _ _))
  ... | x = match-completeness r₁ ((ms ++ ns) ++ ys) _ (CanRec f) ((ms , ns ++ ys , t) , p3 , ms∈r₁ , x)
  match-completeness (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , b , Inl c , d) = either-if (Inl (match-completeness r₁ s k perm ((xs , ys) , b , c , d) ))
  match-completeness (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , b , Inr c , d) = either-if {match r₁ s k perm} {match r₂ s k perm}
                                                                       (Inr (match-completeness r₂ s k perm ((xs , ys) , b , c , d)))
  match-completeness (r ⁺ˢ) s k (CanRec f) ((xs , ys , sf) , b , S+ x , d) = either-if (Inl (match-completeness r s k (CanRec f) ((xs , (ys , sf)) , b , x , d)))
  match-completeness (r ⁺ˢ) s k (CanRec f) ((._ , ys , sf) , b , C+ {.(s₁ ++ s₂)}{s₁}{s₂} Refl q c , d) with match r s k (CanRec f)
  match-completeness (r ⁺ˢ) s k (CanRec f) ((._ , ys , sf) , b , C+ Refl q c , d) | True = Refl
  match-completeness (r ⁺ˢ) s k (CanRec f) ((._ , ys , sf) , b , C+ {.(s₁ ++ s₂)}{s₁}{s₂} Refl q c , d) | False
    with assoc-append-suffix {s₂ ++ ys}{(s₁ ++ s₂) ++ ys}{s} b (assoc-append-suffix (append-assoc s₁ s₂ ys) (append-suffix2 {s₁}{s₂ ++ ys}{r} q))
  ... | t with match-completeness (r ⁺ˢ) (s₂ ++ ys) (λ { (s' , sf') → k (s' , suffix-trans sf' t) }) (f (s₂ ++ ys) t) ((s₂ , ys , append-suffix2⁺ {s₂}{ys}{r} c) , Refl , c , d ∘ ap (λ x → k (ys , x)) (suffix-unique _ _) )
  match-completeness (r ⁺ˢ) ._ k (CanRec f) ((._ , ys , sf) , Refl , C+ {.(s₁ ++ s₂)}{s₁}{s₂} Refl q c , d) | False | t | x = match-completeness r ((s₁ ++ s₂) ++ ys) _ (CanRec f) ((s₁ , s₂ ++ ys , t) , append-assoc s₁ s₂ ys , q , x)
  match-completeness (Gˢ r) s k perm inL = match-completeness r s k perm inL


  _accepts_ : RegExp → String.String → Bool
  r accepts s = match-plus (δ r , standardize r) l (λ { (s , sf) → null s }) (well-founded l)
    where l = String.toList s
          match-plus : Bool × StdRegExp → (s : List Char) → (Σ (λ s' → Suffix s' s) → Bool) → RecursionPermission s → Bool
          match-plus (False , r) s k perm = match r s k perm
          match-plus (True , r) s k perm = if null s then True else match r s k perm

  -- Overall correctness

  correct-soundness : (r : RegExp)
                    → (s : String.String)
                    → r accepts s == True
                    → (String.toList s) ∈L r
  correct-soundness r s eq with String.toList s | δ' r
  ... | xs | Inr q with match-soundness (standardize r) xs _ (well-founded xs) eq
  ... | ((as , (bs , sf)) , a , b , c) with ∈L-soundness as r (Inr b)
  correct-soundness r s eq | xs | Inr q | (_ , _ :: _ , _) , _ , _ , () | as∈Lr
  correct-soundness r s eq | xs | Inr q | (as , [] , sf) , a , b , c | as∈Lr with a ∘ ! (append-rh-[] as)
  correct-soundness r s eq | as | Inr q | (.as , [] , sf) , a , b , c | as∈Lr | Refl = as∈Lr
  correct-soundness r s eq | [] | Inl p = p
  correct-soundness r s eq | x :: xs | Inl p with match-soundness (standardize r) (x :: xs) _ (well-founded (x :: xs)) eq
  ... | ((as , (bs , sf)) , a , b , c) with ∈L-soundness as r (Inr b)
  correct-soundness r s eq | x :: xs | Inl p | (_ , _ :: _ , _) , _ , _ , () | _
  correct-soundness r s eq | x :: xs | Inl p | (as , [] , sf) , a , b , Refl | inL-sn with a ∘ ! (append-rh-[] as)
  correct-soundness r s eq | x :: xs | Inl p | (.(x :: xs) , [] , sf) , a , b , Refl | inL-sn | Refl = inL-sn

  correct-completeness : (r : RegExp)
                       → (s : String.String)
                       → (String.toList s) ∈L r
                       → r accepts s == True
  correct-completeness r s inL with String.toList s | δ' r
  correct-completeness r s inL | [] | Inl p = Refl
  correct-completeness r s inL | x :: xs | Inl p with ∈L-completeness (x :: xs) r inL
  correct-completeness r s inL | x :: xs | Inl p | Inl (d , ())
  correct-completeness r s inL | x :: xs | Inl p | Inr q = match-completeness (standardize r) _ _ _ ((x :: xs , [] , suffix-[]-cons) , ap (λ l → x :: l) (append-rh-[] xs) , q , Refl)
  correct-completeness r s inL | xs | Inr q with ∈L-completeness xs r inL
  correct-completeness r s inL | .[] | Inr q | Inl (d , Refl) = abort (q inL)
  correct-completeness r s inL | xs | Inr q | Inr p with non-empty {standardize r}
  correct-completeness r s inL | [] | Inr q | Inr p | f = abort (q inL)
  correct-completeness r s inL | x :: xs | Inr q | Inr p | f = match-completeness (standardize r) _ _ _ ((x :: xs , [] , suffix-[]-cons) , ap (λ l → x :: l) (append-rh-[] xs) , p , Refl)
