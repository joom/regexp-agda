open import lib.Preliminaries
open import Definitions

module Lemmas where

  open List

  {- Our boolean char equality function that isn't directly primitive. -}
  equalb : Char → Char → Bool
  equalb x y with Char.equal x y
  ... | Inl _ = True
  ... | Inr _ = False

  {- Transitivity of suffixes -}
  suffix-trans : {A : Set} → {xs ys zs : List A} → Suffix xs ys → Suffix ys zs → Suffix xs zs
  suffix-trans s1 Stop = Drop s1
  suffix-trans s1 (Drop s2) = Drop (suffix-trans s1 s2)

  {- Prove that you can make a recursion permission for any suffix of [] -}
  perm-suffix-[] : {A : Set} (xs : List A) → Suffix xs [] → RecursionPermission xs
  perm-suffix-[] _ ()

  perm-suffix : {A : Set} {y : A} {xs ys : List A} → Suffix xs (y :: ys) → RecursionPermission ys → RecursionPermission xs
  perm-suffix Stop rec = rec
  perm-suffix (Drop s) (CanRec perm) = perm _ s

  {- Using perm-suffix-[] and perm-suffix, make a recursion permission for any list. -}
  well-founded : {A : Set} (ys : List A) → RecursionPermission ys
  well-founded [] = CanRec perm-suffix-[]
  well-founded (y :: ys) = CanRec (λ xs suff → perm-suffix suff (well-founded ys))

  suffix-[]-cons : {A : Set} → {x : A} → {xs : List A} → Suffix [] (x :: xs)
  suffix-[]-cons {xs = []} = Stop
  suffix-[]-cons {xs = y :: xs} = Drop suffix-[]-cons

  suffix-not-symmetric : ∀ {A} → (xs ys : List A) → Suffix xs ys → (Suffix ys xs → Void)
  suffix-not-symmetric ._ ._ Stop (Drop sf2) = suffix-not-symmetric _ _ (Drop Stop) sf2
  suffix-not-symmetric ._ ._ (Drop sf) Stop = suffix-not-symmetric _ _ sf (Drop Stop)
  suffix-not-symmetric ._ ._ (Drop sf) (Drop sf2) = suffix-not-symmetric _ _ sf (sub-lemma sf2)
    where sub-lemma : ∀ {A x y} → {xs ys : List A} → Suffix (x :: xs) ys → Suffix xs (y :: ys)
          sub-lemma Stop = Drop (Drop Stop)
          sub-lemma (Drop sf) = Drop (sub-lemma sf)

  not-suffix-self : ∀ {A} → (xs : List A) → Suffix xs xs → Void
  not-suffix-self [] ()
  not-suffix-self (x :: xs) (Drop sf) = suffix-not-symmetric _ _ sf Stop

  suffix-unique : ∀ {A} → {xs ys : List A} → (s1 s2 : Suffix xs ys) → s1 == s2
  suffix-unique Stop Stop = Refl
  suffix-unique Stop (Drop s2) = abort (not-suffix-self _ s2)
  suffix-unique (Drop s1) Stop = abort (not-suffix-self _ s1)
  suffix-unique (Drop s1) (Drop s2) = ap Drop (suffix-unique s1 s2)

  append-rh-[] : ∀ {A} (xs : List A) → (xs ++ []) == xs
  append-rh-[] [] = Refl
  append-rh-[] (x :: xs) = ap (λ l → x :: l) (append-rh-[] xs)

  singleton-append : {A : Set} → {x : A} → {xs ys s : List A} → xs == x :: [] → xs ++ ys == s → x :: ys == s
  singleton-append Refl Refl = Refl

  append-assoc : (xs ys zs : List Char) →  (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs)
  append-assoc [] ys zs = Refl
  append-assoc (x :: xs) ys zs = ap (λ l → x :: l) (append-assoc xs ys zs)

  same-char : (c : Char) → equalb c c == True
  same-char c with Char.equal c c
  ... | Inl _ = Refl
  ... | Inr f = abort (f Refl)

  {- Moves logical or to our lazy or implementation. -}
  either-if : {a b : Bool} → Either (a == True) (b == True) → if a then True else b == True
  either-if {True} (Inl Refl) = Refl
  either-if {True} (Inr Refl) = Refl
  either-if {False} (Inl ())
  either-if {False} (Inr Refl) = Refl

  {- Moves our lazy or implementation to logical or. -}
  lazy-or-eq : {a b : Bool} → if a then True else b == True → Either (a == True) (b == True)
  lazy-or-eq {True} {True} Refl = Inl Refl
  lazy-or-eq {True} {False} Refl = Inl Refl
  lazy-or-eq {False} {True} Refl = Inr Refl
  lazy-or-eq {False} {False} ()

  non-empty : ∀ {r} → ([] ∈Lˢ r → Void)
  non-empty {∅ˢ} inL = inL
  non-empty {Litˢ c} ()
  non-empty {r₁ ·ˢ r₂} ((xs , ys) , a , b , c) with empty-append {xs} {ys} a
  non-empty {r₁ ·ˢ r₂} ((.[] , .[]) , a , b , c) | Refl , Refl = non-empty {r₁} b
  non-empty {r₁ ⊕ˢ r₂} (Inl x) = non-empty {r₁} x
  non-empty {r₁ ⊕ˢ r₂} (Inr x) = non-empty {r₂} x
  non-empty {r ⁺ˢ} (S+ x) = non-empty {r} x
  non-empty {r ⁺ˢ} (C+ {.[]}{s₁}{s₂} p q inL) with empty-append {s₁} {s₂} p
  non-empty {r ⁺ˢ} (C+ p q inL) | Refl , Refl = non-empty {r} q
  non-empty {Gˢ r} inL = non-empty {r} inL

  cons-empty : {x : Char} → {xs : List Char} → x :: xs == [] → Void
  cons-empty ()

  append-suffix2' : {xs ys : List Char} → (xs == [] → Void) → Suffix ys (xs ++ ys)
  append-suffix2' {[]} f = abort (f Refl)
  append-suffix2' {x :: []} {ys} f = Stop
  append-suffix2' {x :: y :: xs} {ys} f = Drop (append-suffix2' {y :: xs} {ys} (cons-empty {y} {xs}))

  append-suffix2 : ∀ {xs ys r} → xs ∈Lˢ r → Suffix ys (xs ++ ys)
  append-suffix2 {xs} {ys} {r} inL with non-empty {r}
  append-suffix2 {[]} inL | q = abort (q inL)
  append-suffix2 {x :: xs} {ys} inL | q = append-suffix2' {x :: xs} {ys} (cons-empty {x} {xs})

  append-suffix2⁺ : ∀ {xs ys r} → xs ∈L⁺ r → Suffix ys (xs ++ ys)
  append-suffix2⁺ {xs}{ys}{r} inL with non-empty {r}
  append-suffix2⁺ {[]} (S+ x) | q = abort (q x)
  append-suffix2⁺ {[]} (C+ {._}{s₁}{s₂} x x₁ inL) | q with empty-append {s₁} {s₂} x
  append-suffix2⁺ {[]} (C+ x x₁ inL) | q | Refl , Refl = abort (q x₁)
  append-suffix2⁺ {x :: xs} {ys} inL | q = append-suffix2' {x :: xs} {ys} (cons-empty {x} {xs})

  assoc-append-suffix : {xs ys zs : List Char}
                      → ys == zs
                      → Suffix xs ys
                      → Suffix xs zs
  assoc-append-suffix Refl sf = sf

  same-list-language : {xs ys : List Char} → {r : StdRegExp} → xs == ys → xs ∈Lˢ r → ys ∈Lˢ r
  same-list-language Refl inL = inL

  null-lemma : {ys : List Char} → null ys == True → ys == []
  null-lemma {[]} eq = Refl
  null-lemma {_ :: _} ()

  replace-left : (as bs xs ys s' : List Char) → as ++ bs == xs → xs ++ ys == s' → as ++ bs ++ ys == s'
  replace-left as bs .(as ++ bs) ys .((as ++ bs) ++ ys) Refl Refl = append-assoc as bs ys

  replace-right : (xs ys as bs s : List Char) → as ++ bs == ys → xs ++ ys == s → (xs ++ as) ++ bs == s
  replace-right xs .(as ++ bs) as bs .(xs ++ as ++ bs) Refl Refl = ! (append-assoc xs as bs)

  -- Standardization proofs
  -- Overall, we are to prove that ∀ (r : RegExp) L(r) = L(standardize(r)) ∪ δ (if δ r then ε else ∅)

  ∈L-soundness : (s : List Char)
               → (r : RegExp)
               → Either ((δ r == True) × (s == [])) (s ∈Lˢ (standardize r))
               → s ∈L r
  ∈L-soundness .[] r (Inl (d , Refl)) with δ' r
  ... | Inl p = p
  ∈L-soundness .[] r (Inl (() , Refl)) | Inr q
  ∈L-soundness s ∅ (Inr x) = x
  ∈L-soundness s ε (Inr ())
  ∈L-soundness s (Lit x) (Inr q) = q
  ∈L-soundness s (r₁ · r₂) (Inr q) with δ' r₁ | δ' r₂
  ∈L-soundness [] (r₁ · r₂) (Inr (Inl x)) | Inl a | Inl b = ([] , []) , Refl , a , b
  ∈L-soundness (x :: s) (r₁ · r₂) (Inr (Inl x₁)) | Inl a | Inl b = (x :: s , []) , ap (λ l → x :: l) (append-rh-[] s) , ∈L-soundness (x :: s) r₁ (Inr x₁) , b
  ∈L-soundness [] (r₁ · r₂) (Inr (Inr (Inl x))) | Inl a | Inl b = ([] , []) , Refl , a , b
  ∈L-soundness (x :: s) (r₁ · r₂) (Inr (Inr (Inl x₁))) | Inl a | Inl b = ([] , x :: s) , Refl , a , ∈L-soundness (x :: s) r₂ (Inr x₁)
  ∈L-soundness s (r₁ · r₂) (Inr (Inr (Inr ((x , y) , n , p , q)))) | Inl a | Inl b = (x , y) , n , ∈L-soundness x r₁ (Inr p) , ∈L-soundness y r₂ (Inr q)
  ∈L-soundness s (r₁ · r₂) (Inr (Inl x)) | Inl a | Inr b = ([] , s) , Refl , a , ∈L-soundness s r₂ (Inr x)
  ∈L-soundness s (r₁ · r₂) (Inr (Inl x)) | Inr a | Inl b = (s , []) , append-rh-[] s , ∈L-soundness s r₁ (Inr x) , b
  ∈L-soundness s (r₁ · r₂) (Inr (Inr ((x , y) , n , p , q))) | Inl a | Inr b = (x , y) , n , ∈L-soundness x r₁ (Inr p) , ∈L-soundness y r₂ (Inr q)
  ∈L-soundness s (r₁ · r₂) (Inr (Inr ((x , y) , n , p , q))) | Inr a | Inl b = (x , y) , n , ∈L-soundness x r₁ (Inr p) , ∈L-soundness y r₂ (Inr q)
  ∈L-soundness s (r₁ · r₂) (Inr ((x , y) , n , p , q)) | Inr a | Inr b = (x , y) , n , ∈L-soundness x r₁ (Inr p) , ∈L-soundness y r₂ (Inr q)
  ∈L-soundness s (r₁ ⊕ r₂) (Inr (Inl x)) = Inl (∈L-soundness s r₁ (Inr x))
  ∈L-soundness s (r₁ ⊕ r₂) (Inr (Inr x)) = Inr (∈L-soundness s r₂ (Inr x))
  ∈L-soundness s (r *) (Inr (S+ x)) = Cx {s}{s}{[]}{r} (append-rh-[] s) (∈L-soundness s r (Inr x)) (Ex Refl)
  ∈L-soundness s (r *) (Inr (C+ {.s}{s₁}{s₂} a b c)) = Cx a (∈L-soundness s₁ r (Inr b)) (∈L-soundness s₂ (r *) (Inr c))
  ∈L-soundness s (G r) (Inr x) = ∈L-soundness s r (Inr x)

  ∈L-completeness : (s : List Char)
                  → (r : RegExp)
                  → s ∈L r
                  → Either ((δ r == True) × (s == [])) (s ∈Lˢ (standardize r))
  ∈L-completeness s ∅ inL = Inr inL
  ∈L-completeness s ε inL = Inl (Refl , inL)
  ∈L-completeness .(x :: []) (Lit x) Refl = Inr Refl
  ∈L-completeness s (r₁ · r₂) inL with δ' r₁ | δ' r₂
  ∈L-completeness .(x ++ y) (r₁ · r₂) ((x , y) , Refl , b , c) | Inl p | Inl q with ∈L-completeness x r₁ b | ∈L-completeness y r₂ c
  ∈L-completeness .([] ++ []) (r₁ · r₂) ((.[] , .[]) , Refl , b , c) | Inl p | Inl q | Inl (m , Refl) | Inl (t , Refl) = Inl (Refl , Refl)
  ∈L-completeness .([] ++ y) (r₁ · r₂) ((.[] , y) , Refl , b , c) | Inl p | Inl q | Inl (m , Refl) | Inr t = Inr (Inr (Inl t))
  ∈L-completeness .(x ++ []) (r₁ · r₂) ((x , .[]) , Refl , b , c) | Inl p | Inl q | Inr m | Inl (t , Refl) = Inr (Inl (same-list-language {_}{_}{standardize r₁} (! (append-rh-[] x)) m))
  ∈L-completeness .(x ++ y) (r₁ · r₂) ((x , y) , Refl , b , c) | Inl p | Inl q | Inr m | Inr t = Inr (Inr (Inr ((x , y) , Refl , m , t)))
  ∈L-completeness s (r₁ · r₂) ((x , y) , a , b , c) | Inl p | Inr q with ∈L-completeness x r₁ b | ∈L-completeness y r₂ c
  ∈L-completeness .[] (r₁ · r₂) ((.[] , .[]) , Refl , b , c) | Inl p | Inr q | Inl (m , Refl) | Inl (t , Refl) = abort (q c)
  ∈L-completeness y (r₁ · r₂) ((.[] , .y) , Refl , b , c) | Inl p | Inr q | Inl (m , Refl) | Inr t = Inr (Inl t)
  ∈L-completeness .(x ++ []) (r₁ · r₂) ((x , .[]) , Refl , b , c) | Inl p | Inr q | Inr m | Inl (t , Refl) = abort (q c)
  ∈L-completeness .(x ++ y) (r₁ · r₂) ((x , y) , Refl , b , c) | Inl p | Inr q | Inr m | Inr t = Inr (Inr ((x , y) , Refl , m , t))
  ∈L-completeness s (r₁ · r₂) ((x , y) , a , b , c) | Inr p | Inl q with ∈L-completeness x r₁ b | ∈L-completeness y r₂ c
  ∈L-completeness s (r₁ · r₂) ((.[] , .[]) , a , b , c) | Inr p | Inl q | Inl (m , Refl) | Inl (t , Refl) = abort (p b)
  ∈L-completeness y (r₁ · r₂) ((.[] , .y) , Refl , b , c) | Inr p | Inl q | Inl (m , Refl) | Inr t = abort (p b)
  ∈L-completeness .(x ++ []) (r₁ · r₂) ((x , .[]) , Refl , b , c) | Inr p | Inl q | Inr m | Inl (t , Refl) = Inr (Inl (same-list-language {_}{_}{standardize r₁}(! (append-rh-[] x)) m))
  ∈L-completeness s (r₁ · r₂) ((x , y) , a , b , c) | Inr p | Inl q | Inr m | Inr t = Inr (Inr ((x , y) , a , m , t))
  ∈L-completeness s (r₁ · r₂) ((x , y) , a , b , c) | Inr p | Inr q with ∈L-completeness x r₁ b | ∈L-completeness y r₂ c
  ∈L-completeness .[] (r₁ · r₂) ((.[] , .[]) , Refl , b , c) | Inr p | Inr q | Inl (m , Refl) | Inl (t , Refl) = abort (p b)
  ∈L-completeness y (r₁ · r₂) ((.[] , .y) , Refl , b , c) | Inr p | Inr q | Inl (m , Refl) | Inr t = abort (p b)
  ∈L-completeness .(x ++ []) (r₁ · r₂) ((x , .[]) , Refl , b , c) | Inr p | Inr q | Inr m | Inl (t , Refl) = abort (q c)
  ∈L-completeness .(x ++ y) (r₁ · r₂) ((x , y) , Refl , b , c) | Inr p | Inr q | Inr m | Inr t = Inr ((x , y) , Refl , m , t)
  ∈L-completeness s (r₁ ⊕ r₂) (Inl x) with ∈L-completeness s r₁ x
  ∈L-completeness .[] (r₁ ⊕ r₂) (Inl x) | Inl (d , Refl) with δ' r₁
  ∈L-completeness .[] (r₁ ⊕ r₂) (Inl x₁) | Inl (d , Refl) | Inl x = Inl (Refl , Refl)
  ∈L-completeness .[] (_ ⊕ _) (Inl _) | Inl (() , Refl) | Inr _
  ∈L-completeness s (r₁ ⊕ r₂) (Inl x) | Inr q = Inr (Inl q)
  ∈L-completeness s (r₁ ⊕ r₂) (Inr x) with ∈L-completeness s r₂ x
  ∈L-completeness .[] (r₁ ⊕ r₂) (Inr x) | Inl (d , Refl) with δ' r₂
  ∈L-completeness .[] (r₁ ⊕ r₂) (Inr x) | Inl (Refl , Refl) | Inl a with δ' r₁
  ∈L-completeness .[] (r₁ ⊕ r₂) (Inr x₁) | Inl (Refl , Refl) | Inl a | Inl x = Inl (Refl , Refl)
  ∈L-completeness .[] (r₁ ⊕ r₂) (Inr x₁) | Inl (Refl , Refl) | Inl a | Inr x = Inl (Refl , Refl)
  ∈L-completeness .[] (_ ⊕ _) (Inr _) | Inl (() , Refl) | Inr _
  ∈L-completeness s (r₁ ⊕ r₂) (Inr x) | Inr q = Inr (Inr q)
  ∈L-completeness .[] (r *) (Ex Refl) = Inl (Refl , Refl)
  ∈L-completeness s (r *) (Cx {.s}{s₁}{s₂} x x₁ inL) with ∈L-completeness s₁ r x₁ | ∈L-completeness s₂ (r *) inL
  ∈L-completeness s (r *) (Cx x x₁ inL) | Inl (m , Refl) | Inl (t , Refl) = Inl (Refl , (! x))
  ∈L-completeness s₂ (r *) (Cx Refl x₁ inL) | Inl (m , Refl) | Inr t = Inr t
  ∈L-completeness ._ (r *) (Cx {._}{s₁}{.[]} Refl x₁ inL) | Inr m | Inl (Refl , Refl) = Inr (S+ (same-list-language {_}{_}{standardize r} (! (append-rh-[] s₁)) m))
  ∈L-completeness s (r *) (Cx x x₁ inL) | Inr m | Inr t = Inr (C+ x m t)
  ∈L-completeness s (G r) inL with ∈L-completeness s r inL
  ∈L-completeness s (G r) inL | Inl (a , b) with δ' (G r)
  ... | Inl x = Inl (Refl , b)
  ... | Inr x = Inl (a , b)
  ∈L-completeness s (G r) inL | Inr x = Inr x
