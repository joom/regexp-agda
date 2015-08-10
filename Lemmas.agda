open import Definitions

module Lemmas where

  open import Data.Bool
  open import Data.Char
  open import Data.Empty
  open import Data.List
  open import Data.Product
  open import Data.Sum
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary.Decidable

  {- Transitivity of suffixes -}
  suffix-trans : {A : Set} → {xs ys zs : List A} → Suffix xs ys → Suffix ys zs → Suffix xs zs
  suffix-trans s1 Stop = Drop s1
  suffix-trans s1 (Drop s2) = Drop (suffix-trans s1 s2)

  {- Prove that you can make a recursion permission for any suffix of [] -}
  perm-suffix-[] : {A : Set} (xs : List A) → Suffix xs [] → RecursionPermission xs
  perm-suffix-[] _ ()

  perm-suffix : {A : Set} {y : A} {xs ys : List A} → Suffix xs (y ∷ ys) → RecursionPermission ys → RecursionPermission xs
  perm-suffix Stop rec = rec
  perm-suffix (Drop s) (CanRec perm) = perm _ s

  {- Using perm-suffix-[] and perm-suffix, make a recursion permission for any list. -}
  well-founded : {A : Set} (ys : List A) → RecursionPermission ys
  well-founded [] = CanRec perm-suffix-[]
  well-founded (y ∷ ys) = CanRec (λ xs suff → perm-suffix suff (well-founded ys))

  suffix-[]-cons : {A : Set} → {x : A} → {xs : List A} → Suffix [] (x ∷ xs)
  suffix-[]-cons {xs = []} = Stop
  suffix-[]-cons {xs = y ∷ xs} = Drop suffix-[]-cons

  suffix-not-symmetric : ∀ {A} → (xs ys : List A) → Suffix xs ys → (Suffix ys xs → ⊥)
  suffix-not-symmetric ._ ._ Stop (Drop sf2) = suffix-not-symmetric _ _ (Drop Stop) sf2
  suffix-not-symmetric ._ ._ (Drop sf) Stop = suffix-not-symmetric _ _ sf (Drop Stop)
  suffix-not-symmetric ._ ._ (Drop sf) (Drop sf2) = suffix-not-symmetric _ _ sf (sub-lemma sf2)
    where sub-lemma : ∀ {A x y} → {xs ys : List A} → Suffix (x ∷ xs) ys → Suffix xs (y ∷ ys)
          sub-lemma Stop = Drop (Drop Stop)
          sub-lemma (Drop sf) = Drop (sub-lemma sf)

  not-suffix-self : ∀ {A} → (xs : List A) → Suffix xs xs → ⊥
  not-suffix-self [] ()
  not-suffix-self (x ∷ xs) (Drop sf) = suffix-not-symmetric _ _ sf Stop

  suffix-unique : ∀ {A} → {xs ys : List A} → (s1 s2 : Suffix xs ys) → s1 ≡ s2
  suffix-unique Stop Stop = refl
  suffix-unique Stop (Drop s2) = ⊥-elim (not-suffix-self _ s2)
  suffix-unique (Drop s1) Stop = ⊥-elim (not-suffix-self _ s1)
  suffix-unique (Drop s1) (Drop s2) = cong Drop (suffix-unique s1 s2)

  append-rh-[] : ∀ {l1} {A : Set l1} (xs : List A) → (xs ++ []) ≡ xs
  append-rh-[] [] = refl
  append-rh-[] (x ∷ xs) = cong (λ l → x ∷ l) (append-rh-[] xs)

  singleton-append : {A : Set} → {x : A} → {xs ys s : List A} → xs ≡ x ∷ [] → xs ++ ys ≡ s → x ∷ ys ≡ s
  singleton-append refl refl = refl

  append-assoc : (xs ys zs : List Char) →  (xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs)
  append-assoc [] ys zs = refl
  append-assoc (x ∷ xs) ys zs = cong (λ l → x ∷ l) (append-assoc xs ys zs)

  same-char : (c : Char) → (c == c) ≡ true
  same-char c with c Data.Char.≟ c
  ... | yes p = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  eq-replace : {a b : Set} → a ≡ b → a → b
  eq-replace refl x = x

  {- Moves logical or to our lazy or implementation. -}
  either-if : {a b : Bool} → (a ≡ true) ⊎ (b ≡ true) → (if a then true else b) ≡ true
  either-if {true} (inj₁ refl) = refl
  either-if {true} (inj₂ refl) = refl
  either-if {false} (inj₁ ())
  either-if {false} (inj₂ refl) = refl

  {- Moves our lazy or implementation to logical or. -}
  lazy-or-eq : {a b : Bool} → (if a then true else b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  lazy-or-eq {true} {true} refl = inj₁ refl
  lazy-or-eq {true} {false} refl = inj₁ refl
  lazy-or-eq {false} {true} refl = inj₂ refl
  lazy-or-eq {false} {false} ()

  non-empty : ∀ {r} → ([] ∈Lˢ r → ⊥)
  non-empty {∅ˢ} inL = inL
  non-empty {Litˢ c} ()
  non-empty {r₁ ·ˢ r₂} ((xs , ys) , a , b , c) with empty-append {xs} {ys} a
  non-empty {r₁ ·ˢ r₂} ((.[] , .[]) , a , b , c) | refl , refl = non-empty {r₁} b
  non-empty {r₁ ⊕ˢ r₂} (inj₁ x) = non-empty {r₁} x
  non-empty {r₁ ⊕ˢ r₂} (inj₂ x) = non-empty {r₂} x
  non-empty {r ⁺ˢ} (S+ x) = non-empty {r} x
  non-empty {r ⁺ˢ} (C+ {.[]}{s₁}{s₂} p q inL) with empty-append {s₁} {s₂} p
  non-empty {r ⁺ˢ} (C+ p q inL) | refl , refl = non-empty {r} q
  non-empty {Gˢ r} inL = non-empty {r} inL

  cons-empty : {x : Char} → {xs : List Char} → x ∷ xs ≡ [] → ⊥
  cons-empty ()

  append-suffix2' : {xs ys : List Char} → (xs ≡ [] → ⊥) → Suffix ys (xs ++ ys)
  append-suffix2' {[]} f = ⊥-elim (f refl)
  append-suffix2' {x ∷ []} {ys} f = Stop
  append-suffix2' {x ∷ y ∷ xs} {ys} f = Drop (append-suffix2' {y ∷ xs} {ys} (cons-empty {y} {xs}))

  append-suffix2 : ∀ {xs ys r} → xs ∈Lˢ r → Suffix ys (xs ++ ys)
  append-suffix2 {xs} {ys} {r} inL with non-empty {r}
  append-suffix2 {[]} inL | q = ⊥-elim (q inL)
  append-suffix2 {x ∷ xs} {ys} inL | q = append-suffix2' {x ∷ xs} {ys} (cons-empty {x} {xs})

  append-suffix2⁺ : ∀ {xs ys r} → xs ∈L⁺ r → Suffix ys (xs ++ ys)
  append-suffix2⁺ {xs}{ys}{r} inL with non-empty {r}
  append-suffix2⁺ {[]} (S+ x) | q = ⊥-elim (q x)
  append-suffix2⁺ {[]} (C+ {._}{s₁}{s₂} x x₁ inL) | q with empty-append {s₁} {s₂} x
  append-suffix2⁺ {[]} (C+ x x₁ inL) | q | refl , refl = ⊥-elim (q x₁)
  append-suffix2⁺ {x ∷ xs} {ys} inL | q = append-suffix2' {x ∷ xs} {ys} (cons-empty {x} {xs})

  assoc-append-suffix : {xs ys zs : List Char}
                      → ys ≡ zs
                      → Suffix xs ys
                      → Suffix xs zs
  assoc-append-suffix refl sf = sf

  same-list-language : {xs ys : List Char} → {r : StdRegExp} → xs ≡ ys → xs ∈Lˢ r → ys ∈Lˢ r
  same-list-language refl inL = inL

  null-lemma : {ys : List Char} → null ys ≡ true → ys ≡ []
  null-lemma {[]} eq = refl
  null-lemma {_ ∷ _} ()

  replace-left : (as bs xs ys s' : List Char) → as ++ bs ≡ xs → xs ++ ys ≡ s' → as ++ bs ++ ys ≡ s'
  replace-left as bs .(as ++ bs) ys .((as ++ bs) ++ ys) refl refl = append-assoc as bs ys

  replace-right : (xs ys as bs s : List Char) → as ++ bs ≡ ys → xs ++ ys ≡ s → (xs ++ as) ++ bs ≡ s
  replace-right xs .(as ++ bs) as bs .(xs ++ as ++ bs) refl refl = sym (append-assoc xs as bs)

  -- Standardization proofs
  -- Overall, we are to prove that ∀ (r : RegExp) L(r) = L(standardize(r)) ∪ δ (if δ r then ε else ∅)

  ∈L-soundness : (s : List Char)
               → (r : RegExp)
               → ((δ r ≡ true) × (s ≡ [])) ⊎ (s ∈Lˢ (standardize r))
               → s ∈L r
  ∈L-soundness .[] r (inj₁ (d , refl)) with δ' r
  ... | inj₁ p = p
  ∈L-soundness .[] r (inj₁ (() , refl)) | inj₂ q
  ∈L-soundness s ∅ (inj₂ x) = x
  ∈L-soundness s ε (inj₂ ())
  ∈L-soundness s (Lit x) (inj₂ q) = q
  ∈L-soundness s (r₁ · r₂) (inj₂ q) with δ' r₁ | δ' r₂
  ∈L-soundness [] (r₁ · r₂) (inj₂ (inj₁ x)) | inj₁ a | inj₁ b = ([] , []) , refl , a , b
  ∈L-soundness (x ∷ s) (r₁ · r₂) (inj₂ (inj₁ x₁)) | inj₁ a | inj₁ b = (x ∷ s , []) , cong (λ l → x ∷ l) (append-rh-[] s) , ∈L-soundness (x ∷ s) r₁ (inj₂ x₁) , b
  ∈L-soundness [] (r₁ · r₂) (inj₂ (inj₂ (inj₁ x))) | inj₁ a | inj₁ b = ([] , []) , refl , a , b
  ∈L-soundness (x ∷ s) (r₁ · r₂) (inj₂ (inj₂ (inj₁ x₁))) | inj₁ a | inj₁ b = ([] , x ∷ s) , refl , a , ∈L-soundness (x ∷ s) r₂ (inj₂ x₁)
  ∈L-soundness s (r₁ · r₂) (inj₂ (inj₂ (inj₂ ((x , y) , n , p , q)))) | inj₁ a | inj₁ b = (x , y) , n , ∈L-soundness x r₁ (inj₂ p) , ∈L-soundness y r₂ (inj₂ q)
  ∈L-soundness s (r₁ · r₂) (inj₂ (inj₁ x)) | inj₁ a | inj₂ b = ([] , s) , refl , a , ∈L-soundness s r₂ (inj₂ x)
  ∈L-soundness s (r₁ · r₂) (inj₂ (inj₁ x)) | inj₂ a | inj₁ b = (s , []) , append-rh-[] s , ∈L-soundness s r₁ (inj₂ x) , b
  ∈L-soundness s (r₁ · r₂) (inj₂ (inj₂ ((x , y) , n , p , q))) | inj₁ a | inj₂ b = (x , y) , n , ∈L-soundness x r₁ (inj₂ p) , ∈L-soundness y r₂ (inj₂ q)
  ∈L-soundness s (r₁ · r₂) (inj₂ (inj₂ ((x , y) , n , p , q))) | inj₂ a | inj₁ b = (x , y) , n , ∈L-soundness x r₁ (inj₂ p) , ∈L-soundness y r₂ (inj₂ q)
  ∈L-soundness s (r₁ · r₂) (inj₂ ((x , y) , n , p , q)) | inj₂ a | inj₂ b = (x , y) , n , ∈L-soundness x r₁ (inj₂ p) , ∈L-soundness y r₂ (inj₂ q)
  ∈L-soundness s (r₁ ⊕ r₂) (inj₂ (inj₁ x)) = inj₁ (∈L-soundness s r₁ (inj₂ x))
  ∈L-soundness s (r₁ ⊕ r₂) (inj₂ (inj₂ x)) = inj₂ (∈L-soundness s r₂ (inj₂ x))
  ∈L-soundness s (r *) (inj₂ (S+ x)) = Cx {s}{s}{[]}{r} (append-rh-[] s) (∈L-soundness s r (inj₂ x)) (Ex refl)
  ∈L-soundness s (r *) (inj₂ (C+ {.s}{s₁}{s₂} a b c)) = Cx a (∈L-soundness s₁ r (inj₂ b)) (∈L-soundness s₂ (r *) (inj₂ c))
  ∈L-soundness s (G r) (inj₂ x) = ∈L-soundness s r (inj₂ x)

  ∈L-completeness : (s : List Char)
                  → (r : RegExp)
                  → s ∈L r
                  → ((δ r ≡ true) × (s ≡ [])) ⊎ (s ∈Lˢ (standardize r))
  ∈L-completeness s ∅ inL = inj₂ inL
  ∈L-completeness s ε inL = inj₁ (refl , inL)
  ∈L-completeness .(x ∷ []) (Lit x) refl = inj₂ refl
  ∈L-completeness s (r₁ · r₂) inL with δ' r₁ | δ' r₂
  ∈L-completeness .(x ++ y) (r₁ · r₂) ((x , y) , refl , b , c) | inj₁ p | inj₁ q with ∈L-completeness x r₁ b | ∈L-completeness y r₂ c
  ∈L-completeness .([] ++ []) (r₁ · r₂) ((.[] , .[]) , refl , b , c) | inj₁ p | inj₁ q | inj₁ (m , refl) | inj₁ (t , refl) = inj₁ (refl , refl)
  ∈L-completeness .([] ++ y) (r₁ · r₂) ((.[] , y) , refl , b , c) | inj₁ p | inj₁ q | inj₁ (m , refl) | inj₂ t = inj₂ (inj₂ (inj₁ t))
  ∈L-completeness .(x ++ []) (r₁ · r₂) ((x , .[]) , refl , b , c) | inj₁ p | inj₁ q | inj₂ m | inj₁ (t , refl) = inj₂ (inj₁ (same-list-language {_}{_}{standardize r₁} (sym (append-rh-[] x)) m))
  ∈L-completeness .(x ++ y) (r₁ · r₂) ((x , y) , refl , b , c) | inj₁ p | inj₁ q | inj₂ m | inj₂ t = inj₂ (inj₂ (inj₂ ((x , y) , refl , m , t)))
  ∈L-completeness s (r₁ · r₂) ((x , y) , a , b , c) | inj₁ p | inj₂ q with ∈L-completeness x r₁ b | ∈L-completeness y r₂ c
  ∈L-completeness .[] (r₁ · r₂) ((.[] , .[]) , refl , b , c) | inj₁ p | inj₂ q | inj₁ (m , refl) | inj₁ (t , refl) = ⊥-elim (q c)
  ∈L-completeness y (r₁ · r₂) ((.[] , .y) , refl , b , c) | inj₁ p | inj₂ q | inj₁ (m , refl) | inj₂ t = inj₂ (inj₁ t)
  ∈L-completeness .(x ++ []) (r₁ · r₂) ((x , .[]) , refl , b , c) | inj₁ p | inj₂ q | inj₂ m | inj₁ (t , refl) = ⊥-elim (q c)
  ∈L-completeness .(x ++ y) (r₁ · r₂) ((x , y) , refl , b , c) | inj₁ p | inj₂ q | inj₂ m | inj₂ t = inj₂ (inj₂ ((x , y) , refl , m , t))
  ∈L-completeness s (r₁ · r₂) ((x , y) , a , b , c) | inj₂ p | inj₁ q with ∈L-completeness x r₁ b | ∈L-completeness y r₂ c
  ∈L-completeness s (r₁ · r₂) ((.[] , .[]) , a , b , c) | inj₂ p | inj₁ q | inj₁ (m , refl) | inj₁ (t , refl) = ⊥-elim (p b)
  ∈L-completeness y (r₁ · r₂) ((.[] , .y) , refl , b , c) | inj₂ p | inj₁ q | inj₁ (m , refl) | inj₂ t = ⊥-elim (p b)
  ∈L-completeness .(x ++ []) (r₁ · r₂) ((x , .[]) , refl , b , c) | inj₂ p | inj₁ q | inj₂ m | inj₁ (t , refl) = inj₂ (inj₁ (same-list-language {_}{_}{standardize r₁}(sym (append-rh-[] x)) m))
  ∈L-completeness s (r₁ · r₂) ((x , y) , a , b , c) | inj₂ p | inj₁ q | inj₂ m | inj₂ t = inj₂ (inj₂ ((x , y) , a , m , t))
  ∈L-completeness s (r₁ · r₂) ((x , y) , a , b , c) | inj₂ p | inj₂ q with ∈L-completeness x r₁ b | ∈L-completeness y r₂ c
  ∈L-completeness .[] (r₁ · r₂) ((.[] , .[]) , refl , b , c) | inj₂ p | inj₂ q | inj₁ (m , refl) | inj₁ (t , refl) = ⊥-elim (p b)
  ∈L-completeness y (r₁ · r₂) ((.[] , .y) , refl , b , c) | inj₂ p | inj₂ q | inj₁ (m , refl) | inj₂ t = ⊥-elim (p b)
  ∈L-completeness .(x ++ []) (r₁ · r₂) ((x , .[]) , refl , b , c) | inj₂ p | inj₂ q | inj₂ m | inj₁ (t , refl) = ⊥-elim (q c)
  ∈L-completeness .(x ++ y) (r₁ · r₂) ((x , y) , refl , b , c) | inj₂ p | inj₂ q | inj₂ m | inj₂ t = inj₂ ((x , y) , refl , m , t)
  ∈L-completeness s (r₁ ⊕ r₂) (inj₁ x) with ∈L-completeness s r₁ x
  ∈L-completeness .[] (r₁ ⊕ r₂) (inj₁ x) | inj₁ (d , refl) with δ' r₁
  ∈L-completeness .[] (r₁ ⊕ r₂) (inj₁ x₁) | inj₁ (d , refl) | inj₁ x = inj₁ (refl , refl)
  ∈L-completeness .[] (_ ⊕ _) (inj₁ _) | inj₁ (() , refl) | inj₂ _
  ∈L-completeness s (r₁ ⊕ r₂) (inj₁ x) | inj₂ q = inj₂ (inj₁ q)
  ∈L-completeness s (r₁ ⊕ r₂) (inj₂ x) with ∈L-completeness s r₂ x
  ∈L-completeness .[] (r₁ ⊕ r₂) (inj₂ x) | inj₁ (d , refl) with δ' r₂
  ∈L-completeness .[] (r₁ ⊕ r₂) (inj₂ x) | inj₁ (refl , refl) | inj₁ a with δ' r₁
  ∈L-completeness .[] (r₁ ⊕ r₂) (inj₂ x₁) | inj₁ (refl , refl) | inj₁ a | inj₁ x = inj₁ (refl , refl)
  ∈L-completeness .[] (r₁ ⊕ r₂) (inj₂ x₁) | inj₁ (refl , refl) | inj₁ a | inj₂ x = inj₁ (refl , refl)
  ∈L-completeness .[] (_ ⊕ _) (inj₂ _) | inj₁ (() , refl) | inj₂ _
  ∈L-completeness s (r₁ ⊕ r₂) (inj₂ x) | inj₂ q = inj₂ (inj₂ q)
  ∈L-completeness .[] (r *) (Ex refl) = inj₁ (refl , refl)
  ∈L-completeness s (r *) (Cx {.s}{s₁}{s₂} x x₁ inL) with ∈L-completeness s₁ r x₁ | ∈L-completeness s₂ (r *) inL
  ∈L-completeness s (r *) (Cx x x₁ inL) | inj₁ (m , refl) | inj₁ (t , refl) = inj₁ (refl , (sym x))
  ∈L-completeness s₂ (r *) (Cx refl x₁ inL) | inj₁ (m , refl) | inj₂ t = inj₂ t
  ∈L-completeness ._ (r *) (Cx {._}{s₁}{.[]} refl x₁ inL) | inj₂ m | inj₁ (refl , refl) = inj₂ (S+ (same-list-language {_}{_}{standardize r} (sym (append-rh-[] s₁)) m))
  ∈L-completeness s (r *) (Cx x x₁ inL) | inj₂ m | inj₂ t = inj₂ (C+ x m t)
  ∈L-completeness s (G r) inL with ∈L-completeness s r inL
  ∈L-completeness s (G r) inL | inj₁ (a , b) with δ' (G r)
  ... | inj₁ x = inj₁ (refl , b)
  ... | inj₂ x = inj₁ (a , b)
  ∈L-completeness s (G r) inL | inj₂ x = inj₂ x
