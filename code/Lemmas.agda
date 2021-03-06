open import Definitions

module Lemmas where

  open import Category.Monad
  open import Function
  open import Data.Bool
  open import Data.Char
  open import Data.Empty
  open import Data.List
  open import Data.Maybe
  import Data.Maybe.Categorical
  open import Data.Product
  open import Data.Unit
  open import Data.Sum
  open import Induction.WellFounded
  open import Relation.Nullary
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary.Decidable
  import Agda.Primitive

  empty-append : {xs ys : List Char} → xs ++ ys ≡ [] → (xs ≡ []) × (ys ≡ [])
  empty-append {[]} {[]} refl = refl , refl
  empty-append {[]} {_ ∷ _} ()
  empty-append {_ ∷ _} {[]} ()
  empty-append {_ ∷ _} {_ ∷ _} ()

  {- Transitivity of suffixes -}
  suffix-trans : {A : Set} → {xs ys zs : List A} → Suffix xs ys → Suffix ys zs → Suffix xs zs
  suffix-trans s1 Stop = Drop s1
  suffix-trans s1 (Drop s2) = Drop (suffix-trans s1 s2)

  {- Prove that you can make a recursion permission for any suffix of [] -}
  perm-suffix-[] : {A : Set} (xs : List A) → Suffix xs [] → Acc Suffix xs
  perm-suffix-[] _ ()

  perm-suffix : {A : Set} {y : A} {xs ys : List A} → Suffix xs (y ∷ ys) → Acc Suffix ys → Acc Suffix xs
  perm-suffix Stop rec = rec
  perm-suffix (Drop s) (acc perm) = perm _ s

  {- Using perm-suffix-[] and perm-suffix, make a recursion permission for any list. -}
  well-founded : {A : Set} (ys : List A) → Acc Suffix ys
  well-founded [] = acc perm-suffix-[]
  well-founded (y ∷ ys) = acc (λ xs suff → perm-suffix suff (well-founded ys))

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

  {- Moves logical or to or implementation. -}
  either-if : {a b : Bool} → (a ≡ true) ⊎ (b ≡ true) → (a ∨ b) ≡ true
  either-if {true} x = refl
  either-if {false} {true} x = refl
  either-if {false} {false} (inj₁ ())
  either-if {false} {false} (inj₂ ())

  {- Moves or implementation to logical or. -}
  or-eq : {a b : Bool} → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
  or-eq {true} refl = inj₁ refl
  or-eq {false} {true} refl = inj₂ refl
  or-eq {false} {false} ()

  bool-eq : (a : Bool) → (a ≡ true) ⊎ (a ≡ false)
  bool-eq true = inj₁ refl
  bool-eq false = inj₂ refl

  non-empty : ∀ {r} → ([] ∈Lˢ r → ⊥)
  non-empty {∅ˢ} ()
  non-empty {Litˢ x} ()
  non-empty {r₁ ·ˢ r₂} (∈ˢ· {s}{xs}{ys} eq inL inL') with empty-append {xs} {ys} eq
  non-empty {r₁ ·ˢ r₂} (∈ˢ· {.[]} {.[]} {ys} eq inL inL') | refl , _ = non-empty inL
  non-empty {r₁ ⊕ˢ r₂} (∈ˢ⊕₁ inL) = non-empty inL
  non-empty {r₁ ⊕ˢ r₂} (∈ˢ⊕₂ inL) = non-empty inL
  non-empty {r ⁺ˢ} (∈ˢS+ inL) = non-empty inL
  non-empty {r ⁺ˢ} (∈ˢC+ {s}{xs}{ys} eq inL _) with empty-append {xs} {ys} eq
  non-empty {r ⁺ˢ} (∈ˢC+ {.[]} {.[]} {ys} eq inL _) | refl , _ = non-empty inL

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

  replace-left : {as bs xs ys s' : List Char} → as ++ bs ≡ xs → xs ++ ys ≡ s' → as ++ bs ++ ys ≡ s'
  replace-left {as} {bs} .{as ++ bs} {ys} .{(as ++ bs) ++ ys} refl refl = append-assoc as bs ys

  replace-right : {xs ys as bs s : List Char} → as ++ bs ≡ ys → xs ++ ys ≡ s → (xs ++ as) ++ bs ≡ s
  replace-right {xs} .{as ++ bs} {as} {bs} .{xs ++ as ++ bs} refl refl = sym (append-assoc xs as bs)

  is-just-lemma : ∀ {A} → {x : Maybe A} → isJust x → is-just x ≡ true
  is-just-lemma {x = just x} m = refl
  is-just-lemma {x = nothing} ()

  is-just-preserve : ∀ {A B} → {x : Maybe A} → {f : A → B} → isJust x → isJust (Data.Maybe.map f x)
  is-just-preserve {x = just _} m = tt
  is-just-preserve {x = nothing} ()

  ∈Lᵏ-empty-continuation : {r : StdRegExp} {s : List Char}
                         → s ∈Lᵏ (r ∷ [])
                         → s ∈Lˢ r
  ∈Lᵏ-empty-continuation {r} {s} (cons p .[] eq inL emp) = eq-replace ((cong₂ _∈Lˢ_ (trans (sym (append-rh-[] p)) eq) refl)) inL

  empty-continuation : ∀ {p' s' s'' r} → (p' ++ s'' ≡ s') → (p' ∈Lˢ r) → Maybe (s' ∈Lˢ r)
  empty-continuation {p'}{s'}{s'' = []} eq inL =  just (eq-replace (cong₂ _∈Lˢ_ (trans (sym (append-rh-[] p')) eq) refl ) inL)
  empty-continuation {s'' = x ∷ s''} eq inL = nothing

  suffix-after-∈Lˢ : ∀ {p s' s r} → (p ++ s' ≡ s) → (p ∈Lˢ r) → Suffix s' s
  suffix-after-∈Lˢ eq inL = eq-replace (cong₂ Suffix refl eq) (append-suffix2 inL)

  open RawMonadPlus {Agda.Primitive.lzero} Data.Maybe.Categorical.monadPlus renaming (∅ to fail)
  or-just : ∀ {A} {a b : Maybe A} → (isJust a) ⊎ (isJust b) → isJust (a ∣ b)
  or-just {a = just x} m = tt
  or-just {a = nothing} (inj₁ ())
  or-just {a = nothing} (inj₂ y) = y

  {- uniqueness of identity -}
  uip : ∀ {l : Agda.Primitive.Level} {A : Set l} {x : A} (p : x ≡ x) → (p ≡ refl)
  uip refl = refl
