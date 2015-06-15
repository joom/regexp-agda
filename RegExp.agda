open import lib.Preliminaries

module RegExp where

  open List

  data RegExp : Set where
    ∅ : RegExp  -- empty set (type \emptyset)
    ε : RegExp   -- empty string (type \epsilon)
    Lit : Char → RegExp -- literal character
    _·_ : RegExp → RegExp → RegExp -- concatenation (type \cdot)
    _⊕_ : RegExp → RegExp → RegExp -- alternation/set union (type \oplus)
    _* : RegExp → RegExp -- Kleene star

  data Δ : Set where
    ∅ᵈ : Δ
    εᵈ : Δ

  demote-Δ : Δ → RegExp
  demote-Δ ∅ᵈ = ∅
  demote-Δ εᵈ = ε

  data StdRegExp : Set where
    ∅ˢ : StdRegExp
    Litˢ : (c : Char) → StdRegExp
    _·ˢ_ : Δ → StdRegExp → StdRegExp
    _ˢ·_ : StdRegExp → Δ → StdRegExp
    _ˢ·ˢ_ : StdRegExp → StdRegExp → StdRegExp
    _⊕ˢ_ : StdRegExp → StdRegExp → StdRegExp
    _*ˢ : StdRegExp → StdRegExp

  demote-std : StdRegExp → RegExp
  demote-std ∅ˢ = ∅
  demote-std (Litˢ c) = Lit c
  demote-std (d ·ˢ r) = demote-Δ d · demote-std r
  demote-std (r ˢ· d) = demote-std r · demote-Δ d
  demote-std (r₁ ˢ·ˢ r₂) = demote-std r₁ · demote-std r₂
  demote-std (r₁ ⊕ˢ r₂) = demote-std r₁ ⊕ demote-std r₂
  demote-std (r *ˢ) = (demote-std r) *

  infix 1 _*
  infix 1 _*ˢ
  infixr 2 _·_
  infixr 2 _ˢ·_
  infixr 2 _·ˢ_
  infixr 2 _ˢ·ˢ_
  infixr 3 _⊕_
  infixr 3 _⊕ˢ_
  {-
    Example regexp:
      ((Lit 'a' ⊕ Lit 'b') · (Lit 'c')) accepts "ac"
      (∅ *) accepts ""
      ((Lit 'd') *) accepts "ddd"
      ((Lit 'd') *) accepts ""
  -}

  -- I can't believe these are not in the preliminaries file
  -- simple stuff
  if_then_else_ : {A : Set} → Bool → A → A → A
  if True then x else _ = x
  if False then _ else y = y

  null : {A : Set} → List A → Bool
  null [] = True
  null _ = False

  equalb : Char → Char → Bool
  equalb x y with Char.equal x y
  ... | Inl _ = True
  ... | Inr _ = False

  {- Suffix xs ys means that xs is a suffix of ys -}

  data Suffix {A : Set} : List A → List A → Set where
    Stop : ∀ {x xs} → Suffix xs (x :: xs)
    Drop : ∀ {y xs ys} → Suffix xs ys → Suffix xs (y :: ys)

  suffix-trans : {A : Set} → {xs ys zs : List A} → Suffix xs ys → Suffix ys zs → Suffix xs zs
  suffix-trans s1 Stop = Drop s1
  suffix-trans s1 (Drop s2) = Drop (suffix-trans s1 s2)

  -- end of simple stuff

  δ : RegExp → Δ
  δ ∅ = ∅ᵈ
  δ ε = εᵈ
  δ (Lit x) = ∅ᵈ
  δ (r₁ · r₂) with δ r₁ | δ r₂
  ... | ∅ᵈ | _ = ∅ᵈ
  ... | _ | ∅ᵈ = ∅ᵈ
  ... | _ | _ = εᵈ
  δ (r₁ ⊕ r₂) with δ r₁ | δ r₂
  ... | εᵈ | _ = εᵈ
  ... | _ | εᵈ = εᵈ
  ... | _ | _ = ∅ᵈ
  δ(r *) = εᵈ
  -- standardize : RegExp → RegExp
  -- standardize ∅ = ∅
  -- standardize ε = ∅
  -- standardize (Lit x) = Lit x
  -- standardize (r₁ · r₂) = (δ r₁ · standardize r₂) ⊕ (standardize r₁ · δ r₂) ⊕ (standardize r₁ · standardize r₂)
  -- standardize (r₁ ⊕ r₂) = standardize r₁ ⊕ standardize r₂
  -- standardize (r *) = standardize r · (standardize r)*

  standardize : RegExp → StdRegExp
  standardize ∅ = ∅ˢ
  standardize ε = ∅ˢ
  standardize (Lit x) = Litˢ x
  standardize (r₁ · r₂) with standardize r₁ | standardize r₂
  ... | x₁ | x₂ =  (δ r₁ ·ˢ x₁) ⊕ˢ (x₁ ˢ· δ r₂) ⊕ˢ (x₁ ˢ·ˢ x₂)
  standardize (r₁ ⊕ r₂) = standardize r₁ ⊕ˢ standardize r₂
  standardize (r *) with standardize r
  ... | x = x ˢ·ˢ (x *ˢ)

  data RecursionPermission {A : Set} : List A → Set where
    CanRec : {ys : List A} → ((xs : List A) → Suffix xs ys → RecursionPermission xs) → RecursionPermission ys

  {- Prove that you can make a recursion permission for any suffix of [] -}
  lemma1 : {A : Set} (xs : List A) → Suffix xs [] → RecursionPermission xs
  lemma1 _ ()

  lemma2 : {A : Set} {y : A} {xs ys : List A} → Suffix xs (y :: ys) → RecursionPermission ys → RecursionPermission xs
  lemma2 Stop rec = rec
  lemma2 (Drop s) (CanRec perm) = perm _ s

  {- Using lemma1 and lemma2, make a recursion permission for any list. -}
  well-founded : {A : Set} (ys : List A) → RecursionPermission ys
  well-founded [] = CanRec lemma1
  well-founded (y :: ys) = CanRec (\ xs suff → lemma2 suff (well-founded ys))

  -- Matching algorithm
  match : StdRegExp → (s : List Char) → (Σ (λ s' → Suffix s' s) → Bool) → RecursionPermission s → Bool
  match ∅ˢ s k _ = False
  match (Litˢ _) [] _ _ = False
  match (Litˢ c) (x :: xs) k _ = if (equalb x c) then (k (xs , Stop)) else False
  match (∅ᵈ ·ˢ r) s k _ = False
  match (εᵈ ·ˢ r) s k perm = match r s k perm
  match (r ˢ· ∅ᵈ) s k _ = False
  match (r ˢ· εᵈ) s k perm = match r s k perm
  match (r₁ ˢ·ˢ r₂) s k (CanRec f) = match r₁ s (λ { (s' , sf) → match r₂ s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)
  match (r₁ ⊕ˢ r₂) s k perm = if match r₁ s k perm then True else match r₂ s k perm
  match (r *ˢ) s k (CanRec f) = if null s then True else match r s (λ { (s' , sf) → match (r *ˢ) s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf)}) (CanRec f) -- shouldn't use null, use k

  match-plus : Δ × StdRegExp → (s : List Char) → (Σ (λ s' → Suffix s' s) → Bool) → RecursionPermission s → Bool
  match-plus (∅ᵈ , r) s k perm = match r s k perm
  match-plus (εᵈ , r) s k perm = if null s then True else match r s k perm -- shouldn't use null, use k

  _accepts_ : RegExp → String.String → Bool
  r accepts s = match-plus (δ r , standardize r) l (λ { (s , sf) → null s }) (well-founded l)
    where l = String.toList s
