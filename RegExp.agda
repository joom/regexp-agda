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

  infix 1 _*
  infixr 2 _·_
  infixr 3 _⊕_
  {-
    Example regexp:
      ((Lit 'a' ⊕ Lit 'b') · (Lit 'c')) accepts "ac"
      (∅ *) accepts ""
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
  -- end of simple stuff

  δ : RegExp → RegExp
  δ ∅ = ∅
  δ ε = ε
  δ (Lit x) = ∅
  δ (r₁ · r₂) with δ r₁ | δ r₂
  ... | ∅ | _ = ∅
  ... | _ | ∅ = ∅
  ... | _ | _ = ε
  δ (r₁ ⊕ r₂) with δ r₁ | δ r₂
  ... | ε | _ = ε
  ... | _ | ε = ε
  ... | _ | _ = ∅
  δ(r *) = ε

  standardize : RegExp → RegExp
  standardize ∅ = ∅
  standardize ε = ∅
  standardize (Lit x) = Lit x
  standardize (r₁ · r₂) = (δ r₁ · standardize r₂) ⊕ (standardize r₁ · δ r₂) ⊕ (standardize r₁ · standardize r₂)
  standardize (r₁ ⊕ r₂) = standardize r₁ ⊕ standardize r₂
  standardize (r *) = standardize r · (standardize r)*

  -- match : RegExp → List Char → (List Char → Bool) → Bool
  -- match ∅ _ _ = False
  -- match ε s k = k s
  -- match (Lit c) (x :: xs) k = if (equalb x c) then (k xs) else False -- lazy and
  -- match (Lit _) _ _ = False
  -- match (r₁ · r₂) s k = match r₁ s (λ s' → match r₂ s' k)
  -- match (r₁ ⊕ r₂) s k = if (match r₁ s k) then True else (match r₂ s k) -- lazy or
  -- match (r *) s k = if (k s) then True else (match r s (λ s' → match (r *) s' k)) -- lazy or

  -- _accepts_ : RegExp → String.String → Bool
  -- r accepts s = match (standardize r) (String.toList s) null
