open import lib.Preliminaries

module RegExp where

  open List

  data RegExp : Set where
    ∅ : RegExp  -- empty set (type \emptyset)
    ε : RegExp   -- empty string (type \epsilon)
    Lit : Char → RegExp -- literal character
    _·_ : RegExp → RegExp → RegExp -- concatenation (type \cdot)
    _⊕_ : RegExp → RegExp → RegExp -- alternation/set union (type \oplus)
  --   _* : RegExp → RegExp -- Kleene star

  -- infix 1 _*
  infixr 2 _·_
  infixr 3 _⊕_
  {-
    Example regexp:
      ((Lit 'a' ⊕ Lit 'b') · (Lit 'c')) accepts "ac"
      (∅ *) accepts ""
  -}


  -- Shows a string accepted by the language of a regexp. Type "\in L".
  _∈L_ : List Char → RegExp → Set
  _ ∈L ∅ = Void
  s ∈L ε = s == []
  s ∈L (Lit c) = s == 'c' :: []
  s ∈L (r₁ ⊕ r₂) = Either (s ∈L r₁) (s ∈L r₂)
  s ∈L (r₁ · r₂) = Σ (λ p  → ((fst p) ++ (snd p) == s) × (fst p) ∈L r₁ × (snd p) ∈L r₂)
  -- s ∈L (r *) = {! Either (s ∈L ε) (s ∈L (r · r *))!}

  -- I can't believe these are not in the preliminaries file
  -- simple stuff
  if_then_else_ : {A : Set} → Bool → A → A → A
  if True then x else _ = x
  if False then _ else y = y

  null : {A : Set} → List A → Bool
  null [] = True
  null _ = False
  -- end of simple stuff

  match : RegExp → List Char → (List Char → Bool) → Bool
  match ∅ _ _ = False
  match ε s k = k s
  match (Lit c) (x :: xs) k = if (Char.equalb x c) then (k xs) else False -- lazy and
  match (Lit _) _ _ = False
  match (r₁ · r₂) s k = match r₁ s (λ s' → match r₂ s' k)
  match (r₁ ⊕ r₂) s k = if (match r₁ s k) then True else (match r₂ s k) -- lazy or
  -- match (r *) s k = if (k s) then True else (match r s (λ s' → match (r *) s' k)) -- lazy or

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
  -- δ(r *) = ε

  standardize : RegExp → RegExp
  standardize ∅ = ∅
  standardize ε = ∅
  standardize (Lit x) = Lit x
  standardize (r₁ · r₂) = (δ r₁ · standardize r₂) ⊕ (standardize r₁ · δ r₂) ⊕ (standardize r₁ · standardize r₂)
  standardize (r₁ ⊕ r₂) = standardize r₁ ⊕ standardize r₂
  -- standardize (r *) = standardize r · (standardize r)*

  _accepts_ : RegExp → String.String → Bool
  r accepts s = match (standardize r) (String.toList s) null

  -- Proofs

  sym : {A : Set} →  {x y : A} → (x == y) → y == x
  sym {_} {y} {.y} Refl = Refl

  append-lh-[] : ∀ {A : Set} → (xs : List A) → (ys : List A) → xs == [] → xs ++ ys == ys
  append-lh-[] .[] ys Refl = Refl

  match-soundness : (r : RegExp)
                  → (s : List Char)
                  → (k : List Char → Bool)
                  → {!!}
                  → Σ (λ p  → ( (fst p) ++ (snd p) == s) × (fst p) ∈L r × (k (snd p) == True))
  match-soundness r s k = {!!}

  match-completeness : (r : RegExp)
                     → (s : List Char)
                     → (k : List Char → Bool)
                     → Σ (λ p  → ( (fst p) ++ (snd p) == s) × (fst p) ∈L r × (k (snd p) == True))
                     → match r s k == True
  match-completeness ∅ s k ((xs , ys) , b , c , d) = abort c
  match-completeness ε s k ((xs , ys) , b , c , d) with ys | s | (b ∘ sym (append-lh-[] xs ys c))
  ... | p | .p | Refl = d
  match-completeness (Lit x) s k ((xs , ys) , b , c , d) = {!!}
  match-completeness (r₁ · r₂) s k ((xs , ys) , b , c , d) = {!!}
  match-completeness (r₁ ⊕ r₂) s k ((xs , ys) , b , c , d) = {!!}
