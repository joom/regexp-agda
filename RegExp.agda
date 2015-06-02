open import lib.Preliminaries

module RegExp where

  open String

  data RegExp : Set where
    ∅ : RegExp  -- empty set (type \emptyset)
    ε : RegExp   -- empty string (type \epsilon)
    Lit : Char → RegExp -- literal character
    _·_ : RegExp → RegExp → RegExp -- concatenation (type \cdot)
    _⊕_ : RegExp → RegExp → RegExp -- alternation/set union (type \oplus)

    -- Left out for now because of termination issues
    -- _* : RegExp → RegExp -- Kleene star

  -- Shows a string accepted by the language of a regexp. Type "\in L".
  _∈L_ : String → RegExp → Set
  _ ∈L ∅ = Void
  s ∈L ε = s == ""
  s ∈L (Lit c) = s == "c"
  s ∈L (r₁ ⊕ r₂) = Either (s ∈L r₁) (s ∈L r₂)
  s ∈L (r₁ · r₂) = Σ {_} {_} {String × String} (λ p  → (append (fst p) (snd p) == s) × (fst p) ∈L r₁ × (snd p) ∈L r₂)

  -- I can't believe this is not in the preliminaries
  _or_ : Bool → Bool → Bool
  True or _ = True
  _ or True = True
  _ or _ = False

  match : RegExp → String → (String → Bool) → Bool
  match ∅ _ _ = False
  match ε s _ = equal s ""
  match (Lit c) s _ with toList s
  ... | (x :: []) = Char.equalb x c
  ... | _ = False
  match (r₁ · r₂) s k = match r₁ s (λ s' → match r₂ s' k)
  match (r₁ ⊕ r₂) s k = (match r₁ s k) or (match r₂ s k)
