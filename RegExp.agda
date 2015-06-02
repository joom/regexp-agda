open import lib.Preliminaries

module RegExp where

  open List
  {- Note: for this code, we define a String to be a list of characters -}
  String = List Char

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
  s ∈L ε = s == []
  s ∈L (Lit c) = s == 'c' :: []
  s ∈L (r₁ ⊕ r₂) = Either (s ∈L r₁) (s ∈L r₂)
  s ∈L (r₁ · r₂) = {!!}
