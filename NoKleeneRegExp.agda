open import lib.Preliminaries

module NoKleeneRegExp where

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
  s ∈L (Lit c) = s == c :: []
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

  equalb : Char → Char → Bool
  equalb x y with Char.equal x y
  ... | Inl _ = True
  ... | Inr _ = False
  -- end of simple stuff

  match : RegExp → List Char → (List Char → Bool) → Bool
  match ∅ _ _ = False
  match ε s k = k s
  match (Lit c) (x :: xs) k = if (equalb x c) then (k xs) else False -- lazy and
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
  append-lh-[] : ∀ {A : Set} → (xs : List A) → (ys : List A) → xs == [] → xs ++ ys == ys
  append-lh-[] .[] ys Refl = Refl

  singleton-append : {A : Set} → {x : A} → {xs ys s : List A} → xs == x :: [] → xs ++ ys == s → x :: ys == s
  singleton-append Refl Refl = Refl

  cons-eq : {A : Set} → {x : A} → {xs ys : List A} → xs == ys → x :: xs == x :: ys
  cons-eq Refl = Refl

  append-assoc : (xs ys zs : List Char) →  (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs)
  append-assoc [] ys zs = Refl
  append-assoc (x :: xs) ys zs = cons-eq (append-assoc xs ys zs)

  same-char : (c : Char) → equalb c c == True
  same-char c with Char.equal c c
  ... | Inl _ = Refl
  ... | Inr f = abort (f Refl)

  eitherIf : {a b : Bool} → Either (a == True) (b == True) → if a then True else b == True
  eitherIf {True} (Inl Refl) = Refl
  eitherIf {True} (Inr Refl) = Refl
  eitherIf {False} (Inl ())
  eitherIf {False} (Inr Refl) = Refl

  lazyOrEq : {a b : Bool} → if a then True else b == True → Either (a == True) (b == True)
  lazyOrEq {True} {True} Refl = Inl Refl
  lazyOrEq {True} {False} Refl = Inl Refl
  lazyOrEq {False} {True} Refl = Inr Refl
  lazyOrEq {False} {False} ()

  match-soundness : (r : RegExp)
                  → (s : List Char)
                  → (k : List Char → Bool)
                  → match r s k == True
                  → Σ (λ p  → ( (fst p) ++ (snd p) == s) × (fst p) ∈L r × (k (snd p) == True))
  match-soundness ∅ s k ()
  match-soundness ε s k m = ([] , s) , Refl , Refl , m
  match-soundness (Lit x) [] k ()
  match-soundness (Lit x) (y :: ys) k m with Char.equal y x
  match-soundness (Lit x) (.x :: ys) k m | Inl Refl = (x :: [] , ys) , Refl , Refl , m
  match-soundness (Lit x) (y :: ys) k () | Inr q
  match-soundness (r₁ · r₂) s k m with match-soundness r₁ s (λ s' → match r₂ s' k) m
  match-soundness (r₁ · r₂) s k m | (xs , ys) , a , b , c with match-soundness r₂ ys k c
  match-soundness (r₁ · r₂) .(xs ++ as ++ bs) k m | (xs , .(as ++ bs)) , Refl , b , c | (as , bs) , Refl , e , f = (xs ++ as , bs) , (! (append-assoc xs as bs) , (((xs , as) , (Refl , (b , e))) , f))
  match-soundness (r₁ ⊕ r₂) s k m with lazyOrEq {match r₁ s k} {match r₂ s k} m
  match-soundness (r₁ ⊕ r₂) s k m | Inl x with match-soundness r₁ s k x
  match-soundness (r₁ ⊕ r₂) s k m | Inl x | (xs , ys) , a , b , c = (xs , ys) , a , Inl b , c
  match-soundness (r₁ ⊕ r₂) s k m | Inr x with match-soundness r₂ s k x
  match-soundness (r₁ ⊕ r₂) s k m | Inr x | (xs , ys) , a , b , c = (xs , ys) , a , Inr b , c


  match-completeness : (r : RegExp)
                     → (s : List Char)
                     → (k : List Char → Bool)
                     → Σ (λ p  → ( (fst p) ++ (snd p) == s) × (fst p) ∈L r × (k (snd p) == True))
                     → match r s k == True
  match-completeness ∅ s k ((xs , ys) , b , c , d) = abort c
  match-completeness ε s k ((xs , ys) , b , c , d) with ys | s | (b ∘ !(append-lh-[] xs ys c))
  ... | p | .p | Refl = d
  match-completeness (Lit x) s k ((xs , ys) , b , c , d)  with !(singleton-append c b)
  match-completeness (Lit x) .(x :: ys) k ((xs , ys) , b , c , d) | Refl with equalb x x | same-char x
  match-completeness (Lit x) .(x :: ys) k ((xs , ys) , b , c , d) | Refl | True | Refl = d
  match-completeness (Lit x) .(x :: ys) k ((xs , ys) , b , c , d) | Refl | False | ()
  match-completeness (r₁ · r₂) s k ((xs , ys) , b , ((ms , ns) , tot , ms∈r₁ , ns∈r₂) , d) with tot | b | append-assoc ms ns ys
  match-completeness (r₁ · r₂) .((ms ++ ns) ++ ys) k ((.(ms ++ ns) , ys) , b , ((ms , ns) , tot , ms∈r₁ , ns∈r₂) , d) | Refl | Refl | p3
    with match-completeness r₂ (ns ++ ys) k ((ns , ys) , (Refl , (ns∈r₂ , d)))
  ... | x = match-completeness r₁ ((ms ++ ns) ++ ys) (λ s' → match r₂ s' k) ((ms , (ns ++ ys)) , (p3 , (ms∈r₁ , x)))
  match-completeness (r₁ ⊕ r₂) s k ((xs , ys) , b , Inl c , d) = eitherIf (Inl (match-completeness r₁ s k ((xs , ys) , b , c , d)))
  match-completeness (r₁ ⊕ r₂) s k ((xs , ys) , b , Inr c , d) = eitherIf {match r₁ s k} {match r₂ s k} (Inr (match-completeness r₂ s k ((xs , ys) , b , c , d)))
