open import lib.Preliminaries

module RegExp where

  open List

  -- Definitions

  data RegExp : Set where
    ∅ : RegExp  -- empty set (type \emptyset)
    ε : RegExp   -- empty string (type \epsilon)
    Lit : Char → RegExp -- literal character
    _·_ : RegExp → RegExp → RegExp -- concatenation (type \cdot)
    _⊕_ : RegExp → RegExp → RegExp -- alternation/set union (type \oplus)
    _* : RegExp → RegExp -- Kleene star
    G : RegExp → RegExp

  {- The regular expressions that do not accept empty string. -}
  data StdRegExp : Set where
    ∅ˢ : StdRegExp
    Litˢ : Char → StdRegExp
    _·ˢ_ : StdRegExp → StdRegExp → StdRegExp
    _⊕ˢ_ : StdRegExp → StdRegExp → StdRegExp
    _⁺ˢ : StdRegExp → StdRegExp -- accepts one or more of the given StdRegExp
    Gˢ : StdRegExp → StdRegExp

  infix 1 _* _⁺ˢ
  infixr 2 _·_ _·ˢ_
  infixr 3 _⊕_ _⊕ˢ_

  {-
    Example regexp:
      ((Lit 'a' ⊕ Lit 'b') · (Lit 'c')) accepts "ac"
      (∅ *) accepts ""
      ((Lit 'd') *) accepts "ddd"
      ((Lit 'd') *) accepts ""
      (Lit '<' · (Lit '0' *) · Lit '>') accepts "<>"
      (Lit '<' · (Lit '0' *) · Lit '>') accepts "<00>"
  -}

  -- Shows a string accepted by the language of a regexp. Type "\in L".
  _∈L_ : List Char → RegExp → Set
  data _∈Lˣ_ : List Char → RegExp → Set

  _ ∈L ∅ = Void
  s ∈L ε = s == []
  s ∈L (Lit c) = s == c :: []
  s ∈L (r₁ ⊕ r₂) = Either (s ∈L r₁) (s ∈L r₂)
  s ∈L (r₁ · r₂) = Σ (λ { (p , q) → (p ++ q == s) × (p ∈L r₁) × (q ∈L r₂) })
  s ∈L (r *) = s ∈Lˣ r
  s ∈L (G r) = s ∈L r

  data _∈Lˣ_ where
    Ex : ∀ {s r} → s == [] → s ∈Lˣ r
    Cx : ∀ {s s₁ s₂ r} → s₁ ++ s₂ == s → s₁ ∈L r → s₂ ∈Lˣ r → s ∈Lˣ r

  _∈Lˢ_ : List Char → StdRegExp → Set
  data _∈L⁺_ : List Char → StdRegExp → Set

  _ ∈Lˢ ∅ˢ = Void
  s ∈Lˢ (Litˢ c) = s == c :: []
  s ∈Lˢ (r₁ ⊕ˢ r₂) = Either (s ∈Lˢ r₁) (s ∈Lˢ r₂)
  s ∈Lˢ (r₁ ·ˢ r₂) = Σ (λ { (p , q)  → (p ++ q == s) × (p ∈Lˢ r₁) × (q ∈Lˢ r₂) })
  s ∈Lˢ (r ⁺ˢ) = s ∈L⁺ r
  s ∈Lˢ (Gˢ r) = s ∈Lˢ r

  data _∈L⁺_ where
    S+ : ∀ {s r} → s ∈Lˢ r → s ∈L⁺ r
    C+ : ∀ {s s₁ s₂ r} → s₁ ++ s₂ == s → s₁ ∈Lˢ r → s₂ ∈L⁺ r → s ∈L⁺ r

  -- Functions & lemmas used in the definition of match

  {- Our boolean char equality function that isn't directly primitive. -}
  equalb : Char → Char → Bool
  equalb x y with Char.equal x y
  ... | Inl _ = True
  ... | Inr _ = False

  {- Suffix xs ys means that xs is a suffix of ys -}
  data Suffix {A : Set} : List A → List A → Set where
    Stop : ∀ {x xs} → Suffix xs (x :: xs)
    Drop : ∀ {y xs ys} → Suffix xs ys → Suffix xs (y :: ys)

  {- Transitivity of suffixes -}
  suffix-trans : {A : Set} → {xs ys zs : List A} → Suffix xs ys → Suffix ys zs → Suffix xs zs
  suffix-trans s1 Stop = Drop s1
  suffix-trans s1 (Drop s2) = Drop (suffix-trans s1 s2)

  {- A type to make it obvious to Agda that our function will terminate. -}
  data RecursionPermission {A : Set} : List A → Set where
    CanRec : {ys : List A} → ((xs : List A) → Suffix xs ys → RecursionPermission xs) → RecursionPermission ys

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

  -- Matching algorithm
  match : StdRegExp → (s : List Char) → (Σ (λ s' → Suffix s' s) → Bool) → RecursionPermission s → Bool
  match ∅ˢ s k _ = False
  match (Litˢ _) [] _ _ = False
  match (Litˢ c) (x :: xs) k _ = if (equalb x c) then (k (xs , Stop)) else False
  match (r₁ ·ˢ r₂) s k (CanRec f) = match r₁ s (λ { (s' , sf) → match r₂ s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)
  match (r₁ ⊕ˢ r₂) s k perm = if match r₁ s k perm then True else match r₂ s k perm
  match (r ⁺ˢ) s k (CanRec f) = if match r s k (CanRec f) then True else match r s (λ { (s' , sf) → match (r ⁺ˢ) s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)
  match (Gˢ r) s k perm = match r s k perm

  -- Lemmas

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

  empty-append : {xs ys : List Char} → xs ++ ys == [] → (xs == []) × (ys == [])
  empty-append {[]} {[]} Refl = Refl , Refl
  empty-append {[]} {_ :: _} ()
  empty-append {_ :: _} {[]} ()
  empty-append {_ :: _} {_ :: _} ()

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

  -- Overall regular expression matching functions & proofs.

  empty-append-δ : ∀ {x y r} → x ++ y == [] → Either (x ∈L r) (y ∈L r) → ([] ∈L r → Void) → Void
  empty-append-δ {x}{y}{r} eq inL f with empty-append {x}{y} eq
  empty-append-δ eq (Inl inL) f | Refl , Refl = f inL
  empty-append-δ eq (Inr inL) f | Refl , Refl = f inL

  -- Checks if a given regexp accepts empty string.
  δ' : (r : RegExp) → Either ([] ∈L r) ([] ∈L r → Void)
  δ' ∅ = Inr (λ ())
  δ' ε = Inl Refl
  δ' (Lit x) = Inr (λ ())
  δ' (r₁ · r₂) with δ' r₁ | δ' r₂
  ... | Inr p | _ = Inr (λ {((x , y) , (a , (b , _))) → empty-append-δ {x}{y}{r₁} a (Inl b) p})
  ... | _ | Inr q = Inr (λ {((x , y) , (a , (_ , c))) → empty-append-δ {x}{y}{r₂} a (Inr c) q})
  ... | Inl p | Inl q = Inl (([] , []) , Refl , p , q)
  δ' (r₁ ⊕ r₂) with δ' r₁ | δ' r₂
  ... | (Inl p) | _ = Inl (Inl p)
  ... | _ | (Inl q) = Inl (Inr q)
  ... | (Inr p) | (Inr q) = Inr (sub-lemma p q)
    where sub-lemma : ∀ {a b} → (a → Void) → (b → Void) → Either a b → Void
          sub-lemma f _ (Inl a) = f a
          sub-lemma _ g (Inr b) = g b
  δ' (r *) = Inl (Ex Refl)
  δ' (G r) = δ' r

  -- Checks if a given regexp accepts empty string. True, if it accepts ε, False otherwise.
  δ : RegExp → Bool
  δ r with δ' r
  ... | Inl _ = True
  ... | Inr _ = False

  standardize : RegExp → StdRegExp
  standardize ∅ = ∅ˢ
  standardize ε = ∅ˢ
  standardize (Lit x) = Litˢ x
  standardize (r₁ · r₂) with standardize r₁ | standardize r₂ | δ r₁ | δ r₂
  ... | x₁ | x₂ | False | False = x₁ ·ˢ x₂
  ... | x₁ | x₂ | False | True = x₁ ⊕ˢ (x₁ ·ˢ x₂)
  ... | x₁ | x₂ | True | False = x₂ ⊕ˢ (x₁ ·ˢ x₂)
  ... | x₁ | x₂ | True | True = x₁ ⊕ˢ x₂ ⊕ˢ (x₁ ·ˢ x₂)
  standardize (r₁ ⊕ r₂) = standardize r₁ ⊕ˢ standardize r₂
  standardize (r *) = x ⁺ˢ
    where x = standardize r
  standardize (G r) = Gˢ (standardize r)

  _accepts_ : RegExp → String.String → Bool
  r accepts s = match-plus (δ r , standardize r) l (λ { (s , sf) → null s }) (well-founded l)
    where l = String.toList s
          match-plus : Bool × StdRegExp → (s : List Char) → (Σ (λ s' → Suffix s' s) → Bool) → RecursionPermission s → Bool
          match-plus (False , r) s k perm = match r s k perm
          match-plus (True , r) s k perm = if null s then True else match r s k perm

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

  -- Using groups

  open Maybe

  eq-pred : {A : Set} → (a : A) → (f : A →  Bool) → Either (f a == True) (f a == False)
  eq-pred {_} a f with f a
  ... | True = Inl Refl
  ... | False = Inr Refl

  eitherToBool : ∀ {A B} → Either A B → Bool
  eitherToBool (Inl _) = False
  eitherToBool (Inr _) = True

  -- Doing the matching and soundness proof at the same time.
  intrinsic : (r : StdRegExp)
            → (s : List Char)
            → (k : Σ (λ s' → Suffix s' s) → Bool)
            → (perm : RecursionPermission s)
            → Either Unit (Σ (λ { (p , (s' , sf)) → (p ++ s' == s) × (p ∈Lˢ r) × (k (s' , sf) == True)}))
  intrinsic ∅ˢ s k perm = Inl <>
  intrinsic (Litˢ _) [] _ _ = Inl <>
  intrinsic (Litˢ c) (x :: xs) k perm with Char.equal x c
  ... | Inr q = Inl <>
  ... | Inl p with eq-pred (xs , Stop) k
  ...            | Inr _ = Inl <>
  ...            | Inl w = Inr ((x :: [] , xs , Stop) , Refl , ap (λ y → y :: []) p , w)
  intrinsic (r₁ ·ˢ r₂) s k (CanRec f)
    with intrinsic r₁ s (λ { (s' , sf) → eitherToBool (intrinsic r₂ s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf)}) (f s' sf)) }) (CanRec f)
  ... | Inl <> = Inl <>
  ... | Inr ((xs , ys , sf) , a , b , c) with intrinsic r₂ ys (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf)}) (f ys sf)
  ...      | Inl <> = Inl <>
  intrinsic (r₁ ·ˢ r₂) .(xs ++ as ++ bs) k (CanRec f) | Inr ((xs , .(as ++ bs) , sf) , Refl , b , c) | Inr ((as , bs , sf') , Refl , q , w) =
      Inr ((xs ++ as , bs , suffix-trans sf' sf) , ! (append-assoc xs as bs) , ((xs , as) , Refl , b , q) , w)
  intrinsic (r₁ ⊕ˢ r₂) s k perm with intrinsic r₁ s k perm
  ... | Inr ((xs , ys , sf) , a , b , c) = Inr ((xs , ys , sf) , a , Inl b , c)
  ... | Inl <> with intrinsic r₂ s k perm
  ...             | Inr ((xs , ys , sf) , a , b , c) = Inr ((xs , ys , sf) , a , Inr b , c)
  ...             | Inl <> = Inl <>
  intrinsic (r ⁺ˢ) s k (CanRec f) with intrinsic r s k (CanRec f)
  ... | Inr ((xs , ys , sf) , a , b , c) = Inr ((xs , ys , sf) , a , S+ b , c)
  ... | Inl <> with intrinsic r s (λ {(s' , sf) → eitherToBool (intrinsic (r ⁺ˢ) s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf)) }) (CanRec f)
  ...       | Inl <> = Inl <>
  intrinsic (r ⁺ˢ) .(as ++ bs) k (CanRec f) | Inl <> | Inr ((as , bs , sf') , Refl , q , w)
    with intrinsic (r ⁺ˢ) bs (λ {(s' , sf'') → k (s' , suffix-trans sf'' sf')}) (f bs sf')
  ... | Inl <> = Inl <>
  intrinsic (r ⁺ˢ) .(as ++ xs ++ ys) k (CanRec f) | Inl <> | Inr ((as , .(xs ++ ys) , sf') , Refl , q , w) | Inr ((xs , ys , sf) , Refl , b , c) =
      Inr ((as ++ xs , ys , suffix-trans sf sf') , ! (append-assoc as xs ys) , C+ Refl q b , c)
  intrinsic (Gˢ r) s k perm = intrinsic r s k perm

  extract : {r : RegExp} → {xs : List Char} → xs ∈L r → List (List Char)
  extract {∅} ()
  extract {ε} Refl = []
  extract {Lit x} Refl = []
  extract {r₁ · r₂}{xs} ((as , bs) , a , b , c) = extract {r₁}{as} b ++ extract {r₂}{bs} c
  extract {r₁ ⊕ r₂}{xs} (Inl x) = extract {r₁}{xs} x
  extract {r₁ ⊕ r₂}{xs} (Inr x) = extract {r₂}{xs} x
  extract {r *} (Ex Refl) = []
  extract {r *} (Cx {s}{s₁}{s₂} x x₁ inL) = extract {r}{s₁} x₁ ++ extract {r *}{s₂} inL
  extract {G r}{xs} inL = xs :: extract {r}{xs} inL

  null-lemma : {ys : List Char} → null ys == True → ys == []
  null-lemma {[]} eq = Refl
  null-lemma {_ :: _} ()

  inL-intrinsic : (r : RegExp)
                → (s : String.String)
                → Either Unit ((String.toList s) ∈L r)
  inL-intrinsic r s with String.toList s | δ' r
  inL-intrinsic r s | [] | Inl x = Inr x
  inL-intrinsic r s | l | d with intrinsic (standardize r) l (λ { (s' , sf) → null s' }) (well-founded l)
  inL-intrinsic r s | l | d | Inl <> = Inl <>
  inL-intrinsic r s | .(xs ++ ys) | d | Inr ((xs , ys , sf) , Refl , b , c) with null-lemma {ys} c
  inL-intrinsic r s | .(xs ++ []) | d | Inr ((xs , .[] , sf) , Refl , b , c) | Refl with ap2 {_}{_}{_}{_}{_}{_}{_}{_}{r}{r} _∈L_ (append-rh-[] xs) Refl
  ... | eq = Inr (eq-replace (! eq) (∈L-soundness xs r (Inr b)))
    where eq-replace : {a b : Set} → a == b → a → b
          eq-replace Refl x = x

  exec : RegExp → String.String → Maybe (List String.String)
  exec r s with inL-intrinsic r s
  ... | Inl <> = None
  ... | Inr inL = Some (map String.fromList (extract {r}{String.toList s} inL))

  -- Example
  foldl : {A B : Set} → (B → A → B) → B → List A → B
  foldl f z [] = z
  foldl f z (x :: xs) = foldl f (f z x) xs

  alphanumeric : RegExp
  alphanumeric = foldl _⊕_ ∅ (map Lit (String.toList "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"))

  e-mail : RegExp
  e-mail = G (alphanumeric *) · Lit '@' · G (alphanumeric *) · Lit '.' · G (alphanumeric *)

  ex1 : Maybe (List String.String)
  ex1 = exec e-mail "jdoe@wesleyan.edu"

  ex2 : Maybe (List String.String)
  ex2 = exec (G ((Lit 'a') *) · G ((Lit 'b') *)) "aaaabbb"
