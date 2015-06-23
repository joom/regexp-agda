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

  data StdRegExp : Set where
    ∅ˢ : StdRegExp
    Litˢ : (c : Char) → StdRegExp
    _·ˢ_ : StdRegExp → StdRegExp → StdRegExp
    _⊕ˢ_ : StdRegExp → StdRegExp → StdRegExp
    _⁺ˢ : StdRegExp → StdRegExp

  demote-std : StdRegExp → RegExp
  demote-std ∅ˢ = ∅
  demote-std (Litˢ c) = Lit c
  demote-std (r₁ ·ˢ r₂) = demote-std r₁ · demote-std r₂
  demote-std (r₁ ⊕ˢ r₂) = demote-std r₁ ⊕ demote-std r₂
  demote-std (r ⁺ˢ) = x · x *
    where x = demote-std r

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

  lemma : ∀ {A} → (xs ys : List A) → Suffix xs ys → (Suffix ys xs → Void)
  lemma ._ ._ Stop (Drop sf2) = lemma _ _ (Drop Stop) sf2
  lemma ._ ._ (Drop sf) Stop = lemma _ _ sf (Drop Stop)
  lemma ._ ._ (Drop sf) (Drop sf2) = lemma _ _ sf (lemma3 sf2)
    where
        lemma3 : ∀ {A x y} → {xs ys : List A} → Suffix (x :: xs) ys → Suffix xs (y :: ys)
        lemma3 Stop = Drop (Drop Stop)
        lemma3 (Drop sf) = Drop (lemma3 sf)

  not-suffix-self : ∀ {A} → (xs : List A) → Suffix xs xs → Void
  not-suffix-self [] ()
  not-suffix-self (x :: xs) (Drop sf) = lemma _ _ sf Stop

  suffix-unique : ∀ {A} → {xs ys : List A} → (s1 s2 : Suffix xs ys) → s1 == s2
  suffix-unique Stop Stop = Refl
  suffix-unique Stop (Drop s2) = abort (not-suffix-self _ s2)
  suffix-unique (Drop s1) Stop = abort (not-suffix-self _ s1)
  suffix-unique (Drop s1) (Drop s2) = ap Drop (suffix-unique s1 s2)

  -- end of simple stuff

  -- Checks if a given regexp accepts empty string. True, if it accepts ε, False otherwise.
  δ : RegExp → Bool
  δ ∅ = False
  δ ε = True
  δ (Lit x) = False
  δ (r₁ · r₂) with δ r₁ | δ r₂
  ... | False | _ = False
  ... | _ | False = False
  ... | _ | _ = True
  δ (r₁ ⊕ r₂) with δ r₁ | δ r₂
  ... | True | _ = True
  ... | _ | True = True
  ... | _ | _ = False
  δ(r *) = True

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
  match (r₁ ·ˢ r₂) s k (CanRec f) = match r₁ s (λ { (s' , sf) → match r₂ s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)
  match (r₁ ⊕ˢ r₂) s k perm = if match r₁ s k perm then True else match r₂ s k perm
  match (r ⁺ˢ) s k (CanRec f) = if match r s k (CanRec f) then True else match r s (λ { (s' , sf) → match (r ⁺ˢ) s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)

  match-plus : Bool × StdRegExp → (s : List Char) → (Σ (λ s' → Suffix s' s) → Bool) → RecursionPermission s → Bool
  match-plus (False , r) s k perm = match r s k perm
  match-plus (True , r) s k perm = if null s then True else match r s k perm

  _accepts_ : RegExp → String.String → Bool
  r accepts s = match-plus (δ r , standardize r) l (λ { (s , sf) → null s }) (well-founded l)
    where l = String.toList s

  -- Proofs

  -- Shows a string accepted by the language of a regexp. Type "\in L".
  _∈L_ : List Char → RegExp → Set
  data _∈Lˣ_ : List Char → RegExp → Set

  _ ∈L ∅ = Void
  s ∈L ε = s == []
  s ∈L (Lit c) = s == c :: []
  s ∈L (r₁ ⊕ r₂) = Either (s ∈L r₁) (s ∈L r₂)
  s ∈L (r₁ · r₂) = Σ (λ { (p , q) → (p ++ q == s) × (p ∈L r₁) × (q ∈L r₂) })
  s ∈L (r *) = s ∈Lˣ r

  data _∈Lˣ_ where
    Ex : ∀ {s r} → s == [] → r == ε → s ∈Lˣ r
    Cx : ∀ {s s₁ s₂ r} → s₁ ++ s₂ == s → s₁ ∈L r → s₂ ∈Lˣ r → s ∈Lˣ r

  _∈Lˢ_ : List Char → StdRegExp → Set
  data _∈L⁺_ : List Char → StdRegExp → Set

  _ ∈Lˢ ∅ˢ = Void
  s ∈Lˢ (Litˢ c) = s == c :: []
  s ∈Lˢ (r₁ ⊕ˢ r₂) = Either (s ∈Lˢ r₁) (s ∈Lˢ r₂)
  s ∈Lˢ (r₁ ·ˢ r₂) = Σ (λ { (p , q)  → (p ++ q == s) × (p ∈Lˢ r₁) × (q ∈Lˢ r₂) })
  s ∈Lˢ (r ⁺ˢ) = s ∈L⁺ r

  data _∈L⁺_ where
    S+ : ∀ {s r} → s ∈Lˢ r → s ∈L⁺ r
    C+ : ∀ {s s₁ s₂ r} → s₁ ++ s₂ == s → s₁ ∈Lˢ r → s₂ ∈L⁺ r → s ∈L⁺ r

  -- Lemmas
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

  append-suffix3 : {xs ys zs : List Char} → Suffix zs ys → Suffix zs (xs ++ ys)
  append-suffix3 {[]} {ys} {zs} sf = sf
  append-suffix3 {x :: xs} {ys} {zs} sf with append-suffix3 {xs} {ys} {zs} sf
  ... | sf' = Drop sf'

  empty-append : {xs ys : List Char} → xs ++ ys == [] → (xs == []) × (ys == [])
  empty-append {[]} {[]} Refl = Refl , Refl
  empty-append {[]} {_ :: _} ()
  empty-append {_ :: _} {[]} ()
  empty-append {_ :: _} {_ :: _} ()

  nonempty : ∀ {r} → ([] ∈Lˢ r → Void)
  nonempty {∅ˢ} inL = inL
  nonempty {Litˢ c} ()
  nonempty {r₁ ·ˢ r₂} ((xs , ys) , a , b , c) with empty-append {xs} {ys} a
  nonempty {r₁ ·ˢ r₂} ((.[] , .[]) , a , b , c) | Refl , Refl = nonempty b
  nonempty {r₁ ⊕ˢ r₂} (Inl x) = nonempty {r₁} x
  nonempty {r₁ ⊕ˢ r₂} (Inr x) = nonempty {r₂} x
  nonempty {r ⁺ˢ} (S+ x) = nonempty {r} x
  nonempty {r ⁺ˢ} (C+ {.[]}{s₁}{s₂} p q inL) with empty-append {s₁} {s₂} p
  nonempty {r ⁺ˢ} (C+ p q inL) | Refl , Refl = nonempty q

  cons-empty : {x : Char} → {xs : List Char} → x :: xs == [] → Void
  cons-empty ()

  append-suffix2' : {xs ys : List Char} → (xs == [] → Void) → Suffix ys (xs ++ ys)
  append-suffix2' {[]} f = abort (f Refl)
  append-suffix2' {x :: []} {ys} f = Stop
  append-suffix2' {x :: y :: xs} {ys} f = Drop (append-suffix2' {y :: xs} {ys} (cons-empty {y} {xs}))

  append-suffix2 : ∀ {xs ys r} → xs ∈Lˢ r → Suffix ys (xs ++ ys)
  append-suffix2 {xs} {ys} {r} inL with nonempty {r}
  append-suffix2 {[]} inL | q = abort (q inL)
  append-suffix2 {x :: xs} {ys} inL | q = append-suffix2' {x :: xs} {ys} (cons-empty {x} {xs})

  assoc-append-suffix : {xs ys zs : List Char}
                      → ys == zs
                      → Suffix xs ys
                      → Suffix xs zs
  assoc-append-suffix Refl sf = sf

  -- Proofs

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
  match-soundness (r₁ ⊕ˢ r₂) s k perm m with lazyOrEq {match r₁ s k perm} {match r₂ s k perm} m
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | Inl x with match-soundness r₁ s k perm x
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | Inl x | (p , q , r) , a , b , c = (p , (q , r)) , (a , (Inl b , c))
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | Inr x with match-soundness r₂ s k perm x
  match-soundness (r₁ ⊕ˢ r₂) s k perm m | Inr x | (p , q , r) , a , b , c = (p , (q , r)) , (a , (Inr b , c))
  match-soundness (r ⁺ˢ) s k (CanRec f) m with lazyOrEq {match r s k (CanRec f)} { match r s (λ { (s' , sf) → match (r ⁺ˢ) s' (λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f)} m
  match-soundness (r ⁺ˢ) s k (CanRec f) m | Inl x with match-soundness r s k (CanRec f) x
  match-soundness (r ⁺ˢ) s k (CanRec f) m | Inl x | (xs , ys , sfYSs) , a , fst , snd = (xs , (ys , sfYSs)) , (a , (S+ fst , snd))
  match-soundness (r ⁺ˢ) s k (CanRec f) m | Inr x with match-soundness r s (λ s'sf → match (r ⁺ˢ) (fst s'sf) (λ s''sf' → k (fst s''sf' , suffix-trans (snd s''sf') (snd s'sf))) (f (fst s'sf) (snd s'sf))) (CanRec f) x
  match-soundness (r ⁺ˢ) s k (CanRec f) m | Inr x | (a1 , (a2 , sf1)) , b1 , c1 , d1 = (a1 , (a2 , sf1)) , (b1 , (S+ c1 , {!d1!}))


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
  ... | x = match-completeness r₁ ((ms ++ ns) ++ ys)
                 (λ s'sf → match r₂ (fst s'sf) (λ s''sf' → k (fst s''sf' , suffix-trans (snd s''sf') (snd s'sf))) (f (fst s'sf) (snd s'sf)))
                 (CanRec f) ((ms , ns ++ ys , t) , p3 , ms∈r₁ , x)
  match-completeness (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , b , Inl c , d) = eitherIf (Inl (match-completeness r₁ s k perm ((xs , ys) , b , c , d) ))
  match-completeness (r₁ ⊕ˢ r₂) s k perm ((xs , ys) , b , Inr c , d) = eitherIf {match r₁ s k perm} {match r₂ s k perm}
                                                                       (Inr (match-completeness r₂ s k perm ((xs , ys) , b , c , d)))
  match-completeness (r ⁺ˢ) s k (CanRec f) ((xs , ys , sf) , b , S+ x , d) = eitherIf (Inl (match-completeness r s k (CanRec f) ((xs , (ys , sf)) , b , x , d)))
  match-completeness (r ⁺ˢ) s k (CanRec f) ((xs , ys , sf) , b , C+ x x₁ c , d) = {!!}
  --eitherIf (Inr (match-completeness (r ⁺ˢ) s (λ { (s' , sf) → match (r ⁺ˢ) s'(λ { (s'' , sf') → k (s'' , suffix-trans sf' sf) }) (f s' sf) }) (CanRec f) ((xs , (ys , sf)) , (b , ({!!} , {!!})))))
