open import Definitions
open import Lemmas

open import Data.Char
open import Data.Bool
open import Data.Empty
open import Data.List
open import Data.Maybe
open import Data.Product
import Data.String as String
open import Data.Sum
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

module RegExpDefinitions where
  data RegExp : Set where
    ∅ : RegExp  -- empty set (type \emptyset)
    ε : RegExp   -- empty string (type \epsilon)
    Lit : Char → RegExp -- literal character
    _·_ : RegExp → RegExp → RegExp -- concatenation (type \cdot)
    _⊕_ : RegExp → RegExp → RegExp -- alternation/set union (type \oplus)
    _* : RegExp → RegExp -- Kleene star
    G : RegExp → RegExp

  infix 1 _*
  infixr 2 _·_
  infixr 3 _⊕_

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
  mutual
    _∈L_ : List Char → RegExp → Set
    _ ∈L ∅ = ⊥
    s ∈L ε = s ≡ []
    s ∈L (Lit c) = s ≡ c ∷ []
    s ∈L (r₁ ⊕ r₂) = (s ∈L r₁) ⊎ (s ∈L r₂)
    s ∈L (r₁ · r₂) = Σ (List Char × List Char) (λ { (p , q) → (p ++ q ≡ s) × (p ∈L r₁) × (q ∈L r₂) })
    s ∈L (r *) = s ∈Lˣ r
    s ∈L (G r) = s ∈L r

    data _∈Lˣ_ : List Char → RegExp → Set where
        Ex : ∀ {s r} → s ≡ [] → s ∈Lˣ r
        Cx : ∀ {s s₁ s₂ r} → s₁ ++ s₂ ≡ s → s₁ ∈L r → s₂ ∈Lˣ r → s ∈Lˣ r

  empty-append-δ : ∀ {x y r} → x ++ y ≡ [] → (x ∈L r) ⊎ (y ∈L r) → ([] ∈L r → ⊥) → ⊥
  empty-append-δ {x}{y}{r} eq inL f with empty-append {x}{y} eq
  empty-append-δ eq (inj₁ inL) f | refl , refl = f inL
  empty-append-δ eq (inj₂ inL) f | refl , refl = f inL

  -- Checks if a given regexp accepts empty string.
  δ' : (r : RegExp) → ([] ∈L r) ⊎ (¬ ([] ∈L r))
  δ' ∅ = inj₂ (λ ())
  δ' ε = inj₁ refl
  δ' (Lit x) = inj₂ (λ ())
  δ' (r₁ · r₂) with δ' r₁ | δ' r₂
  ... | inj₂ p | _ = inj₂ (λ {((x , y) , (a , (b , _))) → empty-append-δ {x}{y}{r₁} a (inj₁ b) p})
  ... | _ | inj₂ q = inj₂ (λ {((x , y) , (a , (_ , c))) → empty-append-δ {x}{y}{r₂} a (inj₂ c) q})
  ... | inj₁ p | inj₁ q = inj₁ (([] , []) , refl , p , q)
  δ' (r₁ ⊕ r₂) with δ' r₁ | δ' r₂
  ... | (inj₁ p) | _ = inj₁ (inj₁ p)
  ... | _ | (inj₁ q) = inj₁ (inj₂ q)
  ... | (inj₂ p) | (inj₂ q) = inj₂ (sub-lemma p q)
    where sub-lemma : ∀ {l1 l2} {a : Set l1} {b : Set l2} → (¬ a) → (¬ b) → ¬ (a ⊎ b)
          sub-lemma f _ (inj₁ a) = f a
          sub-lemma _ g (inj₂ b) = g b
  δ' (r *) = inj₁ (Ex refl)
  δ' (G r) = δ' r

  -- Checks if a given regexp accepts empty string. true, if it accepts ε, false otherwise.
  δ : RegExp → Bool
  δ r with δ' r
  ... | inj₁ _ = true
  ... | inj₂ _ = false

  standardize : RegExp → StdRegExp
  standardize ∅ = ∅ˢ
  standardize ε = ∅ˢ
  standardize (Lit x) = Litˢ x
  standardize (r₁ · r₂) with standardize r₁ | standardize r₂ | δ r₁ | δ r₂
  ... | x₁ | x₂ | false | false = x₁ ·ˢ x₂
  ... | x₁ | x₂ | false | true = x₁ ⊕ˢ (x₁ ·ˢ x₂)
  ... | x₁ | x₂ | true | false = x₂ ⊕ˢ (x₁ ·ˢ x₂)
  ... | x₁ | x₂ | true | true = x₁ ⊕ˢ x₂ ⊕ˢ (x₁ ·ˢ x₂)
  standardize (r₁ ⊕ r₂) = standardize r₁ ⊕ˢ standardize r₂
  standardize (r *) = (standardize r) ⁺ˢ
  standardize (G r) = standardize r

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

  -- Extracts what matches the groups in the proof.
  extract : {r : RegExp} → {xs : List Char} → xs ∈L r → List (List Char)
  extract {∅} ()
  extract {ε} refl = []
  extract {Lit x} refl = []
  extract {r₁ · r₂} ((as , bs) , eq , a , b) = extract {r₁}{as} a ++ extract {r₂}{bs} b
  extract {r₁ ⊕ r₂} (inj₁ x) = extract {r₁} x
  extract {r₁ ⊕ r₂} (inj₂ y) = extract {r₂} y
  extract {r *} (Ex refl) = []
  extract {r *} (Cx {s}{s₁}{s₂} x x₁ inL) = extract {r} x₁ ++ extract {r *} inL
  extract {G r}{xs} inL = xs ∷ extract {r} inL
