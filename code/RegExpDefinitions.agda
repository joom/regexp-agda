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

  data _∈L_ : List Char → RegExp → Set where
    ∈ε : [] ∈L ε
    ∈Lit : ∀ {c} → (c ∷ []) ∈L (Lit c)
    ∈⊕₁ : ∀ {s r₁ r₂} → s ∈L r₁ → s ∈L (r₁ ⊕ r₂)
    ∈⊕₂ : ∀ {s r₁ r₂} → s ∈L r₂ → s ∈L (r₁ ⊕ r₂)
    ∈· : ∀ {s p q r₁ r₂} → p ++ q ≡ s → p ∈L r₁ → q ∈L r₂ → s ∈L (r₁ · r₂)
    ∈Ex : ∀ {r} → [] ∈L (r *)
    ∈Cx : ∀ {s s₁ s₂ r} → s₁ ++ s₂ ≡ s → s₁ ∈L r → s₂ ∈L (r *) → s ∈L (r *)
    ∈G : ∀ {s r} → s ∈L r → s ∈L (G r)

  empty-append-δ : ∀ {x y r} → x ++ y ≡ [] → (x ∈L r) ⊎ (y ∈L r) → ([] ∈L r → ⊥) → ⊥
  empty-append-δ {x}{y}{r} eq inL f with empty-append {x}{y} eq
  empty-append-δ eq (inj₁ inL) f | refl , refl = f inL
  empty-append-δ eq (inj₂ inL) f | refl , refl = f inL

  -- Checks if a given regexp accepts empty string.
  δ' : (r : RegExp) → ([] ∈L r) ⊎ (¬ ([] ∈L r))
  δ' ∅ = inj₂ (λ ())
  δ' ε = inj₁ ∈ε
  δ' (Lit x) = inj₂ (λ ())
  δ' (r₁ · r₂) with δ' r₁ | δ' r₂
  ... | inj₂ p | _ = inj₂ λ {(∈· a b _) → empty-append-δ a (inj₁ b) p}
  ... | _ | inj₂ q = inj₂ λ {(∈· a _ c) → empty-append-δ a (inj₂ c) q}
  ... | inj₁ p | inj₁ q = inj₁ (∈· refl p q)
  δ' (r₁ ⊕ r₂) with δ' r₁ | δ' r₂
  ... | (inj₁ p) | _ = inj₁ (∈⊕₁ p)
  ... | _ | (inj₁ q) = inj₁ (∈⊕₂ q)
  ... | (inj₂ p) | (inj₂ q) = inj₂ λ { (∈⊕₁ p') → p p' ; (∈⊕₂ q') → q q' }
  δ' (r *) = inj₁ ∈Ex
  δ' (G r) with δ' r
  ... | inj₁ p = inj₁ (∈G p)
  ... | inj₂ p = inj₂ λ {(∈G q) → p q}

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
  ∈L-soundness s ∅ (inj₂ ())
  ∈L-soundness s ε (inj₂ ())
  ∈L-soundness .(x ∷ []) (Lit x) (inj₂ ∈ˢLit) = ∈Lit
  ∈L-soundness s (r₁ · r₂) (inj₂ y) with δ' r₁ | δ' r₂
  ∈L-soundness s (r₁ · r₂) (inj₂ (∈ˢ· {_}{p}{q} eq a b)) | inj₂ _ | inj₂ _ = ∈· eq (∈L-soundness p r₁ (inj₂ a)) (∈L-soundness q r₂ (inj₂ b))
  ∈L-soundness s (r₁ · r₂) (inj₂ (∈ˢ⊕₁ y)) | inj₂ _ | inj₁ q = ∈· (append-rh-[] s) (∈L-soundness s r₁ (inj₂ y)) q
  ∈L-soundness s (r₁ · r₂) (inj₂ (∈ˢ⊕₂ (∈ˢ· {_}{p}{q} eq a b))) | inj₂ _ | inj₁ _ = ∈· eq (∈L-soundness p r₁ (inj₂ a)) (∈L-soundness q r₂ (inj₂ b))
  ∈L-soundness s (r₁ · r₂) (inj₂ (∈ˢ⊕₁ y)) | inj₁ p | inj₂ _ = ∈· refl p (∈L-soundness s r₂ (inj₂ y))
  ∈L-soundness s (r₁ · r₂) (inj₂ (∈ˢ⊕₂ (∈ˢ· {_}{p}{q} eq a b))) | inj₁ _ | inj₂ _ = ∈· eq (∈L-soundness p r₁ (inj₂ a)) (∈L-soundness q r₂ (inj₂ b))
  ∈L-soundness s (r₁ · r₂) (inj₂ (∈ˢ⊕₁ y)) | inj₁ _ | inj₁ q = ∈· (append-rh-[] s) (∈L-soundness s r₁ (inj₂ y)) q
  ∈L-soundness s (r₁ · r₂) (inj₂ (∈ˢ⊕₂ (∈ˢ⊕₁ y))) | inj₁ p | inj₁ q = ∈· refl p (∈L-soundness s r₂ (inj₂ y))
  ∈L-soundness s (r₁ · r₂) (inj₂ (∈ˢ⊕₂ (∈ˢ⊕₂ (∈ˢ· eq a b)))) | inj₁ p | inj₁ q = ∈· eq (∈L-soundness _ r₁ (inj₂ a)) ((∈L-soundness _ r₂ (inj₂ b)))
  ∈L-soundness s (r₁ ⊕ r₂) (inj₂ (∈ˢ⊕₁ y)) = ∈⊕₁ (∈L-soundness s r₁ (inj₂ y))
  ∈L-soundness s (r₁ ⊕ r₂) (inj₂ (∈ˢ⊕₂ y)) = ∈⊕₂ (∈L-soundness s r₂ (inj₂ y))
  ∈L-soundness s (r *) (inj₂ (∈ˢS+ y)) = ∈Cx (append-rh-[] s) (∈L-soundness s r (inj₂ y)) ∈Ex
  ∈L-soundness s (r *) (inj₂ (∈ˢC+ {.s}{s₁}{s₂} a b c)) = ∈Cx a (∈L-soundness s₁ r (inj₂ b)) (∈L-soundness s₂ (r *) (inj₂ c))
  ∈L-soundness s (G r) (inj₂ y) = ∈G (∈L-soundness s r (inj₂ y))

  ∈L-completeness : (s : List Char)
                  → (r : RegExp)
                  → s ∈L r
                  → ((δ r ≡ true) × (s ≡ [])) ⊎ (s ∈Lˢ (standardize r))
  ∈L-completeness .[] .ε ∈ε = inj₁ (refl , refl)
  ∈L-completeness .(_ ∷ []) .(Lit _) ∈Lit = inj₂ ∈ˢLit
  ∈L-completeness s (r₁ ⊕ _) (∈⊕₁ inL) with ∈L-completeness s _ inL
  ... | inj₂ pf = inj₂ (∈ˢ⊕₁ pf)
  ... | inj₁ pf with δ' r₁
  ... | inj₁ p = inj₁ pf
  ∈L-completeness s (r₁ ⊕ _) (∈⊕₁ _) | inj₁ (() , _) | inj₂ _
  ∈L-completeness s (_ ⊕ r₂) (∈⊕₂ inL) with ∈L-completeness s _ inL
  ... | inj₂ pf = inj₂ (∈ˢ⊕₂ pf)
  ... | inj₁ pf with δ' r₂
  ∈L-completeness s (_ ⊕ _) (∈⊕₂ _) | inj₁ (() , _) | inj₂ _
  ∈L-completeness s (r₁ ⊕ r₂) (∈⊕₂ inL) | inj₁ pf | inj₁ p with δ' r₁
  ... | inj₁ q = inj₁ pf
  ... | inj₂ q = inj₁ pf
  ∈L-completeness s (r₁ · r₂) (∈· {_}{p}{q} eq inL inL') with δ' r₁ | δ' r₂ | ∈L-completeness p r₁ inL | ∈L-completeness q r₂ inL'
  ∈L-completeness .[] (r₁ · r₂) (∈· {.[]} {.[]} {.[]} refl inL inL') | inj₁ d | inj₁ e | inj₁ (refl , refl) | inj₁ (refl , refl) = inj₁ (refl , refl)
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {.[]} {.s} refl inL inL') | inj₁ d | inj₁ e | inj₁ (refl , refl) | inj₂ b = inj₂ (∈ˢ⊕₂ (∈ˢ⊕₁ b))
  ∈L-completeness .(p ++ []) (r₁ · r₂) (∈· {.(p ++ [])} {p} {.[]} refl inL inL') | inj₁ d | inj₁ e | inj₂ a | inj₁ (refl , refl) =
    inj₂ (∈ˢ⊕₁ (same-list-language (sym (append-rh-[] p)) a))
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} eq inL inL') | inj₁ d | inj₁ e | inj₂ a | inj₂ b = inj₂ (∈ˢ⊕₂ (∈ˢ⊕₂ (∈ˢ· eq a b)))
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} _ _ _) | inj₁ _ | inj₂ _ | inj₁ _ | inj₁ (() , _)
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {.[]} {.s} refl inL inL') | inj₁ d | inj₂ e | inj₁ (refl , refl) | inj₂ b = inj₂ (∈ˢ⊕₁ b)
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} eq inL inL') | inj₁ _ | inj₂ _ | inj₂ _ | inj₁ (() , _)
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} eq inL inL') | inj₁ d | inj₂ e | inj₂ a | inj₂ b = inj₂ (∈ˢ⊕₂ (∈ˢ· eq a b))
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} _ _ _) | inj₂ _ | inj₁ _ | inj₁ (() , _) | inj₁ _
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} _ _ _) | inj₂ _ | inj₁ _ | inj₁ (() , _) | inj₂ _
  ∈L-completeness .(p ++ []) (r₁ · r₂) (∈· {.(p ++ [])} {p} {.[]} refl inL inL') | inj₂ d | inj₁ e | inj₂ a | inj₁ (t , refl) =
    inj₂ (∈ˢ⊕₁ (same-list-language (sym (append-rh-[] p)) a))
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} eq inL inL') | inj₂ d | inj₁ e | inj₂ a | inj₂ b = inj₂ (∈ˢ⊕₂ (∈ˢ· eq a b))
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} _ _ _) | inj₂ d | inj₂ e | inj₁ (() , _) | inj₁ _
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} _ _ _) | inj₂ d | inj₂ e | inj₁ (() , _) | inj₂ _
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} _ _ _) | inj₂ _ | inj₂ _ | inj₂ _ | inj₁ (() , _)
  ∈L-completeness s (r₁ · r₂) (∈· {.s} {p} {q} eq _ _) | inj₂ _ | inj₂ _ | inj₂ a | inj₂ b = inj₂ (∈ˢ· eq a b)
  ∈L-completeness .[] (r *) ∈Ex = inj₁ (refl , refl)
  ∈L-completeness s (r *) (∈Cx {_}{p}{q} eq inL inL') with ∈L-completeness p r inL | ∈L-completeness q (r *) inL'
  ∈L-completeness s (r *) (∈Cx {.s} {.[]} {.[]} eq inL inL') | inj₁ (a , refl) | inj₁ (b , refl) = inj₁ (refl , sym eq)
  ∈L-completeness s (r *) (∈Cx {.s} {.[]} {.s} refl inL inL') | inj₁ (a , refl) | inj₂ b = inj₂ b
  ∈L-completeness .(p ++ []) (r *) (∈Cx {.(p ++ [])} {p} {.[]} refl inL inL') | inj₂ a | inj₁ (refl , refl) =
    inj₂ (∈ˢS+ (same-list-language (sym (append-rh-[] p)) a))
  ∈L-completeness s (r *) (∈Cx {.s} {p} {q} eq inL inL') | inj₂ a | inj₂ b = inj₂ (∈ˢC+ eq a b)
  ∈L-completeness s .(G _) (∈G inL) with ∈L-completeness s _ inL
  ∈L-completeness s (G r) inL | inj₁ (a , b) with δ' (G r)
  ... | inj₁ x = inj₁ (refl , b)
  ∈L-completeness .[] .(G _) (∈G inL) | inj₁ (a , refl) | inj₂ x = ⊥-elim (x (∈G inL))
  ∈L-completeness s (G r) inL | inj₂ x = inj₂ x

  -- Extracts what matches the groups in the proof.
  extract : {r : RegExp} → {xs : List Char} → xs ∈L r → List (List Char)
  extract ∈ε = []
  extract ∈Lit = []
  extract (∈⊕₁ inL) = extract inL
  extract (∈⊕₂ inL) = extract inL
  extract (∈· x inL inL') = extract inL ++ extract inL'
  extract ∈Ex = []
  extract (∈Cx _ inL inL') = extract inL ++ extract inL'
  extract {_}{xs} (∈G inL) = xs ∷ extract inL
