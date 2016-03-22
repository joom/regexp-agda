open import Definitions
open import Lemmas
open import RegExpDefinitions

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

module Matcher {_acceptsˢ_ : StdRegExp → List Char → Bool}
               {acceptsˢ-soundness : (r : StdRegExp) → (s : List Char) → r acceptsˢ s ≡ true → s ∈Lˢ r}
               {acceptsˢ-completeness : (r : StdRegExp) → (s : List Char) → s ∈Lˢ r → r acceptsˢ s ≡ true} where
  -- Overall matcher
  _accepts_ : RegExp → String.String → Bool
  r accepts s with δ r | standardize r | String.toList s
  ... | true  | r' | xs = (null xs) ∨ (r' acceptsˢ xs)
  ... | false | r' | xs = r' acceptsˢ xs

  accepts-intrinsic : (r : RegExp)
                → (s : List Char)
                → Maybe (s ∈L r)
  accepts-intrinsic r xs with δ' r
  accepts-intrinsic r [] | inj₁ x = just x
  accepts-intrinsic r xs | d with bool-eq ((standardize r) acceptsˢ xs)
  ... | inj₂ q = nothing
  ... | inj₁ p = just (∈L-soundness xs r (inj₂ (acceptsˢ-soundness (standardize r) xs p)))

  exec : RegExp → String.String → Maybe (List String.String)
  exec r s = Data.Maybe.map (λ inL → Data.List.map String.fromList (extract {r}{xs} inL)) (accepts-intrinsic r xs)
    where xs = String.toList s

  -- Overall correctness

  correct-soundness : (r : RegExp)
                    → (s : String.String)
                    → r accepts s ≡ true
                    → (String.toList s) ∈L r
  correct-soundness r s eq with String.toList s | δ' r
  correct-soundness r s eq | [] | inj₁ p = p
  correct-soundness r s eq | x ∷ xs | inj₁ p = ∈L-soundness (x ∷ xs) r (inj₂ (acceptsˢ-soundness _ _ eq))
  correct-soundness r s eq | xs | inj₂ y = ∈L-soundness xs r (inj₂ (acceptsˢ-soundness _ _ eq))

  correct-completeness : (r : RegExp)
                       → (s : String.String)
                       → (String.toList s) ∈L r
                       → r accepts s ≡ true
  correct-completeness r s inL with String.toList s | δ' r
  correct-completeness r s inL | xs | inj₁ x with ∈L-completeness xs r inL
  correct-completeness r s inL | .[] | inj₁ _ | inj₁ (_ , refl) = refl
  correct-completeness r s inL | [] | inj₁ _ | inj₂ _ = refl
  correct-completeness r s inL | x ∷ xs | inj₁ _ | inj₂ y = acceptsˢ-completeness _ _ y
  correct-completeness r s inL | xs | inj₂ y with ∈L-completeness xs r inL
  correct-completeness r s inL | .[] | inj₂ y | inj₁ (_ , refl) = ⊥-elim (y inL)
  correct-completeness r s inL | xs | inj₂ _ | inj₂ y = acceptsˢ-completeness _ _ y

  -- open Deprecated-inspect
  decidability : (r : RegExp) → (s : String.String) → ((String.toList s) ∈L r) ⊎ (¬ ((String.toList s) ∈L r))
  decidability r s with bool-eq (r accepts s)
  ... | inj₁ p = inj₁ (correct-soundness r s p)
  ... | inj₂ q = inj₂ (λ x → lemma (trans (sym (correct-completeness r s x)) q))
    where
      lemma : ¬ true ≡ false
      lemma ()

  alphanumeric : RegExp
  alphanumeric = foldl _⊕_ ∅ (Data.List.map Lit (String.toList "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"))

  e-mail : RegExp
  e-mail = G (alphanumeric *) · Lit '@' · G (alphanumeric *) · Lit '.' · G (alphanumeric *)

  ex1 : Maybe (List String.String)
  ex1 = exec (G ((Lit 'a') *) · G ((Lit 'b') *)) "aaaabbb"

  ex2 : Maybe (List String.String)
  ex2 = exec e-mail "jdoe@wesleyan.edu"

  ex3 : Maybe (List String.String)
  ex3 = exec (G (Lit 'a' *) · G (Lit 'a' *)) "aaaa"
