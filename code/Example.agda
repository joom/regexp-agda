module Example where

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

open import IntrinsicHOF

import Matcher
module M = Matcher {_acceptsˢ_} {acceptsˢ-soundness} {acceptsˢ-completeness}
