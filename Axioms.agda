module Axioms where

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit) renaming (implicit-extensionality to ie)

postulate
  extensionality : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

implicit-extensionality : ∀ {ℓ₁ ℓ₂} → ExtensionalityImplicit ℓ₁ ℓ₂
implicit-extensionality = ie extensionality
