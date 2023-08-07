module Functor where

open import Level using (Level; suc; _⊔_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Function.Base using (id; _∘_)
open import Effect.Functor using (RawFunctor)

private
  variable
    ℓ ℓ′ : Level

record IsFunctor
  (F : Set ℓ → Set ℓ′)
  (_<$>_ : ∀ {A B} → (A → B) → F A → F B) : Set (suc ℓ ⊔ ℓ′) where
  field
    identity :
      ∀ {A} {x : F A} →
      --------------------
      id <$> x ≡ x
    composition :
      ∀ {A B C} {f : B → C} {g : A → B} {x : F A} →
      --------------------
      (f ∘ g) <$> x ≡ f <$> (g <$> x)

record Functor (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  field
    rawFunctor : RawFunctor F
    isFunctor : IsFunctor F (RawFunctor._<$>_ rawFunctor)

  open RawFunctor rawFunctor public
  open IsFunctor isFunctor public
