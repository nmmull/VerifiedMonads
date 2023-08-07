module Applicative where

open import Level using (Level; suc; _⊔_)
open import Functor using (IsFunctor)
open import Function.Base using (id)
open import Effect.Applicative using (RawApplicative)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Functor using (Functor)

private
  variable
    ℓ ℓ′ : Level

record ApplicativeLaws
  (F : Set ℓ → Set ℓ′)
  (pure : ∀ {A} → A → F A)
  (_<*>_ : ∀ {A B} → F (A → B) → F A → F B) : Set (suc ℓ ⊔ ℓ′) where
  field
    identity : ∀ {A} {x : F A} →
      --------------------
      pure id <*> x ≡ x
    homomorphism : ∀ {A B} {f : A → B} {x} →
      --------------------
      pure f <*> pure x ≡ pure (f x)
    interchange : ∀ {A B} {u : F (A → B)} {y} →
      --------------------
      u <*> pure y ≡ pure (λ f → f y) <*> u
    composition : ∀ {A B C} {u : F (B → C)} {v : F (A → B)} {w : F A} →
      --------------------
      ((pure (λ f g x → f (g x)) <*> u) <*> v) <*> w ≡ u <*> (v <*> w)

record IsApplicative
  (F : Set ℓ → Set ℓ′)
  (_<$>_ : ∀ {A B} → (A → B) → F A → F B)
  (pure : ∀ {A} → A → F A)
  (_<*>_ : ∀ {A B} → F (A → B) → F A → F B) : Set (suc ℓ ⊔ ℓ′) where
  field
    isFunctor : IsFunctor F _<$>_
    applicativeLaws : ApplicativeLaws F pure _<*>_

  open IsFunctor isFunctor public
  open ApplicativeLaws applicativeLaws public

record Applicative (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  field
    rawApplicative : RawApplicative F
    isApplicative : IsApplicative F
      (RawApplicative._<$>_ rawApplicative)
      (RawApplicative.pure rawApplicative)
      (RawApplicative._<*>_ rawApplicative)

  open RawApplicative rawApplicative public
  open IsApplicative isApplicative public

  functor : Functor F
  functor = record { rawFunctor = rawFunctor ; isFunctor = isFunctor }
