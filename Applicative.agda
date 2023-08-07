module Applicative where

open import Level using (Level; suc; _⊔_)
open import Function.Base using (id)
open import Effect.Applicative using (RawApplicative)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)
open import Function.Base using (id; _∘_)

open import Functor using (FunctorLaws; Functor)

private
  variable
    ℓ ℓ′ : Level

record ApplicativeLaws
  (F : Set ℓ → Set ℓ′)
  (pure : ∀ {A} → A → F A)
  (_<*>_ : ∀ {A B} → F (A → B) → F A → F B) : Set (suc ℓ ⊔ ℓ′) where
  field
    identity :
      ∀ {A} {x : F A} →
      --------------------
      pure id <*> x ≡ x
    homomorphism :
      ∀ {A B} {f : A → B} {x} →
      --------------------
      pure f <*> pure x ≡ pure (f x)
    interchange :
      ∀ {A B} {u : F (A → B)} {y} →
      --------------------
      u <*> pure y ≡ pure (λ f → f y) <*> u
    composition :
      ∀ {A B C} {u : F (B → C)} {v : F (A → B)} {w : F A} →
      --------------------
      ((pure (λ f g x → f (g x)) <*> u) <*> v) <*> w ≡ u <*> (v <*> w)

  functor : Functor F
  functor = record { _<$>_ = _<$>_ ; functorLaws = functorLaws } where
    _<$>_ : ∀ {A B} → (A → B) → F A → F B
    f <$> x = pure f <*> x

    functorLaws : FunctorLaws F _<$>_
    functorLaws = record { identity = identity′ ; composition = composition′ } where
      identity′ :  ∀ {A} {x : F A} →
        (id <$> x) ≡ x
      identity′ = identity

      composition′ : ∀ {A B C} {f : B → C} {g : A → B} {x : F A} →
        ((f ∘ g) <$> x) ≡ (f <$> (g <$> x))
      composition′ {f = f} {g = g} {x = x} =
        begin
          pure (f ∘ g) <*> x
        ≡⟨ cong (λ z → z <*> x) (sym homomorphism) ⟩
          ((pure (λ g x → f (g x))) <*> pure g) <*> x
        ≡⟨ cong (λ z → (z <*> pure g) <*> x) (sym homomorphism) ⟩
          ((pure (λ f g x → f (g x)) <*> pure f) <*> pure g) <*> x
        ≡⟨ composition ⟩
          pure f <*> (pure g <*> x)
        ∎

record Applicative (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  infixl 4 _<*>_
  field
    functor : Functor F
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    applicativeLaws : ApplicativeLaws F pure _<*>_

  rawApplicative : RawApplicative F
  rawApplicative = record { rawFunctor = (Functor.rawFunctor functor) ; pure = pure ; _<*>_ = _<*>_ }

  open Functor.Functor functor public
  open ApplicativeLaws applicativeLaws public hiding (functor)
