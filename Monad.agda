module Monad where

open import Level using (Level; suc; _⊔_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; cong; refl)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)
open import Effect.Monad using (RawMonad)
open import Function.Base using (id; _∘_)

open import Functor using (Functor; FunctorLaws)
open import Applicative using (Applicative; ApplicativeLaws)

postulate
  extensionality : ∀ {i j} {A : Set i} {B : Set j} {f g : A → B} →
    (∀ {x} → f x ≡ f x) → f ≡ g

private
  variable
    ℓ ℓ′ : Level

record MonadLaws
  (F : Set ℓ → Set ℓ′)
  (pure : ∀ {A} → A → F A)
  (_>>=_ : ∀ {A B} → F A → (A → F B) → F B) : Set (suc ℓ ⊔ ℓ′) where
  field
    identityˡ :
      ∀ {A B} {a} {h : A → F B} →
      --------------------
      pure a >>= h ≡ h a
    identityʳ :
      ∀ {A} {m : F A} →
      --------------------
      m >>= pure ≡ m
    associativity :
      ∀ {A B C} {m} {g : C → F A} {h : A → F B} →
      --------------------
      (m >>= g) >>= h ≡ m >>= (λ x → (g x) >>= h)

  functor : Functor F
  functor = record { _<$>_ = _<$>_ ; functorLaws = functorLaws } where
    _<$>_ : ∀ {A B} → (A → B) → F A → F B
    f <$> x = x >>= (pure ∘ f)

    functorLaws : FunctorLaws F _<$>_
    functorLaws = record { identity = identity ; composition = composition } where
      identity :  ∀ {A} {x : F A} →
        (id <$> x) ≡ x
      identity = identityʳ

      composition : ∀ {A B C} {f : B → C} {g : A → B} {x : F A} →
        ((f ∘ g) <$> x) ≡ (f <$> (g <$> x))
      composition {f = f} {g = g} {x = x} =
        begin
          x  >>= (pure ∘ f ∘ g)
        ≡⟨ cong (λ f → x >>= f) (extensionality refl) ⟩
          x >>= (λ y → pure (g y) >>= (pure ∘ f))
        ≡⟨ sym associativity ⟩
          (x >>= (pure ∘ g)) >>= (pure ∘ f)
        ∎

record Monad (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  infixl 1 _>>=_
  field
    applicative : Applicative F
    _>>=_ : ∀ {A B} → F A → (A → F B) → F B
    monadLaws : MonadLaws F (Applicative.pure applicative) _>>=_

  rawMonad : RawMonad F
  rawMonad = record { rawApplicative = Applicative.rawApplicative applicative ; _>>=_ = _>>=_ }

  open Applicative.Applicative applicative public
  open MonadLaws public hiding (functor)
