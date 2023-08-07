module Monad where

open import Level using (Level; suc; _⊔_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; cong; refl)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)
open import Effect.Monad using (RawMonad)
open import Function.Base using (id; _∘_)

open import Functor using (Functor; IsFunctor)
open import Applicative using (Applicative; IsApplicative)

postulate
  extentionality : ∀ {i j} {A : Set i} {B : Set j} {f g : A → B} →
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

  infixl 4 _<$>′_
  _<$>′_ : ∀ {A B} → (A → B) → F A → F B
  f <$>′ x = x >>= (pure ∘ f)

  isFunctor′ : IsFunctor F _<$>′_
  isFunctor′ = record { identity = identity ; composition = composition } where
    identity :  ∀ {A} {x : F A} →
      (id <$>′ x) ≡ x
    identity = identityʳ
    composition : ∀ {A B C} {f : B → C} {g : A → B} {x : F A} →
      ((f ∘ g) <$>′ x) ≡ (f <$>′ (g <$>′ x))
    composition {f = f} {g = g} {x = x} =
      begin
        x  >>= (pure ∘ f ∘ g)
      ≡⟨ cong (λ f → x >>= f) (extentionality refl) ⟩
        x >>= (λ y → pure (g y) >>= (pure ∘ f))
      ≡⟨ sym associativity ⟩
        (x >>= (pure ∘ g)) >>= (pure ∘ f)
      ∎

  functor′ : Functor F
  functor′ = record { rawFunctor = record { _<$>_ = _<$>′_ } ; isFunctor = isFunctor′ }

record IsMonad
  (F : Set ℓ → Set ℓ′)
  (map : ∀ {A B} → (A → B) → F A → F B)
  (pure : ∀ {A} → A → F A)
  (app : ∀ {A B} → F (A → B) → F A → F B)
  (bind : ∀ {A B} → F A → (A → F B) → F B) : Set (suc ℓ ⊔ ℓ′) where
  field
    isApplicative : IsApplicative F map pure app
    monadLaws : MonadLaws F pure bind

  open IsApplicative isApplicative public
  open MonadLaws monadLaws public

record Monad (F : Set ℓ → Set ℓ′) : Set (suc ℓ ⊔ ℓ′) where
  field
    rawMonad : RawMonad F
    isMonad : IsMonad F
      (RawMonad._<$>_ rawMonad)
      (RawMonad.pure  rawMonad)
      (RawMonad._<*>_ rawMonad)
      (RawMonad._>>=_ rawMonad)

  open RawMonad rawMonad public
  open IsMonad isMonad public

  applicative : Applicative F
  applicative = record { rawApplicative = rawApplicative ; isApplicative = isApplicative }
