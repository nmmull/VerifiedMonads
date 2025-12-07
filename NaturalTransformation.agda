module NaturalTransformation where

open import Level using (Level; suc; _⊔_)
open import Function.Base using (_∘_)

private
  variable
    ℓ ℓ′ ℓ′′ : Level

_⇒_ :
  (F : Set ℓ → Set ℓ′) →
  (G : Set ℓ → Set ℓ′) →
  Set (suc ℓ ⊔ ℓ′)
F ⇒ G = ∀ A → F A → G A

_∘F_ : ∀
  {F : Set ℓ′ → Set ℓ′′}
  {G : Set ℓ′ → Set ℓ′′} →
  (F ⇒ G) →
  (K : Set ℓ → Set ℓ′) →
  (F ∘ K) ⇒ (G ∘ K)
F⇒G ∘F K = λ A fka → F⇒G (K A) fka

_∘η_ : ∀
  {F : Set ℓ → Set ℓ′}
  {G : Set ℓ → Set ℓ′}
  {K : Set ℓ → Set ℓ′} →
  (G ⇒ K) →
  (F ⇒ G) →
  (F ⇒ K)
G⇒K ∘η F⇒G = λ A fa → G⇒K A (F⇒G A fa)
