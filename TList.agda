{-# OPTIONS --cubical #-}

module TList where

open import Cubical.Foundations.Everything
open import Cubical.Data.List
open import Cubical.HITs.SetTruncation as S

MList : ∀ {ℓ} -> Type ℓ -> Type ℓ
MList A = ∥ List A ∥₂

variable
  ℓ : Level
  A B C : Type ℓ

inc : (A -> List B) -> (A -> MList B)
inc = ∣_∣₂ ∘_

eta : A -> MList A
eta = inc [_]

map₂ : (A -> B -> C) -> ∥ A ∥₂ -> ∥ B ∥₂ -> ∥ C ∥₂
map₂ f ∣ a ∣₂ = S.map (f a)
map₂ f (squash₂ a a' p q i j) = {!!}

-- fmap : (A -> B) -> ∥ A ∥₂ -> ∥ B ∥₂
-- fmap f ∣ a ∣₂ = ∣ f a ∣₂
-- fmap f (squash₂ a b p q i j) =
--   squash₂ (fmap f a) (fmap f b) (cong (fmap f) p) (cong (fmap f) q) i j

-- module _ (P : List A -> Type ℓ)
--          (h : (xs : List A) -> P xs)
--          (trunc : {xs : List A} -> isSet (P xs))
--          where
--   f : (xs : MList A) -> P {!!}
--   f = {!!}

e : MList A
e = ∣ [] ∣₂

_⊕_ : MList A -> MList A -> MList A
_⊕_ = map₂ _++_

map-inc : ∀ {f : A -> B} {a} -> S.map f (∣ a ∣₂) ≡ ∣ f a ∣₂
map-inc = refl

map₂-inc : ∀ {f : A -> B -> C} {a b} -> map₂ f a ∣ b ∣₂ ≡ S.map (\a -> f a b) a
map₂-inc {a = a} = {!!}

-- congmap : ((a b : A) -> f a ≡ g b)
--         -> (a' b' : ∥ A ∥₂) -> map f a' ≡ map g b'

-- unitr : (xs : MList A) -> xs ⊕ e ≡ xs
-- unitr xs =
--   map₂ _++_ xs e ≡⟨ {!!} ⟩
--   S.map (\xs -> xs ⊕ e) e  ≡⟨ {!!} ⟩
--   idfun _ xs
--   ∎
