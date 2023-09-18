{-# OPTIONS --cubical #-}

module FreeStr where

open import Cubical.Foundations.Everything

private
  variable
    ℓ ℓ' ℓ'' : Level
    S : Type ℓ → Type ℓ'

record FreeS (ℓ : Level) (S : Type ℓ → Type ℓ') : Type (ℓ-max (ℓ-suc ℓ) ℓ') where
  field
    F : Type ℓ -> Type ℓ
    F-S : (A : Type ℓ) -> S (F A)
    η : (A : Type ℓ) -> A -> F A

-- freeS : (S : Type ℓ -> Type ℓ') -> FreeS ℓ S
-- monad T, T-algebra
