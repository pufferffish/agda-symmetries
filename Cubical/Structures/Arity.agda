{-# OPTIONS --cubical --safe #-}

module Cubical.Structures.Arity where

open import Cubical.Foundations.Everything
open import Cubical.Data.InfNat
open import Cubical.Data.Nat
open import Cubical.Data.List

Operands : ∀ {ℓ} -> ℕ+∞ -> Type ℓ -> Type ℓ
Operands ∞ A = ℕ -> A
Operands (fin k) A = Σ[ ops ∈ List A ] length ops ≡ k

supply : ∀ {ℓ} {A : Type ℓ} (xs : List A) -> Operands (fin (length xs)) A
supply x = x , refl

omap : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {l : ℕ+∞} -> (A -> B) -> Operands l A -> Operands l B
omap {l = ∞} f x = f ∘ x
omap {l = fin _} f (list , p) = map f list , length-map f list ∙ p

