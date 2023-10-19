{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Mon.Array where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ
    n m : ℕ

Array : Type ℓ -> Type ℓ
Array A = Σ[ n ∈ ℕ ] (Fin n -> A)

combine : ∀ {n m} -> (Fin n -> A) -> (Fin m -> A) -> (Fin (n + m) -> A)
combine {n = n} {m = m} f g i with Iso.fun (Fin+≅Fin⊎Fin n m) i
... | inl x = f x
... | inr x = g x

_⊕_ : Array A -> Array A -> Array A
(n , as) ⊕ (m , bs) = n + m , combine as bs