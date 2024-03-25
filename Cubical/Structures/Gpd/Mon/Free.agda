{-# OPTIONS --cubical --exact-split #-}
module Cubical.Structures.Gpd.Mon.Free where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F

open import Cubical.Structures.Prelude


data FreeMon {ℓ : Level} (A : Type ℓ) : Type ℓ where
  η : (a : A) -> FreeMon A

  𝟙 : FreeMon A
  _⊗_ : FreeMon A -> FreeMon A -> FreeMon A

  Λ : ∀ x -> 𝟙 ⊗ x ≡ x
  ρ : ∀ x -> x ⊗ 𝟙 ≡ x
  α : ∀ x y z -> (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)

  ▿ : ∀ x y
   -> α x 𝟙 y ∙ ap (x ⊗_) (Λ y)
    ≡ ap (_⊗ y) (ρ x)
  ⬠ : ∀ x y z w
    -> α (w ⊗ x) y z ∙ α w x (y ⊗ z)
     ≡ ap (_⊗ z) (α w x y) ∙ α w (x ⊗ y) z ∙ ap (w ⊗_) (α x y z)

  trunc : isGroupoid (FreeMon A)

-- TODO: write the eliminators for FreeMon and prove them by pattern matching
