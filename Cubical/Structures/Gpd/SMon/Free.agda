{-# OPTIONS --cubical --exact-split #-}
module Cubical.Structures.Gpd.SMon.Free where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F

open import Cubical.Structures.Prelude

data FreeSMon {ℓ : Level} (A : Type ℓ) : Type ℓ where
  η : (a : A) -> FreeSMon A

  𝟙 : FreeSMon A
  _⊗_ : FreeSMon A -> FreeSMon A -> FreeSMon A

  Λ : ∀ x -> 𝟙 ⊗ x ≡ x
  ρ : ∀ x -> x ⊗ 𝟙 ≡ x
  α : ∀ x y z -> (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
  β : ∀ x y -> x ⊗ y ≡ y ⊗ x

  ▿ : ∀ x y
   -> α x 𝟙 y ∙ ap (x ⊗_) (Λ y)
    ≡ ap (_⊗ y) (ρ x)
  ⬠ : ∀ x y z w
    -> α (w ⊗ x) y z ∙ α w x (y ⊗ z)
     ≡ ap (_⊗ z) (α w x y) ∙ α w (x ⊗ y) z ∙ ap (w ⊗_) (α x y z)

  β² : ∀ x y -> β x y ∙ β y x ≡ refl
  ⬡ : ∀ x y z -> α x y z ∙ β x (y ⊗ z) ∙ α y z x
     ≡ ap (_⊗ z) (β x y) ∙ α y x z ∙ ap (y ⊗_) (β x z) 

  trunc : isGroupoid (FreeSMon A)

-- TODO: write the eliminators for FreeSMon and prove them by pattern matching
