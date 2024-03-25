{-# OPTIONS --cubical --exact-split #-}

module Cubical.Structures.Gpd.Mon.Desc where

open import Cubical.Foundations.Everything hiding (str)
open import Cubical.Functions.Logic as L
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥

open import Cubical.Structures.Sig
open import Cubical.Structures.Str
open import Cubical.Structures.Tree as T
open import Cubical.Structures.Eq
open import Cubical.Structures.Coh
open import Cubical.Structures.Arity as F

open import Cubical.Structures.Prelude
open import Cubical.Structures.Set.Mon.Desc as Mon renaming (`e to `𝟙 ; `⊕ to `⊗)

data MonCoh : Type where
  `triangle `pentagon : MonCoh

MonCohFree : MonCoh -> ℕ
MonCohFree `triangle = 2
MonCohFree `pentagon = 4

MonCohSig : CohSig ℓ-zero ℓ-zero
MonCohSig = finCohSig (MonCoh , MonCohFree)

-- TODO: coherences on top of signatures and equations 

record MonStr {a : Level} (A : Type a) : Type (ℓ-suc a) where
  constructor mkMonStr
  infixl 5 _⊗_
  field
    𝟙 : A
    _⊗_ : A -> A -> A
  field
    Λ : (x : A) -> 𝟙 ⊗ x ≡ x
    ρ : (x : A) -> x ⊗ 𝟙 ≡ x
    α : (x y z : A) -> (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
  field
    ▿ : (x y : A)
      -> α x 𝟙 y ∙ ap (x ⊗_) (Λ y)
       ≡ ap (_⊗ y) (ρ x)
    ⬠ : (x y z w : A)
      -> α (w ⊗ x) y z ∙ α w x (y ⊗ z)
       ≡ ap (_⊗ z) (α w x y) ∙ α w (x ⊗ y) z ∙ ap (w ⊗_) (α x y z)

open MonStr public

record MonGpd (a : Level) : Type (ℓ-suc a) where
  constructor mkMonGpd
  field
    car : Type a
    str : MonStr car

open MonGpd public
