{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Sig where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.FinData as F
open import Cubical.Data.List as L
open import Cubical.Data.List.FinData as F
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.SetQuotients as Q
open import Agda.Primitive

record Sig (f a : Level) : Type ((ℓ-suc f) ⊔ (ℓ-suc a)) where
  field
    symbol : Type f
    arity : symbol -> Type a
open Sig public

-- signature functor
module _ {f a n : Level} (σ : Sig f a) where
  sig : Type n -> Type (ℓ-max f (ℓ-max a n))
  sig X = Σ (σ .symbol) \f -> σ .arity f -> X

  sigF : {X Y : Type n} -> (X -> Y) -> sig X -> sig Y
  sigF h (f , i) = f , h ∘ i
