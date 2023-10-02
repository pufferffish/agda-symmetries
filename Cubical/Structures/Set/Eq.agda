{-# OPTIONS --cubical #-}

module Cubical.Structures.Set.Eq where

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

open import Cubical.Structures.Set.Sig
open import Cubical.Structures.Set.Str
open import Cubical.Structures.Set.Tree

record EqSig (e n : Level) : Type (ℓ-max (ℓ-suc e) (ℓ-suc n)) where
  field
    name : Type e
    free : name -> Type n
open EqSig public

record EqThy {f a e n : Level} (σ : Sig f a) (τ : EqSig e n) : Type (ℓ-max (ℓ-max f a) (ℓ-max (ℓ-suc e) (ℓ-suc n))) where
  field
    lhs : (n : τ .name) -> Tree σ (τ .free n)
    rhs : (n : τ .name) -> Tree σ (τ .free n)
open EqThy public

module _ {f a e n : Level} (σ : Sig f a) (τ : EqSig e n) where
  -- same as EqThy
  seq : Type (ℓ-max (ℓ-max (ℓ-max f a) e) n)
  seq = (e : τ .name) -> Tr σ (τ .free e) × Tr σ (τ .free e)

module _ {f a e n : Level} {σ : Sig f a} {τ : EqSig e n} where
  -- type of structure satisfying equations
  infix 30 _⊨_
  _⊨_ : struct σ -> (ε : seq σ τ) -> Type (ℓ-max (ℓ-max (ℓ-max f a) e) n)
  _⊨_ (X , α) ε = (e : τ .name) (ρ : τ .free e -> X) -> sharp σ (X , α) ρ (ε e .fst) ≡ sharp σ (X , α) ρ (ε e .snd)
