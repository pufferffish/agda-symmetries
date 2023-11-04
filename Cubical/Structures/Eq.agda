{-# OPTIONS --cubical #-}

module Cubical.Structures.Eq where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.List as L
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.SetQuotients as Q
open import Agda.Primitive

open import Cubical.Structures.Sig
open import Cubical.Structures.Str
open import Cubical.Structures.Tree

record EqSig (e n : Level) : Type (ℓ-max (ℓ-suc e) (ℓ-suc n)) where
  field
    name : Type e
    free : name -> Type n
open EqSig public

FinEqSig : (e : Level) -> Type (ℓ-max (ℓ-suc e) (ℓ-suc ℓ-zero))
FinEqSig = FinSig

finEqSig : {e : Level} -> FinEqSig e -> EqSig e ℓ-zero
name (finEqSig σ) = σ .fst
free (finEqSig σ) = Fin ∘ σ .snd

emptyEqSig : EqSig ℓ-zero ℓ-zero
name emptyEqSig = ⊥.⊥
free emptyEqSig = ⊥.rec

sumEqSig : {e n e' n' : Level} -> EqSig e n -> EqSig e' n' -> EqSig (ℓ-max e e') (ℓ-max n n')
name (sumEqSig σ τ) = (name σ) ⊎ (name τ)
free (sumEqSig {n' = n} σ τ) (inl x) = Lift {j = n} ((free σ) x)
free (sumEqSig {n = n} σ τ) (inr x) = Lift {j = n} ((free τ) x)

module _ {f a e n : Level} (σ : Sig f a) (τ : EqSig e n) where
  -- TODO: refactor as (Tree σ Unit -> Tree σ X) × (Tree σ Unit -> Tree σ X) ?
  seq : Type (ℓ-max (ℓ-max (ℓ-max f a) e) n)
  seq = (e : τ .name) -> Tree σ (τ .free e) × Tree σ (τ .free e)

emptySEq : seq emptySig emptyEqSig
emptySEq n = ⊥.rec n

module _ {f a e n s : Level} {σ : Sig f a} {τ : EqSig e n} where
  -- type of structure satisfying equations
  -- TODO: refactor as a coequaliser
  infix 30 _⊨_
  _⊨_ : struct s σ -> (ε : seq σ τ) -> Type (ℓ-max s (ℓ-max e n))
  𝔛 ⊨ ε = (eqn : τ .name) (ρ : τ .free eqn -> 𝔛 .car)
       -> sharp σ 𝔛 ρ (ε eqn .fst) ≡ sharp σ 𝔛 ρ (ε eqn .snd)

