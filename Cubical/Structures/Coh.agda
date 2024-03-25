{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Coh where

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
open import Cubical.Structures.Eq

record CohSig (e n : Level) : Type (ℓ-max (ℓ-suc e) (ℓ-suc n)) where
  field
    name : Type e
    free : name -> Type n
open CohSig public

FinCohSig : (e : Level) -> Type (ℓ-max (ℓ-suc e) (ℓ-suc ℓ-zero))
FinCohSig = FinSig

finCohSig : {e : Level} -> FinCohSig e -> CohSig e ℓ-zero
name (finCohSig σ) = σ .fst
free (finCohSig σ) = Fin ∘ σ .snd

emptyCohSig : CohSig ℓ-zero ℓ-zero
name emptyCohSig = ⊥.⊥
free emptyCohSig = ⊥.rec

sumCohSig : {e n e' n' : Level} -> CohSig e n -> CohSig e' n' -> CohSig (ℓ-max e e') (ℓ-max n n')
name (sumCohSig σ τ) = (name σ) ⊎ (name τ)
free (sumCohSig {n' = n} σ τ) (inl x) = Lift {j = n} ((free σ) x)
free (sumCohSig {n = n} σ τ) (inr x) = Lift {j = n} ((free τ) x)

-- system of coherences?
-- module _ {f a e n c m : Level} (σ : Sig f a) (τ : EqSig e n) (ϕ : CohSig c m) where
--   scoh : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max f a) e) n) c) m)
--   scoh = (c : ϕ .name) -> {!!}

-- sequences of paths
--
data EqSeq {a} {A : Type a} : A -> A -> Type a where
  nil : ∀ {a} -> EqSeq a a
  cons : ∀ {a b c} -> a ≡ b -> EqSeq b c -> EqSeq a c

evalEqSeq : ∀ {a} {A : Type a} -> {a b : A} -> EqSeq a b -> a ≡ b
evalEqSeq nil = refl
evalEqSeq (cons p e) = p ∙ evalEqSeq e

-- a coherence between top and bottom sequences
-- cohs : EqSeq a b × EqSeq a b
