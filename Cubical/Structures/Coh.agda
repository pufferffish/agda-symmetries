{-# OPTIONS --cubical #-}

module Cubical.Structures.Coh where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Image
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.List as L
open import Cubical.Data.Sigma
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
