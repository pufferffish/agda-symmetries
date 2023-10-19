{-# OPTIONS --cubical #-}

-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.AFunc where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List as L
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.HITs.SetQuotients as Q

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.Mon.List as LM
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A B : Type ℓ

SymAct : ∀ {A : Type ℓ} -> (n : ℕ) -> (Fin n -> A) -> (Fin n -> A) -> Type ℓ
SymAct n v w = ∃[ σ ∈ (Fin n ≃ Fin n) ] v ≡ w ∘ (σ .fst)

AFunc : Type ℓ -> Type ℓ
AFunc A = Σ[ n ∈ ℕ ] (Fin n -> A) Q./ SymAct n