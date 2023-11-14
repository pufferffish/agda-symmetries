{-# OPTIONS --cubical --exact-split #-}

-- Definition taken from https://drops.dagstuhl.de/opus/volltexte/2023/18395/pdf/LIPIcs-ITP-2023-20.pdf
module Cubical.Structures.Set.CMon.Bag.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List renaming (_∷_ to _∷ₗ_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Set.Mon.Array as A
open import Cubical.Structures.Set.Mon.List as L
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity hiding (_/_)
open import Cubical.HITs.SetQuotients as Q
open import Cubical.Structures.Set.CMon.QFreeMon
open import Cubical.Relation.Nullary

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

_≈_ : ∀ {A : Type ℓ} -> Array A -> Array A -> Type ℓ
_≈_ (n , v) (m , w) = Σ[ σ ∈ Iso (Fin n) (Fin m) ] v ≡ w ∘ σ .fun

Bag : Type ℓ -> Type ℓ
Bag A = Array A Q./ _≈_
