{-# OPTIONS --cubical --exact-split --safe #-}

module Cubical.Structures.Set.CMon.SList.Membership where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
import Cubical.Data.List as L
open import Cubical.Functions.Logic as L

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.HITs.FiniteMultiset public renaming (FMSet to SList; comm to swap)

open import Cubical.Structures.Set.CMon.SList.Base as SList

module Membership {ℓ} {A : Type ℓ} (isSetA : isSet A) where
  open Free {A = A} isSetHProp (M.⊔-MonStr-CMonSEq ℓ)
  
  ∈*Prop : A -> SList A -> hProp ℓ 
  ∈*Prop x = (λ y -> (x ≡ y) , isSetA x y) ♯
  
  _∈*_ : A -> SList A -> Type ℓ
  x ∈* xs = ∈*Prop x xs .fst
  
  x∈*xs : ∀ x xs -> x ∈* (x ∷ xs)
  x∈*xs x xs = inl refl

  ∈*-∷ : ∀ x y xs -> x ∈* xs -> x ∈* (y ∷ xs)
  ∈*-∷ x y xs p = inr p
