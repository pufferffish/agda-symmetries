{-# OPTIONS --cubical #-}

module Experiments.ListArray where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (_∷_ to _∷ₗ_)
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum as ⊎
open import Cubical.Induction.WellFounded
import Cubical.Data.Empty as ⊥

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity

open import Cubical.Structures.Set.Mon.Array
open import Cubical.Structures.Set.Mon.List

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

an-array : Array ℕ
an-array = 3 , lemma
  where
  lemma : Fin 3 -> ℕ
  lemma (0 , p) = 5
  lemma (1 , p) = 9
  lemma (2 , p) = 2
  lemma (suc (suc (suc n)) , p) = ⊥.rec (¬-<-zero (<-k+-cancel p))

module MonDef = F.Definition M.MonSig M.MonEqSig M.MonSEq

want : List ℕ
want = 5 ∷ₗ 9 ∷ₗ 2 ∷ₗ []

to-list : structHom < Array ℕ , array-α > < List ℕ , list-α >
to-list = MonDef.Free.ext arrayDef (isOfHLevelList 0 isSetℕ) list-sat [_]

_ : to-list .fst an-array ≡ want
_ = refl

to-list' : structHom < Array ℕ , MonDef.Free.α (arrayDef' {ℓ' = ℓ-zero}) > < List ℕ , list-α >
to-list' = MonDef.Free.ext arrayDef' (isOfHLevelList 0 isSetℕ) list-sat [_]

_ : to-list' .fst an-array ≡ want
_ = refl

to-list'' : Array ℕ -> List ℕ
to-list'' = MonDef.freeIso arrayDef listDef (isSetArray isSetℕ) (isOfHLevelList 0 isSetℕ) .fun

_ : to-list'' an-array ≡ want
_ = refl
