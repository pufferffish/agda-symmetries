{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Experiments.Fin where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (_∷_ to _∷ₗ_)
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum as ⊎
import Cubical.Data.Empty as ⊥

open import Cubical.Structures.Set.Mon.Array
import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
import Cubical.Structures.Set.Mon.List as LM

open Iso

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Cubical.Reflection.Base
open import Cubical.Tactics.FunctorSolver.Solver
open import Cubical.Tactics.Reflection



postulate
  TODO : ∀ {ℓ} {A : Type ℓ} -> A

arrayIsoToListHom' : ∀ {ℓ} {A : Type ℓ} -> structIsHom < Array A , ArrayDef.Free.α {ℓ' = ℓ} arrayDef' > < List A , LM.list-α > (arrayIsoToList .fun)
arrayIsoToListHom' M.`e i = refl
arrayIsoToListHom' {A = A} M.`⊕ index with index fzero | inspect index fzero
... | zero , f | [ p ]ᵢ = congS (uncurry tabulate) (Array≡ (sym lemma-α) TODO)
  where
  lemma-α : _
  lemma-α = {!   !}
... | suc n , f | p = TODO