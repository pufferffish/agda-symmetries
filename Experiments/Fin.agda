{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Experiments.Fin where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
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

private
  variable
    ℓ : Level
    A : Type ℓ


infixr 5 _∷_

data FMSet (A : Type ℓ) : Type ℓ where
  []    : FMSet A
  _∷_   : (x : A) → (xs : FMSet A) → FMSet A
  comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (FMSet A)

_++_ : ∀ (xs ys : FMSet A) → FMSet A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
comm x y xs i ++ ys = comm x y (xs ++ ys) i
trunc xs zs p q i j ++ ys = {! trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) !}
  -- trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j
