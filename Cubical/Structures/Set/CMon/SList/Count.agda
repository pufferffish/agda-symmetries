{-# OPTIONS --cubical --exact-split --safe #-}

module Cubical.Structures.Set.CMon.SList.Count where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
import Cubical.Data.List as L
open import Cubical.Functions.Logic as L
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary

open import Cubical.Structures.Prelude
import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.Structures.Set.Mon.List

open import Cubical.Structures.Set.CMon.SList.Base as SList

private
  variable
    ℓ : Level
    A : Type ℓ

module Count* {ℓ} {A : Type ℓ} (discA : Discrete A) where
  open SList.Free {A = A} isSetℕ M.ℕ-CMonStr-MonSEq

  よ : A -> A -> ℕ
  よ x = λ y -> decElim (λ x≡y -> 1) (λ x≠y -> 0) (discA x y)

  よ-β : ∀ x -> よ x x ≡ 1
  よ-β x  with discA x x
  ... | yes p = refl
  ... | no ¬p = ⊥.rec (¬p refl)

  ∈*ℕ : A -> SList A -> ℕ
  ∈*ℕ x = (よ x) ♯

  _∈*_ : A -> SList A -> ℕ
  _∈*_ x = (よ x) ♯

  x∈*[] : ∀ x -> x ∈* [] ≡ 0
  x∈*[] x = refl

  x∈*x∷xs : ∀ x xs -> x ∈* (x ∷ xs) ≡ 1 + x ∈* xs
  x∈*x∷xs x xs = ♯-∷ (よ x) x xs ∙ congS (_+ (x ∈* xs)) (よ-β x)
