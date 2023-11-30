{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.CMon.SList.Sort where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order 
open import Cubical.Relation.Nullary
open import Cubical.Data.List
open import Cubical.HITs.PropositionalTruncation as P
import Cubical.Data.List as L

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.Structures.Set.Mon.List
open import Cubical.Structures.Set.CMon.SList.Base renaming (_∷_ to _∷*_; [] to []*)
import Cubical.Structures.Set.CMon.SList.Base as S

open Iso

module Loset→Sort {ℓ : Level} {A : Type ℓ}
                  (_≤_ : A -> A -> Type ℓ) (≤-isTo : IsToset _≤_) 
                  (_≤?_ : (m n : A) -> (m ≤ n) ⊎ (¬(m ≤ n))) where

  open IsToset ≤-isTo

  unneg : {m n : A} -> ¬(m ≤ n) -> n ≤ m
  unneg {m} {n} p with n ≤? m
  ... | inl q = q
  ... | inr q = P.rec (is-prop-valued n m) (⊎.rec (⊥.rec ∘ p) (⊥.rec ∘ q)) (is-strongly-connected m n)

  data AscList : Type ℓ

  headOr : A -> AscList -> A

  data AscList where
    []* : AscList
    cons* : (x : A) -> (xs : AscList) -> x ≤ (headOr x xs) -> AscList

  headOr x []* = x
  headOr _ (cons* x xs p) = x

  AscList→List : AscList -> List A
  AscList→List []* = []
  AscList→List (cons* x xs p) = x ∷ AscList→List xs

  insert : A -> AscList -> AscList
  insert≤ : (x y : A) (ys : AscList) -> y ≤ x -> y ≤ headOr y ys -> y ≤ headOr y (insert x ys)
  insert x []* = cons* x []* (is-refl x)
  insert x (cons* y ys p) with x ≤? y
  ... | inl q = cons* x (cons* y ys p) q
  ... | inr q = cons* y (insert x ys) (insert≤ x y ys (unneg q) p)
  insert≤ x y []* p q = p
  insert≤ x y (cons* z ys r) p q with x ≤? z
  ... | inl s = p
  ... | inr s = q

  -- _++*_ : AscList -> AscList -> AscList
  -- []* ++* ys = ys
  -- cons* x xs p ++* ys = cons* x (xs ++* ys) {!   !}

  list→slist-Hom : structHom < List A , list-α > < SList A , slist-α >
  list→slist-Hom = ListDef.Free.ext listDef trunc (M.cmonSatMon slist-sat) S.[_]

  list→slist : List A -> SList A
  list→slist = list→slist-Hom .fst

  NESList→AscList : A -> SList A -> AscList
  NESList→AscList x =
    Elim.f
      (cons* x []* (is-refl x))
      (λ x ys -> insert x ys)
      {!   !}
      {!   !}

  sort : Σ[ s ∈ (SList A -> List A) ] (∀ x -> list→slist (s x) ≡ x)
  sort = {!   !} , {!   !}