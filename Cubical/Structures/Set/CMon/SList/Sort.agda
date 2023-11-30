{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.CMon.SList.Sort where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Binary.Order 
open import Cubical.Data.List
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

module Loset→Sort {ℓ : Level} {A : Type ℓ} (_≤_ : A -> A -> Type ℓ) (<-isLo : IsToset _≤_) where

  data AscList : Type ℓ

  head : AscList -> A

  data AscList where
    [_]* : A -> AscList
    cons* : (x : A) -> (xs : AscList) -> x ≤ (head xs) -> AscList

  head [ x ]* = x
  head (cons* x _ _) = x

  AscList→List : AscList -> List A
  AscList→List [ x ]* = x ∷ []
  AscList→List (cons* x xs _) = x ∷ AscList→List xs

  SList→AscList : Iso (SList A) (Maybe AscList)
  SList→AscList = {!   !}

  MaybeAscList→List : Maybe AscList -> List A
  MaybeAscList→List = Maybe.rec [] AscList→List

  list→slist-Hom : structHom < List A , list-α > < SList A , slist-α >
  list→slist-Hom = ListDef.Free.ext listDef trunc (M.cmonSatMon slist-sat) S.[_]

  list→slist : List A -> SList A
  list→slist = list→slist-Hom .fst

  slist→list : SList A -> List A
  slist→list = MaybeAscList→List ∘ SList→AscList .fun

  sort : Σ[ s ∈ (SList A -> List A) ] (∀ x -> list→slist (s x) ≡ x)
  sort = slist→list , {!   !}