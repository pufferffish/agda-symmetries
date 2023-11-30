{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.CMon.SList.Sort where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
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

private
  variable
    ℓ : Level
    A : Type ℓ

module Loset→Sort (_<_ : A -> A -> Type ℓ) (<-isLo : IsLoset _<_) where

  list→slist-Hom : structHom < List A , list-α > < SList A , slist-α >
  list→slist-Hom = ListDef.Free.ext listDef isSetSList (M.cmonSatMon slist-sat) S.[_]

  list→slist : List A -> SList A
  list→slist = list→slist-Hom .fst

  slist→list : SList A -> List A
  slist→list = elimSListSet.f _ []
    (λ x xs -> x ∷ xs)
    {!   !}
    {!   !}

  sort : Σ[ s ∈ (SList A -> List A) ] (∀ x -> list→slist (s x) ≡ x)
  sort = {!   !} , {!   !}