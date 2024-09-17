{-# OPTIONS --cubical --exact-split #-}

module Cubical.Structures.Set.CMon.SList.Head where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
import Cubical.Data.List as L
open import Cubical.Functions.Logic as L
open import Cubical.HITs.PropositionalTruncation as P
open import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary as R
open import Cubical.Relation.Binary.Order

open import Cubical.Structures.Prelude
import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.Structures.Set.Mon.List hiding (module Head)

open import Cubical.Structures.Set.CMon.SList.Base as SList

private
  variable
    ℓ : Level
    A : Type ℓ

module Head {ℓ} {A : Type ℓ} (isSetA : isSet A) (_≤_ : A -> A -> Type ℓ) (tosetA : IsToset _≤_) where

  open Toset.Toset-⋀ isSetA _≤_ tosetA

  _⊕_ : Maybe A -> Maybe A -> Maybe A
  nothing ⊕ b = b
  just a ⊕ nothing = just a
  just a ⊕ just b = just (a ⋀ b)

  ⊕-unitl : ∀ x -> nothing ⊕ x ≡ x
  ⊕-unitl x = refl

  ⊕-unitr : ∀ x -> x ⊕ nothing ≡ x
  ⊕-unitr nothing = refl
  ⊕-unitr (just x) = refl

  ⊕-assocr : ∀ x y z -> (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
  ⊕-assocr nothing y z = refl
  ⊕-assocr (just x) nothing z = refl
  ⊕-assocr (just x) (just y) nothing = refl
  ⊕-assocr (just x) (just y) (just z) = congS just (⋀-assocr x y z)

  ⊕-comm : ∀ x y -> x ⊕ y ≡ y ⊕ x
  ⊕-comm nothing y = sym (⊕-unitr y)
  ⊕-comm (just x) nothing = refl
  ⊕-comm (just x) (just y) = congS just (⋀-comm x y)

  Maybe-MonStr : M.MonStruct
  car Maybe-MonStr = Maybe A
  alg Maybe-MonStr (M.`e , _) = nothing
  alg Maybe-MonStr (M.`⊕ , i) = i fzero ⊕ i fone

  Maybe-MonStr-MonSEq : Maybe-MonStr ⊨ M.MonSEq
  Maybe-MonStr-MonSEq M.`unitl ρ = ⊕-unitl (ρ fzero)
  Maybe-MonStr-MonSEq M.`unitr ρ = ⊕-unitr (ρ fzero)
  Maybe-MonStr-MonSEq M.`assocr ρ = ⊕-assocr (ρ fzero) (ρ fone) (ρ ftwo)

  Maybe-MonStr-CMonSEq : Maybe-MonStr ⊨ M.CMonSEq
  Maybe-MonStr-CMonSEq (M.`mon eqn) ρ = Maybe-MonStr-MonSEq eqn ρ
  Maybe-MonStr-CMonSEq M.`comm ρ = ⊕-comm (ρ fzero) (ρ fone)

  open SList.Free {A = A} (isOfHLevelMaybe 0 isSetA) Maybe-MonStr-CMonSEq

  head : SList A -> Maybe A
  head = just ♯

  head-[] : head [] ≡ nothing
  head-[] = refl

  head-[x] : ∀ x -> head [ x ] ≡ just x
  head-[x] _ = refl

  head-[x,y] : ∀ x y -> head (x ∷ y ∷ []) ≡ just (x ⋀ y)
  head-[x,y] _ _ = refl
