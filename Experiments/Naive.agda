{-# OPTIONS --cubical --exact-split -WnoUnsupportedIndexedMatch #-}

module Experiments.Naive where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels
open import Cubical.Data.List
open import Cubical.HITs.PropositionalTruncation as P
import Cubical.Data.List as L
open import Cubical.Functions.Logic as L hiding (¬_; ⊥)
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
open import Cubical.Structures.Set.Mon.List as L
open import Cubical.Structures.Set.CMon.SList.Base renaming (_∷_ to _∷*_; [] to []*; [_] to [_]*; _++_ to _++*_)
import Cubical.Structures.Set.CMon.SList.Base as S
open import Cubical.Structures.Set.CMon.SList.Length as S
open import Cubical.Structures.Set.CMon.SList.Membership as S

open Iso
open Toset

private
  variable
    ℓ : Level
    A : Type ℓ

module Naive {ℓ} {A : Type ℓ} (isSetA : isSet A) (_≤_ : A -> A -> Type ℓ) (tosetA : IsToset _≤_) where

  open IsToset
  open Toset-⋀ isSetA _≤_ tosetA
  open Toset-⋁ isSetA _≤_ tosetA

  i : A -> A -> List A
  i a b = (a ⋀ b) ∷ (a ⋁ b) ∷ []

  i-comm : ∀ a b -> i a b ≡ i b a
  i-comm a b j = ⋀-comm a b j ∷ ⋁-comm a b j ∷ []

  isSetListA : isSet (List A)
  isSetListA = isOfHLevelList 0 isSetA

  module FreeList = L.Free {A = A} isSetListA list-sat

  f : A -> List A -> List A
  f a = i a FreeList.♯

private module Test where

  ≤ℕ-isToset : IsToset _≤ℕ_
  ≤ℕ-isToset = istoset isSetℕ
    (λ _ _ -> isProp≤)
    (λ _ -> ≤-refl)
    (λ _ _ _ -> ≤-trans)
    (λ _ _ -> ≤-antisym)
    lemma
    where
    <→≤ : ∀ {n m} -> n <ℕ m -> n ≤ℕ m
    <→≤ (k , p) = suc k , sym (+-suc k _) ∙ p
    lemma : BinaryRelation.isStronglyConnected _≤ℕ_
    lemma x y = ∣ ⊎.rec ⊎.inl (_⊎_.inr ∘ <→≤) (splitℕ-≤ x y) ∣₁

  open Naive isSetℕ _≤ℕ_ ≤ℕ-isToset

  _ : i 3 2 ≡ 2 ∷ 3 ∷ []
  _ = refl

  _ : f 2 [] ≡ []
  _ = refl

  _ : f 2 [ 3 ] ≡ 2 ∷ 3 ∷ []
  _ = refl

  _ : f 3 [ 2 ] ≡ 2 ∷ 3 ∷ []
  _ = refl

  _ : f 2 (1 ∷ 3 ∷ []) ≡ 1 ∷ 2 ∷ 2 ∷ 3 ∷ []
  _ = refl
