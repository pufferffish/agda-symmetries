{-# OPTIONS --cubical --exact-split -WnoUnsupportedIndexedMatch --safe #-}

module Cubical.Structures.Set.CMon.SList.Sort.Equiv where

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

import Cubical.Structures.Set.Mon.Desc as M
import Cubical.Structures.Set.CMon.Desc as M
import Cubical.Structures.Free as F
open import Cubical.Structures.Sig
open import Cubical.Structures.Str public
open import Cubical.Structures.Tree
open import Cubical.Structures.Eq
open import Cubical.Structures.Arity
open import Cubical.Structures.Set.Mon.List
open import Cubical.Structures.Set.CMon.SList.Base renaming (_∷_ to _∷*_; [] to []*; [_] to [_]*; _++_ to _++*_)
import Cubical.Structures.Set.CMon.SList.Base as S
open import Cubical.Structures.Set.CMon.SList.Length as S
open import Cubical.Structures.Set.CMon.SList.Membership as S
open import Cubical.Structures.Set.CMon.SList.Sort.Base
open import Cubical.Structures.Set.CMon.SList.Sort.Sort
open import Cubical.Structures.Set.CMon.SList.Sort.Order

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

module Sort↔Order {ℓ : Level} {A : Type ℓ} (isSetA : isSet A) where
  open Sort isSetA
  open Sort.Section isSetA
  open Sort→Order isSetA
  open Order→Sort
  open IsToset

  IsDecOrder : (A -> A -> Type ℓ) -> Type _
  IsDecOrder _≤_ = IsToset _≤_ × (∀ x y -> Dec (x ≤ y))

  HasDecOrder : Type _
  HasDecOrder = Σ _ IsDecOrder

  HasSortSectionAndIsDiscrete : Type _
  HasSortSectionAndIsDiscrete = (Σ _ is-sort-section) × (Discrete A)

  order→sort : HasDecOrder -> HasSortSectionAndIsDiscrete
  order→sort (_≤_ , isToset , isDec) =
    (sort _≤_ isToset isDec , subst (λ isSetA' -> Sort.is-sort-section isSetA' (sort _≤_ isToset isDec)) (isPropIsSet _ _) (Order→Sort.sort-is-sort-section _≤_ isToset isDec)) , isDiscreteA _≤_ isToset isDec

  sort→order : HasSortSectionAndIsDiscrete -> HasDecOrder
  sort→order ((s , s-is-section , s-is-sort) , discA) =
    _≤_ s s-is-section , ≤-isToset s s-is-section s-is-sort , dec-≤ s s-is-section discA

  order→sort→order : ∀ x -> sort→order (order→sort x) ≡ x
  order→sort→order (_≤_ , isToset , isDec) =
    Σ≡Prop (λ _≤'_ -> isOfHLevelΣ 1 (isPropIsToset _) (λ p -> isPropΠ2 λ x y -> isPropDec (is-prop-valued p x y))) (sym ≤-≡)
    where
    _≤*_ : A -> A -> Type _
    _≤*_ = sort→order (order→sort (_≤_ , isToset , isDec)) .fst

    ≤*-isToset : IsToset _≤*_
    ≤*-isToset = sort→order (order→sort (_≤_ , isToset , isDec)) .snd .fst

    iso-to : ∀ x y -> x ≤ y -> x ≤* y
    iso-to x y x≤y with isDec x y
    ... | yes p = refl
    ... | no ¬p = ⊥.rec (¬p x≤y)

    iso-from : ∀ x y -> x ≤* y -> x ≤ y
    iso-from x y x≤y with isDec x y
    ... | yes p = p
    ... | no ¬p = ⊥.rec (¬p (subst (_≤ y) (just-inj y x x≤y) (is-refl isToset y)))

    iso-≤ : ∀ x y -> Iso (x ≤ y) (x ≤* y)
    iso-≤ x y = iso (iso-to x y) (iso-from x y) (λ p -> is-prop-valued ≤*-isToset x y _ p) (λ p -> is-prop-valued isToset x y _ p)
    ≤-≡ : _≤_ ≡ _≤*_  
    ≤-≡ = funExt λ x -> funExt λ y -> isoToPath (iso-≤ x y) 

  sort→order→sort : ∀ x -> order→sort (sort→order x) ≡ x
  sort→order→sort ((s , s-is-section , s-is-sort) , discA) =
    Σ≡Prop (λ _ -> isPropDiscrete)
    $ Σ≡Prop isProp-is-sort-section
    $ sym
    $ funExt λ xs -> unique-sort' _≤*_ ≤*-isToset ≤*-dec s xs (s-is-section , ∣_∣₁ ∘ s-is-sort')
    where
    s' : SList A -> List A
    s' = order→sort (sort→order ((s , s-is-section , s-is-sort) , discA)) .fst .fst

    s'-is-sort-section : is-sort-section s'
    s'-is-sort-section = order→sort (sort→order ((s , s-is-section , s-is-sort) , discA)) .fst .snd

    _≤*_ : A -> A -> Type _
    _≤*_ = _≤_ s s-is-section

    ≤*-isToset : IsToset _≤*_
    ≤*-isToset = ≤-isToset s s-is-section s-is-sort

    ≤*-dec : ∀ x y -> Dec (x ≤* y)
    ≤*-dec = dec-≤ s s-is-section discA

    Sorted* : List A -> Type _
    Sorted* = Sorted _≤*_ ≤*-isToset ≤*-dec

    s-is-sort'' : ∀ xs n -> n ≡ L.length (s xs) -> Sorted* (s xs)
    s-is-sort'' xs n p with n | s xs | inspect s xs
    ... | zero  | []     | _ = sorted-nil
    ... | zero  | y ∷ ys | _ = ⊥.rec (znots p)
    ... | suc _ | []     | _ = ⊥.rec (snotz p)
    ... | suc _ | y ∷ [] | _ = sorted-one y
    ... | suc m | y ∷ z ∷ zs | [ q ]ᵢ = induction (s-is-sort'' (list→slist (z ∷ zs)) m (injSuc p ∙ wit))
      where
      wit : suc (L.length zs) ≡ L.length (s (list→slist (z ∷ zs)))
      wit = sym $
        L.length (s (list→slist (z ∷ zs))) ≡⟨ sort-length≡ s s-is-section (list→slist (z ∷ zs)) ⟩
        S.length (list→slist (z ∷ zs)) ≡⟨ sym (sort-length≡-α s s-is-section (z ∷ zs)) ⟩
        L.length (z ∷ zs) ∎

      z∷zs-sorted : s (list→slist (z ∷ zs)) ≡ z ∷ zs
      z∷zs-sorted = sort-unique s s-is-section (z ∷ zs) (s-is-sort .snd y (z ∷ zs) ∣ _ , q ∣₁)

      induction : Sorted* (s (list→slist (z ∷ zs))) -> Sorted* (y ∷ z ∷ zs)  
      induction IH =
        sorted-cons y z zs
          (is-sorted→≤ s s-is-section y z (s-is-sort .fst y z _ ∣ _ , q ∣₁ (L.inr (L.inl refl))))
          (subst Sorted* z∷zs-sorted IH)

    s-is-sort' : ∀ xs -> Sorted* (s xs)
    s-is-sort' xs = s-is-sort'' xs (L.length (s xs)) refl -- helps with termination checking

  sort↔order : Iso HasDecOrder HasSortSectionAndIsDiscrete
  sort↔order = iso order→sort sort→order sort→order→sort order→sort→order
