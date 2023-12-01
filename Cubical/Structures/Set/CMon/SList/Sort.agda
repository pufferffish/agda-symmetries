{-# OPTIONS --cubical --exact-split #-}

module Cubical.Structures.Set.CMon.SList.Sort where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_)
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
open import Cubical.Structures.Set.CMon.SList.Base renaming (_∷_ to _∷*_; [] to []*; [_] to [_]*; _++_ to _++*_)
import Cubical.Structures.Set.CMon.SList.Base as S
open import Cubical.Structures.Set.CMon.SList.Length as S

open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

list→slist-Hom : structHom < List A , list-α > < SList A , slist-α >
list→slist-Hom = ListDef.Free.ext listDef trunc (M.cmonSatMon slist-sat) S.[_]

list→slist : List A -> SList A
list→slist = list→slist-Hom .fst

head-maybe : List A -> Maybe A
head-maybe [] = nothing
head-maybe (x ∷ xs) = just x

module Sort→Toset (discreteA : Discrete A) (sort : SList A -> List A) (sort≡ : ∀ xs -> list→slist (sort xs) ≡ xs) where

  isSetA : isSet A
  isSetA = Discrete→isSet discreteA

  private
    list→slist-η : ∀ xs -> (x : A) -> list→slist xs ≡ [ x ]* -> xs ≡ [ x ]
    list→slist-η [] x p = ⊥.rec (znots (congS S.length p))
    list→slist-η (x ∷ []) y p = congS [_] ([-]-inj {ϕ = isSetA} p)
    list→slist-η (x ∷ y ∷ xs) z p = ⊥.rec (snotz (injSuc (congS S.length p)))

    sort-length≡-α : ∀ (xs : List A) -> L.length xs ≡ S.length (list→slist xs)
    sort-length≡-α [] = refl
    sort-length≡-α (x ∷ xs) = congS suc (sort-length≡-α xs)

    sort-length≡ : ∀ xs -> L.length (sort xs) ≡ S.length xs
    sort-length≡ xs = sort-length≡-α (sort xs) ∙ congS S.length (sort≡ xs)

    length-0 : ∀ (xs : List A) -> L.length xs ≡ 0 -> xs ≡ []
    length-0 [] p = refl
    length-0 (x ∷ xs) p = ⊥.rec (snotz p)

    sort-[] : sort []* ≡ []
    sort-[] = length-0 (sort []*) (sort-length≡ []*)

    sort-[-] : ∀ x -> sort [ x ]* ≡ [ x ]
    sort-[-] x = list→slist-η (sort [ x ]*) x (sort≡ [ x ]*)

  least : SList A -> Maybe A
  least xs = head-maybe (sort xs)

  _∈*_ : A -> SList A -> Type _
  x ∈* xs = 0 < (FMScount discreteA x xs)

  private
    ∈*-∷-α : ∀ x y xs -> x ≡ y -> x ∈* xs -> x ∈* (y ∷* xs)
    ∈*-∷-α x y xs p q = <-trans q lemma-β
      where
      lemma-α : FMScount discreteA x (y ∷* xs) ≡ suc (FMScount discreteA x xs)
      lemma-α = FMScount-≡-lemma discreteA xs p
      lemma-β : FMScount discreteA x xs < FMScount discreteA x (y ∷* xs)
      lemma-β = subst (FMScount discreteA x xs <_) (sym lemma-α) ≤-refl
    ∈*-∷-β : ∀ x y xs -> ¬(x ≡ y) -> x ∈* xs -> x ∈* (y ∷* xs)
    ∈*-∷-β x y xs p q = subst (0 <_) (sym lemma) q
      where
      lemma : FMScount discreteA x (y ∷* xs) ≡ FMScount discreteA x xs
      lemma = FMScount-≢-lemma discreteA xs p
    ∈*-∷ : ∀ x y xs -> x ∈* xs -> x ∈* (y ∷* xs)
    ∈*-∷ x y xs p = decRec
      (λ q -> ∈*-∷-α x y xs q p)
      (λ q -> ∈*-∷-β x y xs q p)
      (discreteA x y)

  ∈*-++ : ∀ x xs ys -> x ∈* ys -> x ∈* (xs ++* ys)
  ∈*-++ x xs ys p =
    ElimProp.f {B = λ zs -> x ∈* (zs ++* ys)} isProp≤ p
      (λ z {zs} q -> ∈*-∷ x z (zs ++* ys) q)
      xs

  _≤_ : A -> A -> Type _
  x ≤ y = ∃[ xs ∈ SList A ] (least xs ≡ just x) × (y ∈* xs)

  refl-≤ : ∀ x -> x ≤ x
  refl-≤ x = ∣ (x ∷* []*) , congS head-maybe (sort-[-] x) , x∈xs ∣₁
    where
    x∈xs : x ∈* [ x ]*
    x∈xs with discreteA x x
    ... | yes p = 0 , refl
    ... | no ¬p = ⊥.rec (¬p refl)

  trans-≤ : ∀ x y z -> x ≤ y -> y ≤ z -> x ≤ z
  trans-≤ x y z = P.rec (isPropΠ (λ _ -> squash₁)) λ (xs , p , q) ->
    P.rec squash₁ λ (ys , r , s) ->
      ∣ xs ++* ys , {!   !} , ∈*-++ z xs ys s ∣₁

--
--  _≤_ : A -> A -> Type _
--  x ≤ y = least (x ∷* y ∷* []*) ≡ just x
--
--  ≤-refl : ∀ x -> x ≤ x
--  ≤-refl x = ⊎.rec (λ p -> p) (λ p -> p) (least-choice x x)
--
--  ≤-trans : ∀ x y z -> x ≤ y -> y ≤ z -> x ≤ z
--  ≤-trans x y z p q = {!   !}
--
--  ≤-antisym : ∀ x y -> x ≤ y -> y ≤ x -> x ≡ y
--  ≤-antisym x y p q = ⊎.rec
--    (λ xy -> just-inj x y $
--      just x ≡⟨ sym xy ⟩
--      least (x ∷* y ∷* []*) ≡⟨ congS least (swap x y []*) ⟩
--      least (y ∷* x ∷* []*) ≡⟨ q ⟩
--      just y
--    ∎)
--    (λ yx -> just-inj x y $
--      just x ≡⟨ sym p ⟩
--      least (x ∷* [ y ]*) ≡⟨ yx ⟩
--      just y
--    ∎)
--    (least-choice x y)
--
--  ≤-dec : ∀ x y -> (x ≤ y) ⊎ (y ≤ x)
--  ≤-dec x y = ⊎.rec
--    (λ p -> inl p)
--    (λ p -> inr $
--      least (y ∷* [ x ]*) ≡⟨ congS least (swap y x []*) ⟩
--      least (x ∷* [ y ]*) ≡⟨ p ⟩
--      just y
--    ∎)
--    (least-choice x y)
--
--  ≤-isToset : IsToset _≤_
--  IsToset.is-set ≤-isToset = isSetA
--  IsToset.is-prop-valued ≤-isToset x y = isOfHLevelMaybe 0 isSetA _ _
--  IsToset.is-refl ≤-isToset = ≤-refl
--  IsToset.is-trans ≤-isToset = ≤-trans
--  IsToset.is-antisym ≤-isToset = ≤-antisym
--  IsToset.is-strongly-connected ≤-isToset x y = ∣ ≤-dec x y ∣₁ 