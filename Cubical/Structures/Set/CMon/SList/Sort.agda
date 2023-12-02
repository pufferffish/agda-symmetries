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

module Sort→Order (discreteA : Discrete A) (sort : SList A -> List A) (sort≡ : ∀ xs -> list→slist (sort xs) ≡ xs) where

  private
    module 𝔖 = M.CMonSEq < SList A , slist-α > slist-sat

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
    
    -- ElimProp.f (isPropΠ λ _ -> isOfHLevelMaybe 0 isSetA _ (just x)) (idfun _)

  ∈*-++ : ∀ x xs ys -> x ∈* ys -> x ∈* (xs ++* ys)
  ∈*-++ x xs ys p =
    ElimProp.f {B = λ zs -> x ∈* (zs ++* ys)} isProp≤ p
      (λ z {zs} q -> ∈*-∷ x z (zs ++* ys) q)
      xs

  x∈[x] : ∀ x -> x ∈* [ x ]*
  x∈[x] x with discreteA x x
  ... | yes p = 0 , refl
  ... | no ¬p = ⊥.rec (¬p refl)

  list→slist-∈* : ∀ x xs -> x ∈* list→slist (x ∷ xs)
  list→slist-∈* x xs = subst (x ∈*_) lemma x∈xs++x
    where
    x∈xs++x : x ∈* (list→slist xs ++* [ x ]*)
    x∈xs++x = ∈*-++ x (list→slist xs) [ x ]* (x∈[x] x)
    lemma : list→slist xs ++* [ x ]* ≡ list→slist (x ∷ xs)
    lemma = sym (𝔖.comm [ x ]* (list→slist xs))

  _≤_ : A -> A -> Type _
  x ≤ y = ∃[ xs ∈ SList A ] (least xs ≡ just x) × (y ∈* xs)

  least-subset : ∀ x y xs -> least xs ≡ just x -> y ∈* xs -> x ≤ y
  least-subset x y xs p q = ∣ xs , p , q ∣₁

  remove1-in : ∀ x xs -> x ∈* xs -> x ∷* remove1 discreteA x xs ≡ xs
  remove1-in = {!   !}

  least-in : ∀ x xs -> least xs ≡ just x -> x ∈* xs
  least-in x xs p with sort xs | inspect sort xs
  ... | []     | _      = ⊥.rec (¬nothing≡just p)
  ... | y ∷ ys | [ q ]ᵢ = subst (_∈* xs) (just-inj y x p) y∈xs
    where
    y∷ys≡xs : list→slist (y ∷ ys) ≡ xs
    y∷ys≡xs = congS list→slist (sym q) ∙ sort≡ xs
    y∈xs : y ∈* xs
    y∈xs = subst (y ∈*_) y∷ys≡xs (list→slist-∈* y ys)

  least-choice : ∀ x y -> (least (x ∷* [ y ]*) ≡ just x) ⊎ (least (x ∷* [ y ]*) ≡ just y)
  least-choice x y with (discreteMaybe discreteA) (least (x ∷* [ y ]*)) (just x)
  ... | yes p = inl p
  ... | no ¬p with (discreteMaybe discreteA) (least (x ∷* [ y ]*)) (just y)
  ... | yes q = inr q
  ... | no ¬q = {!   !}

  least-dec : ∀ x y -> (x ≤ y) ⊎ (¬(x ≤ y))
  least-dec x y = {!   !}

  least-order : ∀ x y -> x ≤ y -> least (x ∷* y ∷* []*) ≡ just x
  least-order x y = P.rec (isOfHLevelMaybe 0 isSetA _ (just x)) λ (xs , p , q) ->
    {!   !}

  refl-≤ : ∀ x -> x ≤ x
  refl-≤ x = ∣ (x ∷* []*) , congS head-maybe (sort-[-] x) , x∈[x] x ∣₁

  trans-≤ : ∀ x y z -> x ≤ y -> y ≤ z -> x ≤ z
  trans-≤ x y z = P.rec (isPropΠ (λ _ -> squash₁)) λ (xs , p , q) ->
    P.rec squash₁ λ (ys , r , s) ->
      ∣ xs ++* ys , {!   !} , ∈*-++ z xs ys s ∣₁

  antisym-≤ : ∀ x y -> x ≤ y -> y ≤ x -> x ≡ y  
  antisym-≤ x y p q = just-inj x y $
    just x ≡⟨ sym (least-order x y p) ⟩
    least (x ∷* [ y ]*) ≡⟨ congS least (swap x y []*) ⟩
    least (y ∷* [ x ]*) ≡⟨ least-order y x q ⟩
    just y ∎

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