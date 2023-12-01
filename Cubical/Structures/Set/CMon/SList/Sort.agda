{-# OPTIONS --cubical --exact-split #-}

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

module Sort→Toset (isSetA : isSet A) (sortHom : structHom < SList A , slist-α > < List A , list-α >) (sort≡ : ∀ xs -> list→slist (sortHom .fst xs) ≡ xs) where
  sort : SList A -> List A
  sort = sortHom .fst

  private
    list→slist-η : ∀ xs -> (x : A) -> list→slist xs ≡ [ x ]* -> xs ≡ [ x ]
    list→slist-η [] x p = ⊥.rec (znots (congS S.length p))
    list→slist-η (x ∷ []) y p = congS [_] ([-]-inj {ϕ = isSetA} p)
    list→slist-η (x ∷ y ∷ xs) z p = ⊥.rec (snotz (injSuc (congS S.length p)))

    sort-η : ∀ x -> sort [ x ]* ≡ [ x ]
    sort-η x = list→slist-η (sort [ x ]*) x (sort≡ [ x ]*)

  private -- test
    lemma-test-α : ∀ x y -> head-maybe (sort (x ∷* y ∷* []*)) ≡ just x
    lemma-test-α x y =
      head-maybe (sortHom .fst (x ∷* [ y ]*)) ≡⟨ congS head-maybe $ sym (sortHom .snd M.`⊕ ⟪ [ x ]* ⨾ [ y ]* ⟫) ⟩
      head-maybe (sort [ x ]* ++ sort [ y ]*) ≡⟨ congS (λ w -> head-maybe (w ++ sort [ y ]*)) (sort-η x) ⟩
      head-maybe (x ∷ sort [ y ]*) ≡⟨⟩
      just x ∎
    lemma-test-β : ∀ x y -> head-maybe (sort (x ∷* y ∷* []*)) ≡ just y
    lemma-test-β x y =
      head-maybe (sort (x ∷* y ∷* []*)) ≡⟨ congS (λ z -> head-maybe (sort z)) (swap x y []*) ⟩
      head-maybe (sort (y ∷* [ x ]*)) ≡⟨ lemma-test-α y x ⟩
      just y ∎
    lemma-test : ∀ (x y : A) -> x ≡ y -- wtf?
    lemma-test x y = just-inj x y (sym (lemma-test-α x y) ∙ (lemma-test-β x y))

  _≤_ : A -> A -> Type _
  x ≤ y = head-maybe (sort (x ∷* y ∷* []*)) ≡ just x

  ≤-refl : ∀ x -> x ≤ x
  ≤-refl x =
    head-maybe (sort ([ x ]* ++* [ x ]*)) ≡⟨ congS head-maybe $ sym (sortHom .snd M.`⊕ ⟪ [ x ]* ⨾ [ x ]* ⟫) ⟩
    head-maybe (sort [ x ]* ++ sort [ x ]*) ≡⟨ congS (λ w -> head-maybe (w ++ sort [ x ]*)) (sort-η x) ⟩
    head-maybe (x ∷ sort [ x ]*) ≡⟨⟩
    just x ∎

  ≤-trans : ∀ x y z -> x ≤ y -> y ≤ z -> x ≤ z
  ≤-trans x y z p q =
    head-maybe (sortHom .fst (x ∷* [ z ]*)) ≡⟨ congS head-maybe $ sym (sortHom .snd M.`⊕ ⟪ [ x ]* ⨾ [ z ]* ⟫) ⟩
    head-maybe (sort [ x ]* ++ sort [ z ]*) ≡⟨ congS (λ w -> head-maybe (w ++ sort [ z ]*)) (sort-η x) ⟩
    head-maybe (x ∷ sort [ z ]*) ≡⟨⟩
    just x ∎

  ≤-isToset : IsToset _≤_
  IsToset.is-set ≤-isToset = isSetA
  IsToset.is-prop-valued ≤-isToset x y = isOfHLevelMaybe 0 isSetA _ _
  IsToset.is-refl ≤-isToset = ≤-refl
  IsToset.is-trans ≤-isToset = ≤-trans
  IsToset.is-antisym ≤-isToset = {!   !}
  IsToset.is-strongly-connected ≤-isToset = {!   !} 