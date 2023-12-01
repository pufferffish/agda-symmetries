{-# OPTIONS --cubical --safe --exact-split #-}

module Cubical.Structures.Set.CMon.SList.Hom where

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

module UniqueHom (hom : structHom < SList A , slist-α > < List A , list-α >) where
  f : SList A -> List A
  f = hom .fst

  lemma-α : ∀ x y -> f (x ∷* y ∷* []*) ≡ f [ x ]* ++ f [ y ]*
  lemma-α x y = sym (hom .snd M.`⊕ ⟪ [ x ]* ⨾ [ y ]* ⟫)

  lemma-β : ∀ x y -> f (x ∷* y ∷* []*) ≡ f [ y ]* ++ f [ x ]*
  lemma-β x y = congS f (swap x y []*) ∙ (lemma-α y x)

  lemma-γ : ∀ x y -> f [ x ]* ++ f [ y ]* ≡ f [ y ]* ++ f [ x ]*
  lemma-γ x y = sym (lemma-α x y) ∙ (lemma-β x y)

  -- Prove f must be trivial?